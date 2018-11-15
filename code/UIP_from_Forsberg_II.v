(* Checked with Coq 8.8.0. *)

(* Need to fix lemma numbers *)

Set Universe Polymorphism.

From Coq Require ssreflect.
Import ssreflect.SsrSyntax.
(* Use the pattern conditional: `if 3 is S n then n else 10`*)

(* Define the type of dependent pairs *)
Record prod (A : Type) (B : A -> Type) := pair { p1 : A ; p2 : B p1 }.
Arguments pair {A B}.
Arguments p1 {A B}.
Arguments p2 {A B}.

(* Some properties of types: *)

(* homotopy proposition *)
Definition unique_inhabitants@{i} (X : Type@{i}) : Type@{i}
  := forall (x y : X), x = y.
(* homotopy set; equivalently forall (x y : X), unique_inhabitants (x = y). *)
Definition UIP_holds@{i} (X : Type@{i}) : Type@{i}
  := forall (x y : X) (p q : x = y), p = q.

Section UIP_from_Forsberg_II.
Universe i.
Context (X : Type@{i}).

(* Forsberg's translation of
A : Set
B : A -> Set
eta : X -> A
join : forall a, B a -> A
inj : forall a, B a

c.f. Forsberg's thesis section 5.3, example 5.32
*)

Inductive preA : Type@{i} :=
  | pre_eta : X -> preA
  | pre_join : preA -> preB -> preA
with preB : Type@{i} :=
  | pre_inj : preA -> preB
.
Inductive goodA : preA -> Type@{i} :=
  | good_eta : forall x, goodA (pre_eta x)
  | good_join : forall a, goodA a -> forall b, goodB a b -> goodA (pre_join a b)
with goodB : preA -> preB -> Type@{i} :=
  | good_inj : forall a, goodA a -> goodB a (pre_inj a)
.

(* Definition of the inductive-inductive object *)
Definition A : Type@{i}
  := prod preA goodA.
(* note that B is only dependent on (p1 a). *)
Definition B (a : A) : Type@{i}
  := prod preB (goodB (p1 a)).
Definition eta (x : X) : A
  := pair (pre_eta x) (good_eta x).
Definition join (a : A) (b : B a) : A
  := pair (pre_join (p1 a) (p1 b)) (good_join (p1 a) (p2 a) (p1 b) (p2 b)).
Definition inj (a : A) : B a
  := pair (pre_inj (p1 a)) (good_inj (p1 a) (p2 a)).

Record motives@{j} : Type@{max(i, j+1)} := {
  PA : A -> Type@{j};
  PB : forall a, B a -> Type@{j};
  Peta : forall x, PA (eta x);
  Pjoin : forall a, PA a -> forall b, PB a b -> PA (join a b);
  Pinj : forall a, PA a -> PB a (inj a);
}.

Record eliminated@{j} {M : motives@{j}} : Type@{max(i, j)} := {
  EA : forall a, M.(PA) a;
  EB : forall a b, M.(PB) a b;
  Eeta : forall x, EA (eta x) = M.(Peta) x;
  Ejoin : forall a b, EA (join a b) = M.(Pjoin) a (EA a) b (EB a b);
  Einj : forall a, EB a (inj a) = M.(Pinj) a (EA a);
}.
Arguments eliminated M : clear implicits.

Definition simple_eliminators : Type@{i+1}
  := (forall m : motives@{i}, eliminated m).

Section unique_goodness_only_if_UIP.
(* Section 4.1 *)

Notation "( x == y )" := (pre_join (pre_eta x) (pre_inj (pre_eta y))).

Section XtoAtoX_retract.
Context (x : X).
(* Retraction from (x = y) to goodA (x == y) *)
(* Lemma 4.1 *)
Definition XtoA y : x = y -> goodA (x == y)
  := fun 'eq_refl => good_join _ (good_eta x) _ (good_inj _ (good_eta x)).
Definition AtoX y : goodA (x == y) -> x = y
  := fun good_a =>
     if good_a is good_join _ _ _ good_b
       in goodA a return if a is (x == y) then x = y else unit
     then if good_b is good_inj (pre_eta x) _ then eq_refl x else tt else tt.
Definition XtoAtoX_id y : forall (e : x = y), AtoX y (XtoA y e) = e
  := fun e => match e with eq_refl => eq_refl end.
End XtoAtoX_retract.

Context (A_unique : forall t, unique_inhabitants (goodA t)).
Let t x : A := join (eta x) (inj (eta x)).
Definition UIP_refl : forall x (p : x = x), eq_refl = p
  := fun x p => eq_trans
     (f_equal (AtoX x x) (A_unique (x == x) (t x).(p2) (XtoA x x p)))
     (XtoAtoX_id x x p).

(* Lemma 4.2 *)
Definition UIP : forall (x y : X) (p q : x = y), p = q
  := fun x y p => match p with eq_refl => UIP_refl x end.
End unique_goodness_only_if_UIP.

Section simple_eliminators_only_if_unique_goodness.
(* Section 4.2 *)

(* Retraction from goodA (p1 t) to B t (for all t : A) *)
(* Lemma 4.3 *)
Definition AtoB t : goodA (p1 t) -> B t
  := fun good_a => pair (pre_inj (p1 t)) (good_inj (p1 t) good_a).
Definition BtoA t : B t -> goodA (p1 t)
  := fun '(pair _ good_b) =>
     let '(good_inj _ good_a) := good_b
     in good_a.
(* (AtoB t) and (BtoA t) are inverses up to definitional equality *)
Definition AtoBtoA_id t : forall a, BtoA t (AtoB t a) = a
  := fun a => eq_refl.

Context (elim : simple_eliminators).

Definition match_on_B
  (P : forall a, B a -> Type@{i})
  (step_inj : forall a, P a (inj a))
  : forall a b, P a b
  := (elim {|
        PB := P; Pinj a _ := step_inj a;
        PA _ := unit; Peta _ := tt; Pjoin _ _ _ _ := tt;
      |}).(EB).

(* Lemma 4.4 *)
Definition B_contr : forall a (b : B a), inj a = b
  := match_on_B (fun a b => inj a = b) (fun a => eq_refl (inj a)).

(* Lemma 4.5 *)
(* Combining with B_contr, we can show that goodA t has unique inhabitents *)
Definition A_unique t : forall a1 a2 : goodA t, a1 = a2
  := fun a1 a2 => let tt := pair t a1 in
     f_equal (BtoA tt) (B_contr tt (AtoB tt a2)).

End simple_eliminators_only_if_unique_goodness.

End UIP_from_Forsberg_II.

(* Theorem 4.6 *)
Definition UIP_from_Forsberg_II@{i} (X : Type@{i})
  : simple_eliminators X -> UIP_holds X
  := fun elim => UIP@{i} X (A_unique X elim).
