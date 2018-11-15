{-# OPTIONS --cubical --safe #-}
module Prelude where

-- Many definitions are taken from the HoTT book <https://homotopytypetheory.org/book>
-- and <https://github.com/Saizan/cubical-demo>

open import Agda.Primitive public
open import Agda.Builtin.Nat public
  using (zero; suc)
  renaming (Nat to ℕ)

open import Primitives public

record ⊤ {ℓ} : Set ℓ where
  constructor tt
  eta-equality
pattern ★ = tt

infixr 4 _,_
record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

infix 2 Σ-syntax
Σ-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

onSnd : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : A → Set ℓ₂} {C : A → Set ℓ₃} → (∀ a → B a → C a) → Σ A B → Σ A C
onSnd f (a , b) = a , f a b

_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

module _ {ℓ} {A : Set ℓ} where
  refl : {x : A} → x ≡ x
  refl {x = x} = λ _ → x

  sym : {x y : A} → x ≡ y → y ≡ x
  sym p = λ i → p (~ i)

  trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans {x = x} p q i = primComp (λ _ → A) _ (λ { j (i = i0) → x ; j (i = i1) → q j }) (p i)

  cong : ∀ {ℓ'} {B : Set ℓ'} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
  cong f p = λ i → f (p i)

fill : {ℓ : I → Level} → (A : (i : I) → Set (ℓ i)) → (φ : I) →
  ((i : I) → Partial φ (A i)) → A i0 → (i : I) → A i
fill A φ u a0 i = unsafeComp (λ j → A (i ∧ j)) (φ ∨ ~ i)
  (λ j → unsafePOr φ (~ i) (u (i ∧ j)) λ { (i = i0) → a0 }) a0

transp : {ℓ : I → Level} → (A : (i : I) → Set (ℓ i)) → A i0 → A i1
transp A x = primComp A i0 (λ _ → empty) x

coep : ∀ {ℓ} → (p : ∀ i → Set ℓ) → (a : p i0) → PathP p a (transp p a)
coep p a i = fill p i0 (λ _ → empty) a i

transp-refl : ∀{ℓ} → {A : Set ℓ} → (x : A) → transp (λ _ → A) x ≡ x
transp-refl {A = A} x = sym (coep (λ _ → A) x)

module _ {ℓ} (A : Set ℓ) where
  isContr : Set ℓ
  isContr = Σ[ x ∈ A ] (∀ y → x ≡ y)

  isProp  : Set ℓ
  isProp  = (x y : A) → x ≡ y

contrIsProp : ∀ {ℓ} {A : Set ℓ} → isContr A → isProp A
contrIsProp h x y = trans (sym (h .snd x)) (h .snd y)
propIsSet : ∀ {ℓ} {A : Set ℓ} → isProp A → (x y : A) → isProp (x ≡ y)
propIsSet {A = A} AisProp x y p q i j = primComp (λ _ → A) (i ∨ ~ i ∨ j ∨ ~ j)
    (λ { k (i = i0) → AisProp x (p j) k ; k (i = i1) → AisProp x (q j) k ;
         k (j = i0) → AisProp x x k ; k (j = i1) → AisProp x y k })
    x

module _ {ℓ ℓ'} {A : Set ℓ} {x : A}
         (P : ∀ y → x ≡ y → Set ℓ') (d : P x ((λ i → x))) where
  pathJ : (y : A) → (p : x ≡ y) → P y p
  pathJ _ p = transp (λ i → P (p i) (λ j → p (i ∧ j))) d

  pathJprop : pathJ x refl ≡ d
  pathJprop i = primComp (λ _ → P x refl) i (λ {j (i = i1) → d}) d

fiber : ∀ {ℓ ℓ'} {E : Set ℓ} {B : Set ℓ'} (f : E → B) (y : B) → Set (ℓ ⊔ ℓ')
fiber {E = E} f y = Σ[ x ∈ E ] y ≡ f x

module _ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') where
  isEquiv : (A → B) → Set (ℓ ⊔ ℓ')
  isEquiv f = (y : B) → isContr (fiber f y)

  infix 4 _≃_
  _≃_ = Σ _ isEquiv

≃-refl : ∀ {ℓ} → {A : Set ℓ} → A ≃ A
≃-refl {A = A} = (λ a → a) , (λ y → (y , refl) , λ fib i → fib .snd i , λ j → fib .snd (i ∧ j))

-- below are some assorted lemmas

equiv-pullback : ∀ {ℓA ℓB ℓP} {A : Set ℓA} {B : Set ℓB} (e : A ≃ B) {P : B → Set ℓP} → (∀ a → P (e .fst a)) → ∀ b → P b
equiv-pullback e {P} IH b =
  let fib = e .snd b .fst
  in transp (λ i → P (e .snd b .fst .snd (~ i))) (IH (e .snd b .fst .fst))
equiv-pullback-refl : ∀ {ℓA ℓB ℓP} {A : Set ℓA} {B : Set ℓB} (e : A ≃ B) {P : B → Set ℓP} → (IH : ∀ a → P (e .fst a)) → ∀ a → equiv-pullback e {P} IH (e .fst a) ≡ IH a
equiv-pullback-refl e {P} IH a = trans
  (λ j → let fib = e .snd (e .fst a) .snd (a , refl) j in transp (λ i → P (fib .snd (~ i))) (IH (fib .fst)))
  (transp-refl (IH a))

equiv-pullback-J : ∀ {ℓI ℓA ℓB ℓP} {I : Set ℓI} {A : Set ℓA} {t : A → I} {B : I → Set ℓB}
                     (e : ∀ i → (Σ[ a ∈ A ] (t a ≡ i)) ≃ B i) (P : ∀ i → B i → Set ℓP)
                     (IH : ∀ a → P (t a) (e (t a) .fst (a , refl))) →
                   Σ[ f ∈ (∀ i b → P i b) ] (∀ a → f (t a) (e (t a) .fst (a , refl)) ≡ IH a)
equiv-pullback-J e P IH .fst i b =
  equiv-pullback (e i) (λ { (a , p) →
  pathJ (λ i p → P i (e i .fst (a , p)))
  (IH a) i p }) b
equiv-pullback-J {t = t} e P IH .snd a = trans
  (equiv-pullback-refl (e (t a)) {P = λ b → P (t a) b} (λ { (a2 , p) →
   pathJ (λ i p → P i (e i .fst (a2 , p))) (IH a2) (t a) p }) (a , refl))
  (pathJprop (λ i p → P i (e i .fst (a , p))) (IH a))

module _ {ℓA ℓB ℓC} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} where
  abstract
    isEquiv-trans : (eq1 : A ≃ B) → (eq2 : B ≃ C) → isEquiv A C (λ a → eq2 .fst (eq1 .fst a))
    isEquiv-trans (f , feq) (g , geq) c .fst .fst = feq (geq c .fst .fst) .fst .fst
    isEquiv-trans (f , feq) (g , geq) c .fst .snd = trans (geq c .fst .snd) (cong g (feq (geq c .fst .fst) .fst .snd))
    isEquiv-trans (f , feq) (g , geq) c .snd (a , sec) =
      let sec' : geq c .fst ≡ (f a , sec)
          sec' = geq c .snd (f a , sec)
          ffib : feq (f a) .fst ≡ (a , refl)
          ffib = feq (f a) .snd (a , refl)
      in trans (trans
         (λ i → feq (sec' i .fst) .fst .fst , trans (sec' i .snd) (cong g (feq (sec' i .fst) .fst .snd)))
         (λ i → ffib i .fst , trans sec (cong g (ffib i .snd))))
         (λ i → a , transp-refl sec i)

  ≃-trans : A ≃ B → B ≃ C → A ≃ C
  ≃-trans (f , feq) (g , geq) .fst a = g (f a)
  ≃-trans (f , feq) (g , geq) .snd = isEquiv-trans (f , feq) (g , geq)

module make-equiv {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} (f : A → B) (g : B → A) (s : ∀ b → f (g b) ≡ b) (t : ∀ a → g (f a) ≡ a) where
  -- Copied from the cubicaltt repository
  abstract
    f-isEquiv : isEquiv A B f
    f-isEquiv y = (g y , sym (s y)) , λ z → lemIso y (g y) (z .fst) (sym (s y)) (z .snd)
      where
      lemIso : (y : B) → (x0 x1 : A) → (p0 : y ≡ f x0) → (p1 : y ≡ f x1) → Path {A = fiber f y} (x0 , p0) (x1 , p1)
      lemIso y x0 x1 p0 p1 i = p i , sq1 i
        where
        rem0 : g y ≡ x0
        rem0 i = primComp (λ _ → A) (i ∨ ~ i) (λ { k (i = i1) → t x0 k ; k (i = i0) → g y }) (g (p0 i))

        rem1 : g y ≡ x1
        rem1 i = primComp (λ _ → A) (i ∨ ~ i) (λ { k (i = i1) → t x1 k ; k (i = i0) → g y }) (g (p1 i))

        p : x0 ≡ x1
        p i = primComp (λ _ → A) (i ∨ ~ i) (λ { k (i = i0) → rem0 k ; k (i = i1) → rem1 k }) (g y)

        fill0 : PathP (λ i → g (p0 i) ≡ rem0 i) (λ j → g y) (t x0)
        fill0 i j = primComp (λ _ → A) (i ∨ ~ i ∨ ~ j)
          (λ { k (i = i1) → t x0 (j ∧ k) ; k (i = i0) → g y ; k (j = i0) → g (p0 i) })
          (g (p0 i))

        fill1 : PathP (λ i → g (p1 i) ≡ rem1 i) (λ j → g y) (t x1)
        fill1 i j = primComp (λ _ → A) (i ∨ ~ i ∨ ~ j)
          (λ { k (i = i1) → t x1 (j ∧ k) ; k (i = i0) → g y ; k (j = i0) → g (p1 i) })
          (g (p1 i))

        fill2 : PathP (λ i → g y ≡ p i) rem0 rem1
        fill2 i j = primComp (λ _ → A) (i ∨ ~ i ∨ ~ j)
          (λ { k (i = i0) → rem0 (j ∧ k) ; k (i = i1) → rem1 (j ∧ k) ; k (j = i0) → g y })
          (g y)

        sq : PathP (λ i → g y ≡ g (f (p i))) (λ j → g (p0 j)) (λ j → g (p1 j))
        sq i j = primComp (λ _ → A) (i ∨ ~ i ∨ j ∨ ~ j)
          (λ { k (i = i0) → fill0 j (~ k) ; k (i = i1) → fill1 j (~ k) ;
               k (j = i0) → g y ; k (j = i1) → t (p i) (~ k) })
          (fill2 i j)

        sq1 : PathP (λ i → y ≡ f (p i)) p0 p1
        sq1 i j = primComp (λ _ → B) (i ∨ ~ i ∨ j ∨ ~ j)
          (λ { k (i = i0) → s (p0 j) k ; k (i = i1) → s (p1 j) k ; k (j = i1) → s (f (p i)) k ; k (j = i0) → s y k })
          (f (sq i j))

module make-equiv-approx {ℓX ℓA ℓB} {X : Set ℓX} {A : X → Set ℓA} {B : X → Set ℓB} (f : ∀ x → A x → B x) (x y : X) (p : y ≡ x)
  (g : B x → A y)
  (s : ∀ b → PathP (λ i → B (p i)) (f y (g b)) b) (t : ∀ a → PathP (λ i → A (p i)) (g (f x a)) a) where
  f-isEquiv : isEquiv (A x) (B x) (f x)
  f-isEquiv = pathJ
    (λ y p →
      (g : B x → A y) →
      (∀ b → PathP (λ i → B (sym p i)) (f y (g b)) b) →
      (∀ a → PathP (λ i → A (sym p i)) (g (f x a)) a) →
      isEquiv (A x) (B x) (f x))
    (λ g s t → make-equiv.f-isEquiv (f x) g s t)
    y (sym p) g s t

module equiv-Σ {ℓA1 ℓA2 ℓB1 ℓB2} {A1 : Set ℓA1} {A2 : Set ℓA2} {B1 : A1 → Set ℓB1} {B2 : A2 → Set ℓB2} (Aeq : A1 ≃ A2) (Beq : ∀ a → B1 a ≃ B2 (Aeq .fst a)) where
  abstract
    depfiber : (fa : A1 → A2) → (fb : ∀ a → B1 a → B2 (fa a)) → (a2 : A2) → (a1 : fiber fa a2) → (b2 : B2 a2) → Set (ℓB1 ⊔ ℓB2)
    depfiber fa fb a2 a1 b2 = Σ (B1 (a1 .fst)) (λ b1 → PathP (λ i → B2 (a1 .snd i)) b2 (fb _ b1))
    isDepEquiv : (Aeq : A1 ≃ A2) → (∀ a → B1 a → B2 (Aeq .fst a)) → Set (ℓA1 ⊔ ℓA2 ⊔ ℓB1 ⊔ ℓB2)
    isDepEquiv Aeq fb = (a2 : A2) → (b2 : B2 a2) →
      Σ (depfiber (Aeq .fst) fb a2 (Aeq .snd a2 .fst) b2) (λ bfib →
      (a1' : fiber (Aeq .fst) a2) → (bfib' : depfiber (Aeq .fst) fb a2 a1' b2) →
      PathP (λ i → depfiber (Aeq .fst) fb a2 (Aeq .snd a2 .snd a1' i) b2) bfib bfib')
    Beq-isDepEquiv : isDepEquiv Aeq (λ a1 b1 → Beq a1 .fst b1)
    Beq-isDepEquiv a2 b2 .fst =
      let a1 = Aeq .snd a2 .fst .fst
          asec : Path a2 (Aeq .fst a1)
          asec = Aeq .snd a2 .fst .snd
          b2' : PathP (λ i → B2 (asec i)) b2 (transp (λ i → B2 (asec i)) b2)
          b2' = coep (λ i → B2 (asec i)) b2
          b1 = Beq a1 .snd (b2' i1) .fst .fst
          bsec = Beq a1 .snd (b2' i1) .fst .snd
          bsec-type-path = λ k → PathP (λ i → B2 (asec (i ∨ ~ k))) (b2' (~ k)) (Beq a1 .fst b1)
          bsec' : PathP bsec-type-path bsec (transp bsec-type-path bsec)
          bsec' k = coep bsec-type-path bsec k
      in b1 , bsec' i1
    Beq-isDepEquiv a2 b2 .snd (a1' , asec') (b1' , bsec') = 
      let a1 = Aeq .snd a2 .fst .fst
          asec : Path a2 (Aeq .fst a1)
          asec = Aeq .snd a2 .fst .snd
          b2p : PathP (λ i → B2 (asec i)) b2 (transp (λ i → B2 (asec i)) b2)
          b2p = coep (λ i → B2 (asec i)) b2
          b1 = Beq a1 .snd (b2p i1) .fst .fst
          bsec : Path {A = B2 (Aeq .fst a1)} (b2p i1) (Beq a1 .fst b1)
          bsec = Beq a1 .snd (b2p i1) .fst .snd
          bsec-type-path = λ k → PathP (λ i → B2 (asec (i ∨ ~ k))) (b2p (~ k)) (Beq a1 .fst b1)
          bsecp : PathP bsec-type-path bsec (transp bsec-type-path bsec)
          bsecp k = coep bsec-type-path bsec k
          bfibp : PathP (λ k → depfiber (Aeq .fst) (λ a → Beq a .fst) (asec (~ k)) (a1 , λ i → asec (i ∨ ~ k)) (b2p (~ k)))
                  (b1 , bsec) (b1 , bsecp i1)
          bfibp k = b1 , bsecp k
          auniq : Path {A = fiber (Aeq .fst) a2} (a1 , asec) (a1' , asec')
          auniq = Aeq .snd a2 .snd (a1' , asec')
          b2pp : (i j : I) → B2 (auniq i .snd j)
          b2pp i j = fill (λ i → B2 (auniq i .snd j)) (~ j) (λ { _ (j = i0) → b2 }) (b2p j) i
          buniq : ∀ y → Path {A = depfiber (Aeq .fst) (λ a → Beq a .fst) (Aeq .fst a1) (a1 , refl) (b2p i1)} (b1 , bsec) y
          buniq = Beq a1 .snd (b2p i1) .snd
          buniq-type-path : I → Set (ℓB1 ⊔ ℓB2)
          buniq-type-path k = ∀ y →
            PathP (λ i → depfiber (Aeq .fst) (λ a → Beq a .fst)
              (auniq (i ∧ k) .snd (~ k)) (auniq (i ∧ k) .fst , λ j → auniq (i ∧ k) .snd (j ∨ ~ k)) (b2pp (i ∧ k) (~ k)))
              (bfibp k) y
      in
      transp buniq-type-path buniq (b1' , bsec')

  func : Σ A1 B1 → Σ A2 B2
  func (a , b) = Aeq .fst a , Beq a .fst b

  abstract
    func-isEquiv : isEquiv _ _ func
    func-isEquiv (a2 , b2) .fst .fst = Aeq .snd a2 .fst .fst , Beq-isDepEquiv a2  b2 .fst .fst
    func-isEquiv (a2 , b2) .fst .snd = λ j → Aeq .snd a2 .fst .snd j , Beq-isDepEquiv a2 b2 .fst .snd j
    func-isEquiv (a2 , b2) .snd ((a , b) , sec) =
      let asec : fiber (Aeq .fst) a2
          asec = a , λ i → sec i .fst
          bsec : depfiber (Aeq .fst) (λ a → Beq a .fst) a2 asec b2
          bsec = b , λ i → sec i .snd
          apath = Aeq .snd a2 .snd asec
          bpath = Beq-isDepEquiv a2 b2 .snd asec bsec
      in λ k → (apath k .fst , bpath k .fst) , λ j → apath k .snd j , bpath k .snd j

  equiv-Σ : Σ A1 B1 ≃ Σ A2 B2
  equiv-Σ .fst = func
  equiv-Σ .snd = func-isEquiv
open equiv-Σ using (equiv-Σ) public

module path-equivs {ℓA ℓB} {A : I → Set ℓA} {B : I → Set ℓB} (feq : ∀ i → A i ≃ B i) where
  f : ∀ i → A i → B i
  f i = feq i .fst
  f-isEquiv : ∀ i → isEquiv (A i) (B i) (f i)
  f-isEquiv i = feq i .snd

  contract-inverse : ∀ i b → f-isEquiv i b .snd (f-isEquiv i b .fst) ≡ refl
  contract-inverse i b = propIsSet (contrIsProp (f-isEquiv i b)) _ _ _ _

  abstract
    path-equiv' : ∀ {b1 b2} → (pb : PathP B b1 b2) →
      isContr (Σ (PathP A (f-isEquiv i0 b1 .fst .fst) (f-isEquiv i1 b2 .fst .fst)) (λ pa →
                 PathP (λ i → PathP B (f-isEquiv i0 b1 .fst .snd i) (f-isEquiv i1 b2 .fst .snd i)) pb (λ i → f i (pa i))))
    path-equiv' pb .fst .fst i = f-isEquiv i (pb i) .fst .fst
    path-equiv' pb .fst .snd j i = f-isEquiv i (pb i) .fst .snd j
    path-equiv' {b1} {b2} pb .snd (pa , sec) =
      λ k → (λ i → slice-path i k .fst) , (λ j i → slice-path i k .snd j)
      where
      slice-pa : PathP (λ i → fiber (f i) (pb i)) (f-isEquiv i0 b1 .fst) (f-isEquiv i1 b2 .fst)
      slice-pa i = pa i , λ j → sec j i
      slice-path : PathP (λ i → f-isEquiv i (pb i) .fst ≡ slice-pa i) refl refl
      slice-path i j = primComp (λ k → fiber (f i) (pb i)) (i ∨ ~ i ∨ j ∨ ~ j)
        (λ { k (i = i0) → contract-inverse i0 b1 k j ; k (i = i1) → contract-inverse i1 b2 k j ;
             k (j = i0) → f-isEquiv i (pb i) .fst ; k (j = i1) → slice-pa i })
        (f-isEquiv i (pb i) .snd (slice-pa i) j)

    path-equiv : ∀ x1 x2 → isEquiv (PathP A x1 x2) (PathP B (f i0 x1) (f i1 x2)) (λ p i → f i (p i))
    path-equiv x1 x2 pb =
      let b1p = f-isEquiv i0 (f i0 x1) .snd (x1 , refl)
          b2p = f-isEquiv i1 (f i1 x2) .snd (x2 , refl)
      in transp (λ k → isContr
           (Σ (PathP A (b1p k .fst) (b2p k .fst)) (λ pa →
            PathP (λ i → PathP B (b1p k .snd i) (b2p k .snd i)) pb (λ i → f i (pa i)))))
         (path-equiv' pb)

  P≃ : ∀ x1 x2 → PathP A x1 x2 ≃ (PathP B (f i0 x1) (f i1 x2))
  P≃ x1 x2 = (λ p i → f i (p i)) , path-equiv x1 x2

module deg-sq {ℓ} {A : Set ℓ} where
  expand : ∀ {x y z : A} (p : x ≡ y) (q : y ≡ z) (k : I) →
           PathP (λ i → p (~ k ∨ i) ≡ q (k ∧ i)) (λ i → p (~ k ∨ i)) (λ i → q (k ∧ i))
  expand {y = y} p q k i j = fill (λ k → A) (i ∨ ~ i ∨ j ∨ ~ j)
    (λ { k (i = i0) → p (~ k ∨ j) ; k (i = i1) → q (k ∧ j) ;
         k (j = i0) → p (~ k ∨ i) ; k (j = i1) → q (k ∧ i) })
    y k
  module dep {ℓ₂} {B : A → Set ℓ₂} where
    expand-dep : ∀ {x y z : A} {p : x ≡ y} {q : y ≡ z} {xx : B x} {yy : B y} {zz : B z}
                 (pp : PathP (λ i → B (p i)) xx yy) (qq : PathP (λ i → B (q i)) yy zz) →
                 ∀ k → PathP (λ i → PathP (λ j → B (expand p q k i j)) (pp (~ k ∨ i)) (qq (k ∧ i))) (λ i → pp (~ k ∨ i)) (λ i → qq (k ∧ i))
    expand-dep {p = p} {q = q} {yy = yy} pp qq k i j = fill (λ k → B (expand p q k i j))
      (i ∨ ~ i ∨ j ∨ ~ j)
      (λ { k (i = i0) → pp (~ k ∨ j) ; k (i = i1) → qq (k ∧ j) ;
           k (j = i0) → pp (~ k ∨ i) ; k (j = i1) → qq (k ∧ i) })
      yy k


