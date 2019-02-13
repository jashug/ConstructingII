{-# OPTIONS --without-K --safe #-}

-- Argue that Forsberg's construction of inductive-inductive types implies UIP (or Axiom K)
-- Mirrors the Coq development
-- Checked with Agda 2.6.0 commit bd338484d

open import Agda.Primitive public

data _≡_ {ℓ} {X : Set ℓ} (x : X) : X → Set ℓ where
  refl : x ≡ x

trans : ∀ {ℓ} {X : Set ℓ} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
trans p refl = p

cong : ∀ {ℓ1 ℓ2} {X : Set ℓ1} {Y : Set ℓ2} {x y : X} (f : X → Y) → x ≡ y → f x ≡ f y
cong f refl = refl

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

-- homotopy proposition
mere-proposition : ∀ {ℓ} (X : Set ℓ) → Set ℓ
mere-proposition X = (x y : X) → x ≡ y

-- homotopy set
UIP-holds : ∀ {ℓ} (X : Set ℓ) → Set ℓ
UIP-holds X = (x y : X) (p q : x ≡ y) → p ≡ q

module UIP-from-Forsberg-II {ℓ} (X : Set ℓ) where
  -- Forsberg's translation of
  -- data A : Set ℓ
  -- data B : A → Set ℓ
  -- data A where
  --   η : X → A
  --   join : (a : A) → B a → A
  -- data B where
  --   inj : (a : A) → B a

  -- Fig 2: Pre-syntax for the running example
  data pre-A : Set ℓ
  data pre-B : Set ℓ
  data pre-A where
    pre-η : X → pre-A
    pre-join : pre-A → pre-B → pre-A
  data pre-B where
    pre-inj : pre-A → pre-B

  -- Fig 3: Construction given by Nordvall Forsberg
  data good-A : pre-A → Set ℓ
  data good-B : pre-A → pre-B → Set ℓ
  data good-A where
    good-η : (x : X) → good-A (pre-η x)
    good-join : ∀ a → good-A a → ∀ b → good-B a b → good-A (pre-join a b)
  data good-B where
    good-inj : ∀ a → good-A a → good-B a (pre-inj a)

  -- definition of the inductive-inductive object
  A : Set ℓ
  A = Σ pre-A good-A
  B : A → Set ℓ
  B a = Σ pre-B (good-B (a .fst))
  η : X → A
  η x = pre-η x , good-η x
  join : (a : A) → B a → A
  join (pre-a , good-a) (pre-b , good-b) = pre-join pre-a pre-b , good-join pre-a good-a pre-b good-b
  inj : (a : A) → B a
  inj (pre-a , good-a) = pre-inj pre-a , good-inj pre-a good-a

  record Motives ℓ2 : Set (ℓ ⊔ lsuc ℓ2) where
    field
      PA : A → Set ℓ2
      PB : ∀ a → B a → Set ℓ2
      Pη : ∀ x → PA (η x)
      Pjoin : ∀ a → PA a → ∀ b → PB a b → PA (join a b)
      Pinj : ∀ a → PA a → PB a (inj a)

  record Eliminated ℓ2 (M : Motives ℓ2) : Set (ℓ ⊔ ℓ2) where
    open Motives M
    field
      EA : ∀ a → PA a
      EB : ∀ a b → PB a b
      Eη : ∀ x → EA (η x) ≡ Pη x
      Ejoin : ∀ a b → EA (join a b) ≡ Pjoin a (EA a) b (EB a b)
      Einj : ∀ a → EB a (inj a) ≡ Pinj a (EA a)

  -- the definition of the simple elimnators (specifically for Forsberg's construction
  -- (restricted to eliminate into the same universe level as X)
  simple-eliminators : Set (lsuc ℓ)
  simple-eliminators = (M : Motives ℓ) → Eliminated ℓ M

  module unique-goodness-only-if-UIP where
    -- Section 2.1
    pattern _==_ x y = pre-join (pre-η x) (pre-inj (pre-η y))

    -- Lemma 1
    module XtoAtoX-retract (x : X) where
      XtoA : ∀ y → x ≡ y → good-A (x == y)
      XtoA .x refl = good-join _ (good-η x) _ (good-inj _ (good-η x))
      AtoX : ∀ y → good-A (x == y) → x ≡ y
      AtoX y (good-join .(pre-η y) good-a .(pre-inj (pre-η y)) (good-inj .(pre-η y) x)) = refl
      XtoAtoX-id : ∀ y (e : x ≡ y) → AtoX y (XtoA y e) ≡ e
      XtoAtoX-id .x refl = refl
    open XtoAtoX-retract

    module _ (A-unique : ∀ t → mere-proposition (good-A t)) where
      t : X → A
      t x = join (η x) (inj (η x))
      UIP-refl : (x : X) (p : x ≡ x) → refl ≡ p
      UIP-refl x p = trans
        (cong (AtoX x x) (A-unique (x == x) (t x .snd) (XtoA x x p)))
        (XtoAtoX-id x x p)
      -- note UIP-refl x refl = refl fails because K is disabled

      -- Lemma 2
      UIP : (x y : X) (p q : x ≡ y) → p ≡ q
      UIP x .x refl q = UIP-refl x q

      Axiom-K : ∀ ℓ2 (x : X) (P : x ≡ x → Set ℓ2) → P refl → ∀ p → P p
      Axiom-K ℓ2 x P IH p = helper p (UIP-refl x p)
        where
        helper : ∀ p → refl ≡ p → P p
        helper p refl = IH
  open unique-goodness-only-if-UIP using (UIP) public

  module simple-eliminators-only-if-unique-goodness where
    -- Section 2.2

    -- Lemma 3
    module AtoBtoA-retract where
      AtoB : ∀ t → good-A (t .fst) → B t
      AtoB t good-a = pre-inj (t .fst) , good-inj (t .fst) good-a
      BtoA : ∀ t → B t → good-A (t .fst)
      BtoA _ (_ , good-inj _ good-a) = good-a
      AtoBtoA-id : ∀ t good-a → BtoA t (AtoB t good-a) ≡ good-a
      AtoBtoA-id t good-a = refl
    open AtoBtoA-retract

    module _ (elim : simple-eliminators) where
      match-on-B : (P : ∀ a → B a → Set ℓ) (step-inj : ∀ a → P a (inj a)) → ∀ a b → P a b
      match-on-B P step-inj = elim record {
          PA = λ _ → ⊤;
          PB = P;
          Pη = λ _ → ★;
          Pjoin = λ _ _ _ _ → ★;
          Pinj = λ a _ → step-inj a
        } .Eliminated.EB

      -- Lemma 4
      B-contr : ∀ a → (b : B a) → inj a ≡ b
      B-contr = match-on-B (λ a b → inj a ≡ b) (λ a → refl)

      -- Lemma 5
      A-unique : ∀ t (a1 a2 : good-A t) → a1 ≡ a2
      A-unique t a1 a2 = let t' = t , a1 in cong (BtoA t') (B-contr t' (AtoB t' a2))
  open simple-eliminators-only-if-unique-goodness using (A-unique) public

open UIP-from-Forsberg-II using (simple-eliminators ; UIP ; A-unique)

-- Theorem 1
UIP-from-Forsberg-II : ∀ {ℓ} (X : Set ℓ) → simple-eliminators X → UIP-holds X
UIP-from-Forsberg-II X elim = UIP X (A-unique X elim)
