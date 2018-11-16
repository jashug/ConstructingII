{-# OPTIONS --cubical --safe #-}
-- note: --cubical implies --without-K

-- Checked with Agda 2.6.0 commit bd338484d

module RunningExample where

open import Prelude
open import Chain

-- given a type (X : Set), simulate the inductive-inductive type
-- A : Set
-- B : A → Set
-- η : X → A
-- join : (a : A) → B a → A
-- inj : (a : A) → B a

module _ ℓX (X : Set ℓX) where

  -- Figure 1:
  -- inductive objects / algebras
  record Alg : Set (lsuc ℓX) where
    field
      A : Set ℓX
      B : A → Set ℓX
      η : X → A
      join : (a : A) → B a → A
      inj : (a : A) → B a

  -- the motives and methods for the simple elimination rules
  record Motives-Methods ℓ (T : Alg) : Set (lsuc ℓ ⊔ ℓX) where
    open Alg T
    field
      PA : A → Set ℓ
      PB : ∀ a → B a → Set ℓ
      Pη : ∀ x → PA (η x)
      Pjoin : ∀ a → PA a → ∀ b → PB a b → PA (join a b)
      Pinj : ∀ a → PA a → PB a (inj a)

  -- the eliminators and equations for the simple elimination rules
  record Eliminators-Equations ℓ (T : Alg) (P : Motives-Methods ℓ T) : Set (ℓ ⊔ ℓX) where
    open Alg T
    open Motives-Methods P
    field
      EA : ∀ a → PA a
      EB : ∀ a b → PB a b
      Eη : ∀ x → EA (η x) ≡ Pη x
      Ejoin : ∀ a b → EA (join a b) ≡ Pjoin a (EA a) b (EB a b)
      Einj : ∀ a → EB a (inj a) ≡ Pinj a (EA a)

  -- we want to prove that there is some T such that for all levels ℓ, we have simple-eliminators ℓ T.
  simple-eliminators : ∀ ℓ → Alg → Set (lsuc ℓ ⊔ ℓX)
  simple-eliminators ℓ T = (P : Motives-Methods ℓ T) → Eliminators-Equations ℓ T P

  module pre where
    -- Section 5.1: pre-syntax
    -- this is a standard mutual inductive definition
    data A : Set ℓX
    data B : Set ℓX
    data A where
      η : X → A
      join : A → B → A
    data B where
      inj : A → B

  -- Section 5.2: goodness algebras
  -- now we define Ix and Arg
  Ix-A : Set
  Ix-A = ⊤
  Ix-B : (goodA : Ix-A → pre.A → Set ℓX) → Set ℓX
  Ix-B goodA = Σ[ a ∈ pre.A ] goodA ★ a
  Arg-η : X → Ix-A → Set ℓX
  Arg-η x ϕ = Σ[ _ ∈ ⊤ ] (★ ≡ ϕ)
  Arg-join : (goodA : Ix-A → pre.A → Set ℓX) → (goodB : Ix-B goodA → pre.B → Set ℓX) →
             Σ[ _ ∈ pre.A ] pre.B → Ix-A → Set ℓX
  Arg-join goodA goodB (a , b) ϕ = Σ[ p ∈ Σ[ good-a ∈ goodA ★ a ] goodB (a , good-a) b ] (★ ≡ ϕ)
  Arg-inj : (goodA : Ix-A → pre.A → Set ℓX) → pre.A → Ix-B goodA → Set ℓX
  Arg-inj goodA a ϕ = Σ[ good-a ∈ goodA ★ a ] ((a , good-a) ≡ ϕ)

  -- and use these to define goodness algebras
  record Good : Set (lsuc ℓX) where
    field
      A : Ix-A → pre.A → Set ℓX
      B : Ix-B A → pre.B → Set ℓX
      η : (x : X) → ∀ ϕ → Arg-η x ϕ → A ϕ (pre.η x)
      join : ∀ p ϕ → Arg-join A B p ϕ → A ϕ (pre.join (p .fst) (p .snd))
      inj : ∀ a ϕ → Arg-inj A a ϕ → B ϕ (pre.inj a)

  -- which can be turned into Alg
  Good→Alg : Good → Alg
  Good→Alg G .Alg.A = Σ[ a ∈ pre.A ] G .Good.A ★ a
  Good→Alg G .Alg.B ϕ = Σ[ b ∈ pre.B ] G .Good.B ϕ b
  Good→Alg G .Alg.η x = pre.η x , G .Good.η x ★ (★ , refl)
  Good→Alg G .Alg.join (pre-a , good-a) (pre-b , good-b) =
    pre.join pre-a pre-b , G .Good.join (pre-a , pre-b) ★ ((good-a , good-b) , refl)
  Good→Alg G .Alg.inj (pre-a , good-a) =
    pre.inj pre-a , G .Good.inj pre-a (pre-a , good-a) (good-a , refl)

  -- and goodness algebras are inhabited
  O : Good
  O .Good.A ϕ a = ⊤
  O .Good.B ϕ b = ⊤
  O .Good.η x ϕ t = ★
  O .Good.join (a , b) ϕ t = ★
  O .Good.inj a ϕ t = ★

  -- Section 5.3: niceness
  record Nice (G : Good) : Set ℓX where
    open Good G
    field
      Nη : ∀ x ϕ → isEquiv (Arg-η x ϕ) (A ϕ (pre.η x)) (η x ϕ)
      Njoin : ∀ p ϕ → isEquiv (Arg-join A B p ϕ) (A ϕ (pre.join (p .fst) (p .snd))) (join p ϕ)
      Ninj : ∀ a ϕ → isEquiv (Arg-inj A a ϕ) (B ϕ (pre.inj a)) (inj a ϕ)

  -- Lemma 6: nice goodness algebras give objects with simple eliminaton rules
  nice-goodness-to-simple-eliminators : ∀ G → Nice G → ∀ ℓ → simple-eliminators ℓ (Good→Alg G)
  nice-goodness-to-simple-eliminators G N ℓ P = record
    {
      EA = λ a → EA (a .fst) (a .snd);
      EB = λ ϕ b → EB (b .fst) ϕ (b .snd);
      Eη = λ x → equiv-pullback-J
        (λ ϕ → η x ϕ , Nη x ϕ)
        (λ ϕ good-a → PA (pre.η x , good-a))
        (λ { ★ → Pη x })
        .snd ★;
      Ejoin = λ { (a , good-a) (b , good-b) → equiv-pullback-J
        (λ ϕ → join (a , b) ϕ , Njoin (a , b) ϕ)
        (λ ϕ good-a → PA (pre.join a b , good-a))
        (λ { (good-a , good-b) → Pjoin (a , good-a) (EA a good-a)
                                       (b , good-b) (EB b (a , good-a) good-b) })
        .snd (good-a , good-b)
        };
      Einj = λ { (a , good-a) → equiv-pullback-J
        (λ ϕ → inj a ϕ , Ninj a ϕ)
        (λ ϕ good-b → PB ϕ (pre.inj a , good-b))
        (λ good-a → Pinj (a , good-a) (EA a good-a))
        .snd good-a
        }
    }
    where
    open Good G
    open Nice N
    open Motives-Methods P

    EA : (pre-a : pre.A) → (good-a : A ★ pre-a) → PA (pre-a , good-a)
    EB : (pre-b : pre.B) → (ϕ : Ix-B A) → (good-b : B ϕ pre-b) → PB ϕ (pre-b , good-b)
    EA (pre.η x) =
      equiv-pullback-J
      (λ ϕ → η x ϕ , Nη x ϕ)
      (λ ϕ good-a → PA (pre.η x , good-a))
      (λ { ★ → Pη x }) .fst ★
    EA (pre.join a b) =
      equiv-pullback-J
      (λ ϕ → join (a , b) ϕ , Njoin (a , b) ϕ)
      (λ ϕ good-a → PA (pre.join a b , good-a))
      (λ { (good-a , good-b) → Pjoin (a , good-a) (EA a good-a)
                                     (b , good-b) (EB b (a , good-a) good-b) }) .fst ★
    EB (pre.inj a) ϕ =
      equiv-pullback-J
      (λ ϕ → inj a ϕ , Ninj a ϕ)
      (λ ϕ good-b → PB ϕ (pre.inj a , good-b))
      (λ good-a → Pinj (a , good-a) (EA a good-a)) .fst ϕ

  -- Section 5.4: successor goodness algebra
  module succ (G : Good) where
    module E where
      A : (a : pre.A) → (ϕ : Ix-A) → Σ[ Y ∈ Set ℓX ] (Y → G .Good.A ϕ a)
      B : (b : pre.B) → (ϕ : Ix-B (G .Good.A)) → Σ[ Y ∈ Set ℓX ] (Y → G .Good.B ϕ b)
      A (pre.η x) ϕ = Arg-η x ϕ , G .Good.η x ϕ
      A (pre.join a b) ϕ = Arg-join (G .Good.A) (G .Good.B) (a , b) ϕ , G .Good.join (a , b) ϕ
      B (pre.inj a) ϕ = Arg-inj (G .Good.A) a ϕ , G .Good.inj a ϕ

    πA : Ix-A → Ix-A
    πA ★ = ★
    newA : Ix-A → pre.A → Set ℓX
    newA ϕ a = E.A a (πA ϕ) .fst
    
    πB : Ix-B newA → Ix-B (G .Good.A)
    πB (pre-a , good-a) = pre-a , E.A pre-a ★ .snd good-a
    newB : Ix-B newA → pre.B → Set ℓX
    newB ϕ b = E.B b (πB ϕ) .fst

    πη : ∀ x ϕ → Arg-η x ϕ → Arg-η x (πA ϕ)
    πη x ϕ (★ , p) = ★ , cong πA p

    πjoin : ∀ p ϕ → Arg-join newA newB p ϕ → Arg-join (G .Good.A) (G .Good.B) p (πA ϕ)
    πjoin (a , b) ϕ ((good-a , good-b) , p) =
      let aG = E.A a ★ .snd good-a in
      (aG , E.B b (a , aG) .snd good-b), cong πA p

    πinj : ∀ a ϕ → Arg-inj newA a ϕ → Arg-inj (G .Good.A) a (πB ϕ)
    πinj a ϕ (good-a , p) = E.A a ★ .snd good-a , cong πB p

    alg : Good
    alg .Good.A = newA
    alg .Good.B = newB
    alg .Good.η = πη
    alg .Good.join = πjoin
    alg .Good.inj = πinj

  -- See Chain.agda for the Limit of Sets subsection of Section 5.5

  -- Section 5.5: limit of goodness algebras
  module limit (O : Good) where
    open chain-≃

    S^ : ℕ → Good
    S^ zero = O
    S^ (suc n) = succ.alg (S^ n)

    Ix-≃-A : Ix-A ≃ chain.t (λ n i → Ix-A) (λ n → succ.πA (S^ n))
    Ix-≃-A = A-≃-CA

    module limit-A (ϕ : Ix-A) (a : pre.A) = limit-sort
      (λ n → Ix-A)
      (λ n → succ.πA (S^ n))
      (λ n ϕ → S^ n .Good.A ϕ a)
      (λ n ϕ → succ.E.A (S^ n) a ϕ .fst)
      (λ n ϕ → succ.E.A (S^ n) a ϕ .snd)
      (λ n ϕ y → y)
      (Ix-≃-A .fst ϕ)

    Ix-≃-B : Ix-B limit-A.t ≃ chain.t (λ n i → Ix-B (S^ n .Good.A)) (λ n → succ.πB (S^ n))
    Ix-≃-B = Σ-≃-CΣ A-≃-CA λ a → ≃-refl

    module limit-B (ϕ : Ix-B limit-A.t) (b : pre.B) = limit-sort
      (λ n → Ix-B (S^ n .Good.A))
      (λ n → succ.πB (S^ n))
      (λ n ϕ → S^ n .Good.B ϕ b)
      (λ n ϕ → succ.E.B (S^ n) b ϕ .fst)
      (λ n ϕ → succ.E.B (S^ n) b ϕ .snd)
      (λ n ϕ y → y)
      (Ix-≃-B .fst ϕ)

    module limit-η (x : X) (ϕ : Ix-A) where
      ≃ : Arg-η x ϕ ≃ limit-A.t ϕ (pre.η x)
      ≃ = ≃-trans (Σ-≃-CΣ A-≃-CA (λ _ → P-≃-CP (λ i → Ix-≃-A)))
                  (limit-A.st-≃-t ϕ (pre.η x))
      f = ≃ .fst
      isEq = ≃ .snd

    module limit-join (p : Σ[ a ∈ pre.A ] pre.B) (ϕ : Ix-A) where
      ≃ : Arg-join limit-A.t limit-B.t p ϕ ≃ limit-A.t ϕ (pre.join (p .fst) (p .snd))
      ≃ = ≃-trans (Σ-≃-CΣ (Σ-≃-CΣ ≃-refl (λ _ → ≃-refl)) (λ _ → P-≃-CP λ i → Ix-≃-A))
                  (limit-A.st-≃-t ϕ (pre.join (p .fst) (p .snd)))
      f = ≃ .fst
      isEq = ≃ .snd

    module limit-inj (a : pre.A) (ϕ : Ix-B limit-A.t) where
      ≃ : Arg-inj limit-A.t a ϕ ≃ limit-B.t ϕ (pre.inj a)
      ≃ = ≃-trans (Σ-≃-CΣ ≃-refl λ _ → P-≃-CP λ i → Ix-≃-B)
                  (limit-B.st-≃-t ϕ (pre.inj a))
      f = ≃ .fst
      isEq = ≃ .snd

    L : Good
    L .Good.A = limit-A.t
    L .Good.B = limit-B.t
    L .Good.η = limit-η.f
    L .Good.join = limit-join.f
    L .Good.inj = limit-inj.f

    LN : Nice L
    LN .Nice.Nη = limit-η.isEq
    LN .Nice.Njoin = limit-join.isEq
    LN .Nice.Ninj = limit-inj.isEq

  -- Theorem 2
  T : Alg
  T = Good→Alg (limit.L O)
  T-elim : ∀ ℓ → simple-eliminators ℓ T
  T-elim ℓ = nice-goodness-to-simple-eliminators (limit.L O) (limit.LN O) ℓ
