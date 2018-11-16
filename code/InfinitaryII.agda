{-# OPTIONS --cubical --safe #-}

module InfinitaryII where

open import Prelude
open import Chain

-- This II type has infinitary parameters

module _
  (AA : Set) (AB : AA → Set) (AC : AA → Set) (ACi : ∀ a → AC a → AB a)
  (BA : Set) (BB : BA → Set) (BC : BA → Set) (BCi : ∀ a → BC a → BB a)
  (Bi : ∀ a → BB a)
  where

  record Alg : Set₁ where
    field
      A : Set
      B : A → Set
      supA : (a : AA) → (chA : AB a → A) → (chB : (c : AC a) → B (chA (ACi a c))) → A
      supB : (a : BA) → (chA : BB a → A) → (chB : (c : BC a) → B (chA (BCi a c))) → B (chA (Bi a))

  -- the motives and methods for the simple elimination rules
  record Motives-Methods ℓ (T : Alg) : Set (lsuc ℓ) where
    open Alg T
    field
      PA : A → Set ℓ
      PB : ∀ a → B a → Set ℓ
      PsupA : ∀ a chA → ((b : AB a) → PA (chA b)) → ∀ chB → ((c : AC a) → PB _ (chB c)) → PA (supA a chA chB)
      PsupB : ∀ a chA → ((b : BB a) → PA (chA b)) → ∀ chB → ((c : BC a) → PB _ (chB c)) → PB _ (supB a chA chB)

  -- the eliminators and equations for the simple elimination rules
  record Eliminators-Equations ℓ (T : Alg) (P : Motives-Methods ℓ T) : Set ℓ where
    open Alg T
    open Motives-Methods P
    field
      EA : ∀ a → PA a
      EB : ∀ a b → PB a b
      EsupA : ∀ a chA chB → EA (supA a chA chB) ≡ PsupA a chA (λ b → EA (chA b)) chB (λ c → EB _ (chB c))
      EsupB : ∀ a chA chB → EB _ (supB a chA chB) ≡ PsupB a chA (λ b → EA (chA b)) chB (λ c → EB _ (chB c))

  -- we want to prove that there is some T such that for all levels ℓ, we have simple-eliminators ℓ T.
  simple-eliminators : ∀ ℓ → Alg → Set (lsuc ℓ)
  simple-eliminators ℓ T = (P : Motives-Methods ℓ T) → Eliminators-Equations ℓ T P

  module pre where
    -- Section 3.1: pre-syntax
    -- this is a standard mutual inductive definition
    data A : Set
    data B : Set
    data A where
      supA : (a : AA) → (AB a → A) → (AC a → B) → A
    data B where
      supB : (a : BA) → (BB a → A) → (BC a → B) → B

  -- Section 3.2: goodness algebras
  -- now we define Ix and Arg
  Ix-A : Set
  Ix-A = ⊤
  Ix-B : (goodA : Ix-A → pre.A → Set) → Set
  Ix-B goodA = Σ[ a ∈ pre.A ] goodA ★ a
  Arg-supA : (goodA : Ix-A → pre.A → Set) (goodB : Ix-B goodA → pre.B → Set) →
             (a : AA) → Σ[ _ ∈ (AB a → pre.A) ] (AC a → pre.B) → Ix-A → Set
  Arg-supA goodA goodB a (pre-chA , pre-chB) ϕ =
    Σ[ _ ∈ Σ[ good-chA ∈ ((b : AB a) → goodA ★ (pre-chA b)) ]
           ((c : AC a) → goodB (pre-chA (ACi a c) , good-chA (ACi a c)) (pre-chB c)) ]
    (★ ≡ ϕ)
  Arg-supB : (goodA : Ix-A → pre.A → Set) (goodB : Ix-B goodA → pre.B → Set) →
             (a : BA) → Σ[ _ ∈ (BB a → pre.A) ] (BC a → pre.B) → Ix-B goodA → Set
  Arg-supB goodA goodB a (pre-chA , pre-chB) ϕ =
    Σ[ p ∈ (Σ[ good-chA ∈ ((b : BB a) → goodA ★ (pre-chA b)) ]
           ((c : BC a) → goodB (pre-chA (BCi a c) , good-chA (BCi a c)) (pre-chB c))) ]
    ((pre-chA (Bi a) , p .fst (Bi a)) ≡ ϕ)

  -- and use these to define goodness algebras
  record Good : Set₁ where
    field
      A : Ix-A → pre.A → Set
      B : Ix-B A → pre.B → Set
      supA : ∀ a p ϕ → Arg-supA A B a p ϕ → A ϕ (pre.supA a (p .fst) (p .snd))
      supB : ∀ a p ϕ → Arg-supB A B a p ϕ → B ϕ (pre.supB a (p .fst) (p .snd))

  -- which can be turned into Alg
  Good→Alg : Good → Alg
  Good→Alg G .Alg.A = Σ[ a ∈ pre.A ] G .Good.A ★ a
  Good→Alg G .Alg.B ϕ = Σ[ b ∈ pre.B ] G .Good.B ϕ b
  Good→Alg G .Alg.supA a chA chB =
    pre.supA a (λ b → chA b .fst) (λ c → chB c .fst) ,
    G .Good.supA a ((λ b → chA b .fst) , (λ c → chB c .fst)) _  (((λ b → chA b .snd) , (λ c → chB c .snd)) , refl)
  Good→Alg G .Alg.supB a chA chB =
    pre.supB a (λ b → chA b .fst) (λ c → chB c .fst) ,
    G .Good.supB a ((λ b → chA b .fst) , (λ c → chB c .fst)) _  (((λ b → chA b .snd) , (λ c → chB c .snd)) , refl)

  -- and goodness algebras are inhabited
  O : Good
  O .Good.A ϕ a = ⊤
  O .Good.B ϕ b = ⊤
  O .Good.supA _ _ _ _ = ★
  O .Good.supB _ _ _ _ = ★

  -- Section 3.3: niceness
  record Nice (G : Good) : Set where
    open Good G
    field
      NsupA : ∀ a p ϕ → isEquiv _ _ (supA a p ϕ)
      NsupB : ∀ a p ϕ → isEquiv _ _ (supB a p ϕ)

  -- Lemma 6: nice goodness algebras give objects with simple eliminaton rules
  nice-goodness-to-simple-eliminators : ∀ G → Nice G → ∀ ℓ → simple-eliminators ℓ (Good→Alg G)
  nice-goodness-to-simple-eliminators G N ℓ P = record
    {
      EA = λ a → EA (a .fst) (a .snd);
      EB = λ ϕ b → EB (b .fst) ϕ (b .snd);
      EsupA = λ a chA chB → equiv-pullback-J
        (λ ϕ → supA a ((λ b → chA b .fst) , (λ c → chB c .fst)) ϕ , NsupA a ((λ b → chA b .fst) , (λ c → chB c .fst)) ϕ)
        (λ ϕ g → PA (pre.supA a (λ b → chA b .fst) (λ c → chB c .fst) , g))
        (λ { (good-chA , good-chB) → PsupA a
                (λ b → chA b .fst , good-chA b) (λ b → EA (chA b .fst) (good-chA b))
                (λ c → chB c .fst , good-chB c) (λ c → EB (chB c .fst) _ (good-chB c)) })
        .snd ((λ b → chA b .snd) , (λ c → chB c .snd));
      EsupB = λ a chA chB → equiv-pullback-J
        (λ ϕ → supB a ((λ b → chA b .fst) , (λ c → chB c .fst)) ϕ , NsupB a ((λ b → chA b .fst) , (λ c → chB c .fst)) ϕ)
        (λ ϕ g → PB _ (pre.supB a (λ b → chA b .fst) (λ c → chB c .fst) , g))
        (λ { (good-chA , good-chB) → PsupB a
                (λ b → chA b .fst , good-chA b) (λ b → EA (chA b .fst) (good-chA b))
                (λ c → chB c .fst , good-chB c) (λ c → EB (chB c .fst) _ (good-chB c)) })
        .snd ((λ b → chA b .snd) , (λ c → chB c .snd))
    }
    where
    open Good G
    open Nice N
    open Motives-Methods P

    EA : (pre-a : pre.A) → (good-a : A ★ pre-a) → PA (pre-a , good-a)
    EB : (pre-b : pre.B) → (ϕ : Ix-B A) → (good-b : B ϕ pre-b) → PB ϕ (pre-b , good-b)
    EA (pre.supA a chA chB) = 
      equiv-pullback-J
      (λ ϕ → supA a (chA , chB) ϕ , NsupA a (chA , chB) ϕ)
      (λ ϕ g → PA (pre.supA a chA chB , g))
      (λ { (good-chA , good-chB) → PsupA a
              (λ b → chA b , good-chA b) (λ b → EA (chA b) (good-chA b))
              (λ c → chB c , good-chB c) (λ c → EB (chB c) _ (good-chB c)) })
      .fst ★
    EB (pre.supB a chA chB) ϕ = equiv-pullback-J
      (λ ϕ → supB a (chA , chB) ϕ , NsupB a (chA , chB) ϕ)
      (λ ϕ g → PB ϕ (pre.supB a chA chB , g))
      (λ { (good-chA , good-chB) → PsupB a
              (λ b → chA b , good-chA b) (λ b → EA (chA b) (good-chA b))
              (λ c → chB c , good-chB c) (λ c → EB (chB c) _ (good-chB c)) })
      .fst ϕ

  -- Section 3.4: successor goodness algebra
  module succ (G : Good) where
    module E where
      A : (a : pre.A) → (ϕ : Ix-A) → Σ[ Y ∈ Set ] (Y → G .Good.A ϕ a)
      B : (b : pre.B) → (ϕ : Ix-B (G .Good.A)) → Σ[ Y ∈ Set ] (Y → G .Good.B ϕ b)
      A (pre.supA a chA chB) ϕ = Arg-supA (G .Good.A) (G .Good.B) a (chA , chB) ϕ , G .Good.supA a (chA , chB) ϕ
      B (pre.supB a chA chB) ϕ = Arg-supB (G .Good.A) (G .Good.B) a (chA , chB) ϕ , G .Good.supB a (chA , chB) ϕ

    πA : Ix-A → Ix-A
    πA ★ = ★
    newA : Ix-A → pre.A → Set
    newA ϕ a = E.A a (πA ϕ) .fst
    
    πB : Ix-B newA → Ix-B (G .Good.A)
    πB (pre-a , good-a) = pre-a , E.A pre-a ★ .snd good-a
    newB : Ix-B newA → pre.B → Set
    newB ϕ b = E.B b (πB ϕ) .fst

    πsupA : ∀ a p ϕ → Arg-supA newA newB a p ϕ → Arg-supA (G .Good.A) (G .Good.B) a p (πA ϕ)
    πsupA a (chA , chB) ϕ ((good-chA , good-chB) , p) =
      ((λ b → E.A (chA b) _ .snd (good-chA b)) , (λ c → E.B (chB c) _ .snd (good-chB c))) , cong πA p

    πsupB : ∀ a p ϕ → Arg-supB newA newB a p ϕ → Arg-supB (G .Good.A) (G .Good.B) a p (πB ϕ)
    πsupB a (chA , chB) ϕ ((good-chA , good-chB) , p) =
      ((λ b → E.A (chA b) _ .snd (good-chA b)) , (λ c → E.B (chB c) _ .snd (good-chB c))) , cong πB p

    alg : Good
    alg .Good.A = newA
    alg .Good.B = newB
    alg .Good.supA = πsupA
    alg .Good.supB = πsupB

  -- See Chain.agda for the Limit of Sets subsection of Section 3.5

  -- Section 3.5: limit of goodness algebras
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

    module limit-supA (a : AA) (p : Σ[ _ ∈ (AB a → pre.A) ] (AC a → pre.B)) (ϕ : Ix-A) where
      ≃ : Arg-supA limit-A.t limit-B.t a p ϕ ≃ limit-A.t ϕ (pre.supA a (p .fst) (p .snd))
      ≃ = ≃-trans
        (Σ-≃-CΣ (Σ-≃-CΣ (∀-≃-C∀ λ b → ≃-refl) λ _ → ∀-≃-C∀ λ c → ≃-refl) λ _ → P-≃-CP λ i → Ix-≃-A)
        (limit-A.st-≃-t ϕ (pre.supA a (p .fst) (p .snd)))
      f = ≃ .fst
      isEq = ≃ .snd

    module limit-supB (a : BA) (p : Σ[ _ ∈ (BB a → pre.A) ] (BC a → pre.B)) (ϕ : Ix-B limit-A.t) where
      ≃ : Arg-supB limit-A.t limit-B.t a p ϕ ≃ limit-B.t ϕ (pre.supB a (p .fst) (p .snd))
      ≃ = ≃-trans
        (Σ-≃-CΣ (Σ-≃-CΣ (∀-≃-C∀ λ b → ≃-refl) λ _ → ∀-≃-C∀ λ c → ≃-refl) λ _ → P-≃-CP λ i → Ix-≃-B)
        (limit-B.st-≃-t ϕ (pre.supB a (p .fst) (p .snd)))
      f = ≃ .fst
      isEq = ≃ .snd

    L : Good
    L .Good.A = limit-A.t
    L .Good.B = limit-B.t
    L .Good.supA = limit-supA.f
    L .Good.supB = limit-supB.f

    LN : Nice L
    LN .Nice.NsupA = limit-supA.isEq
    LN .Nice.NsupB = limit-supB.isEq

  -- Theorem 2
  T : Alg
  T = Good→Alg (limit.L O)
  T-elim : ∀ ℓ → simple-eliminators ℓ T
  T-elim ℓ = nice-goodness-to-simple-eliminators (limit.L O) (limit.LN O) ℓ
