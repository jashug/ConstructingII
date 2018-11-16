{-# OPTIONS --cubical --safe #-}

module ConTy where

open import Prelude
open import Chain

-- This is the example given in the introduction
-- note that we use U in the type of El
-- (U, El) is supposed to represent a universe; El gives a type in the context Γ , U Γ.

record Alg : Set₁ where
  field
    Con : Set
    Ty : Con → Set
    ε : Con
    join : (Γ : Con) → Ty Γ → Con
    U : (Γ : Con) → Ty Γ
    El : (Γ : Con) → Ty (join Γ (U Γ))

record Motives-Methods ℓ (T : Alg) : Set (lsuc ℓ) where
  open Alg T
  field
    PCon : Con → Set ℓ
    PTy : ∀ Γ → Ty Γ → Set ℓ
    Pε : PCon ε
    Pjoin : ∀ Γ → PCon Γ → ∀ A → PTy Γ A → PCon (join Γ A)
    PU : ∀ Γ → PCon Γ → PTy Γ (U Γ)
    PEl : ∀ Γ → PCon Γ → PTy (join Γ (U Γ)) (El Γ)

record Eliminators-Equations ℓ (T : Alg) (P : Motives-Methods ℓ T) : Set ℓ where
  open Alg T
  open Motives-Methods P
  field
    ECon : ∀ Γ → PCon Γ
    ETy : ∀ Γ A → PTy Γ A
    Eε : ECon ε ≡ Pε
    Ejoin : ∀ Γ A → ECon (join Γ A) ≡ Pjoin Γ (ECon Γ) A (ETy Γ A)
    EU : ∀ Γ → ETy Γ (U Γ) ≡ PU Γ (ECon Γ)
    EEl : ∀ Γ → ETy (join Γ (U Γ)) (El Γ) ≡ PEl Γ (ECon Γ)

simple-eliminators : ∀ ℓ → Alg → Set (lsuc ℓ)
simple-eliminators ℓ T = (P : Motives-Methods ℓ T) → Eliminators-Equations ℓ T P

module pre where
  data Con : Set
  data Ty : Set
  data Con where
    ε : Con
    join : Con → Ty → Con
  data Ty where
    U : Con → Ty
    El : Con → Ty

Ix-Con : Set
Ix-Con = ⊤
Ix-Ty : (goodCon : Ix-Con → pre.Con → Set) → Set
Ix-Ty goodCon = Σ[ a ∈ pre.Con ] goodCon ★ a
Arg-ε : Ix-Con → Set
Arg-ε ϕ = Σ[ _ ∈ ⊤ ] (★ ≡ ϕ)
Arg-join : (goodCon : Ix-Con → pre.Con → Set) (goodTy : Ix-Ty goodCon → pre.Ty → Set) →
           Σ[ _ ∈ pre.Con ] pre.Ty → Ix-Con → Set
Arg-join goodCon goodTy (a , b) ϕ = Σ[ p ∈ Σ[ good-a ∈ goodCon ★ a ] goodTy (a , good-a) b ] (★ ≡ ϕ)
Arg-U : (goodCon : Ix-Con → pre.Con → Set) → pre.Con → Ix-Ty goodCon → Set
Arg-U goodCon a ϕ = Σ[ good-a ∈ goodCon ★ a ] ((a , good-a) ≡ ϕ)
Arg-El : (goodCon : Ix-Con → pre.Con → Set) (goodTy : Ix-Ty goodCon → pre.Ty → Set)
         (good-join : ∀ p ϕ → Arg-join goodCon goodTy p ϕ → goodCon ϕ (pre.join (p .fst) (p .snd)))
         (good-U : ∀ a ϕ → Arg-U goodCon a ϕ → goodTy ϕ (pre.U a)) →
         pre.Con → Ix-Ty goodCon → Set
Arg-El goodCon goodTy good-join good-U a ϕ = Σ[ good-a ∈ goodCon ★ a ]
    ((pre.join a (pre.U a) , good-join (a , pre.U a) _ ((good-a , good-U a _ (good-a , refl)) , refl)) ≡ ϕ)

record Good : Set₁ where
  field
    Con : Ix-Con → pre.Con → Set
    Ty : Ix-Ty Con → pre.Ty → Set
    ε : ∀ ϕ → Arg-ε ϕ → Con ϕ pre.ε
    join : ∀ p ϕ → Arg-join Con Ty p ϕ → Con ϕ (pre.join (p .fst) (p .snd))
    U : ∀ a ϕ → Arg-U Con a ϕ → Ty ϕ (pre.U a)
    El : ∀ a ϕ → Arg-El Con Ty join U a ϕ → Ty ϕ (pre.El a)

Good→Alg : Good → Alg
Good→Alg G .Alg.Con = Σ[ a ∈ pre.Con ] G .Good.Con ★ a
Good→Alg G .Alg.Ty ϕ = Σ[ a ∈ pre.Ty ] G .Good.Ty ϕ a
Good→Alg G .Alg.ε = pre.ε , G .Good.ε _ (★ , refl)
Good→Alg G .Alg.join (pre-a , good-a) (pre-b , good-b) =
  pre.join pre-a pre-b , G .Good.join (pre-a , pre-b) ★ ((good-a , good-b) , refl)
Good→Alg G .Alg.U (pre-a , good-a) = pre.U pre-a , G .Good.U pre-a _ (good-a , refl)
Good→Alg G .Alg.El (pre-a , good-a) = pre.El pre-a , G .Good.El pre-a _ (good-a , refl)

O : Good
O .Good.Con ϕ _ = ⊤
O .Good.Ty ϕ _ = ⊤
O .Good.ε ϕ _ = ★
O .Good.join _ ϕ _ = ★
O .Good.U _ ϕ _ = ★
O .Good.El _ ϕ _ = ★

record Nice (G : Good) : Set where
  open Good G
  field
    Nε : ∀ ϕ → isEquiv _ _ (ε ϕ)
    Njoin : ∀ p ϕ → isEquiv _ _ (join p ϕ)
    NU : ∀ a ϕ → isEquiv _ _ (U a ϕ)
    NEl : ∀ a ϕ → isEquiv _ _ (El a ϕ)

nice-goodness-to-simple-eliminators : ∀ G → Nice G → ∀ ℓ → simple-eliminators ℓ (Good→Alg G)
nice-goodness-to-simple-eliminators G N ℓ P = record
  {
    ECon = λ Γ → ECon (Γ .fst) (Γ .snd);
    ETy = λ ϕ A → ETy (A .fst) ϕ (A .snd);
    Eε = equiv-pullback-J
      (λ ϕ → ε ϕ , Nε ϕ)
      (λ ϕ g → PCon (pre.ε , g))
      (λ { ★ → Pε }) .snd ★;
    Ejoin = λ { (a , good-a) (b , good-b) → equiv-pullback-J
      (λ ϕ → join (a , b) ϕ , Njoin (a , b) ϕ)
      (λ ϕ g → PCon (pre.join a b , g))
      (λ { (good-a , good-b) → Pjoin (a , good-a) (ECon a good-a)
                                     (b , good-b) (ETy b (a , good-a) good-b) }) .snd (good-a , good-b) };
    EU = λ { (a , good-a) → equiv-pullback-J
      (λ ϕ → U a ϕ , NU a ϕ)
      (λ ϕ g → PTy ϕ (pre.U a , g))
      (λ good-a → PU (a , good-a) (ECon a good-a)) .snd good-a };
    EEl = λ { (a , good-a) → equiv-pullback-J
      (λ ϕ → El a ϕ , NEl a ϕ)
      (λ ϕ g → PTy ϕ (pre.El a , g))
      (λ good-a → PEl (a , good-a) (ECon a good-a)) .snd good-a }
  }
  where
  open Good G
  open Nice N
  open Motives-Methods P

  ECon : (pre-a : pre.Con) → (good-a : Con ★ pre-a) → PCon (pre-a , good-a)
  ETy : (pre-a : pre.Ty) → (ϕ : Ix-Ty Con) → (good-a : Ty ϕ pre-a) → PTy ϕ (pre-a , good-a)
  ECon pre.ε =
    equiv-pullback-J
    (λ ϕ → ε ϕ , Nε ϕ)
    (λ ϕ g → PCon (pre.ε , g))
    (λ { ★ → Pε }) .fst ★
  ECon (pre.join a b) =
    equiv-pullback-J
    (λ ϕ → join (a , b) ϕ , Njoin (a , b) ϕ)
    (λ ϕ g → PCon (pre.join a b , g))
    (λ { (good-a , good-b) → Pjoin (a , good-a) (ECon a good-a)
                                   (b , good-b) (ETy b (a , good-a) good-b) }) .fst ★
  ETy (pre.U a) ϕ =
    equiv-pullback-J
    (λ ϕ → U a ϕ , NU a ϕ)
    (λ ϕ g → PTy ϕ (pre.U a , g))
    (λ good-a → PU (a , good-a) (ECon a good-a)) .fst ϕ
  ETy (pre.El a) ϕ =
    equiv-pullback-J
    (λ ϕ → El a ϕ , NEl a ϕ)
    (λ ϕ g → PTy ϕ (pre.El a , g))
    (λ good-a → PEl (a , good-a) (ECon a good-a)) .fst ϕ

module succ (G : Good) where
  module E where
    Con : (a : pre.Con) → (ϕ : Ix-Con) → Σ[ Y ∈ Set ] (Y → G .Good.Con ϕ a)
    Ty : (a : pre.Ty) → (ϕ : Ix-Ty (G .Good.Con)) → Σ[ Y ∈ Set ] (Y → G .Good.Ty ϕ a)
    Con pre.ε ϕ = Arg-ε ϕ , G .Good.ε ϕ
    Con (pre.join a b) ϕ = Arg-join (G .Good.Con) (G .Good.Ty) (a , b) ϕ , G .Good.join (a , b) ϕ
    Ty (pre.U a) ϕ = Arg-U (G .Good.Con) a ϕ , G .Good.U a ϕ
    Ty (pre.El a) ϕ = Arg-El (G .Good.Con) (G .Good.Ty) (G .Good.join) (G .Good.U) a ϕ , G .Good.El a ϕ

  πCon : Ix-Con → Ix-Con
  πCon ★ = ★
  newCon : Ix-Con → pre.Con → Set
  newCon ϕ a = E.Con a (πCon ϕ) .fst

  πTy : Ix-Ty newCon → Ix-Ty (G .Good.Con)
  πTy (pre-a , good-a) = pre-a , E.Con pre-a ★ .snd good-a
  newTy : Ix-Ty newCon → pre.Ty → Set
  newTy ϕ a = E.Ty a (πTy ϕ) .fst

  πε : ∀ ϕ → Arg-ε ϕ → Arg-ε (πCon ϕ)
  πε ϕ (★ , p) = ★ , cong πCon p

  πjoin : ∀ p ϕ → Arg-join newCon newTy p ϕ → Arg-join (G .Good.Con) (G .Good.Ty) p (πCon ϕ)
  πjoin (a , b) ϕ ((good-a , good-b) , p) = (E.Con a ★ .snd good-a , E.Ty b _ .snd good-b) , cong πCon p

  πU : ∀ a ϕ → Arg-U newCon a ϕ → Arg-U (G .Good.Con) a (πTy ϕ)
  πU a ϕ (good-a , p) = E.Con a ★ .snd good-a , cong πTy p

  πEl : ∀ a ϕ → Arg-El newCon newTy πjoin πU a ϕ → Arg-El (G .Good.Con) (G .Good.Ty) (G .Good.join) (G .Good.U) a (πTy ϕ)
  πEl a ϕ (good-a , p) = E.Con a ★ .snd good-a , cong πTy p

  alg : Good
  alg .Good.Con = newCon
  alg .Good.Ty = newTy
  alg .Good.ε = πε
  alg .Good.join = πjoin
  alg .Good.U = πU
  alg .Good.El = πEl

module limit (O : Good) where
  open chain-≃

  S^ : ℕ → Good
  S^ zero = O
  S^ (suc n) = succ.alg (S^ n)

  Ix-≃-Con : Ix-Con ≃ chain.t (λ n i → Ix-Con) (λ n → succ.πCon (S^ n))
  Ix-≃-Con = A-≃-CA

  module limit-Con (ϕ : Ix-Con) (a : pre.Con) = limit-sort
    (λ n → Ix-Con)
    (λ n → succ.πCon (S^ n))
    (λ n ϕ → S^ n .Good.Con ϕ a)
    (λ n ϕ → succ.E.Con (S^ n) a ϕ .fst)
    (λ n ϕ → succ.E.Con (S^ n) a ϕ .snd)
    (λ n ϕ y → y)
    (Ix-≃-Con .fst ϕ)

  Ix-≃-Ty : Ix-Ty limit-Con.t ≃ chain.t (λ n i → Ix-Ty (S^ n .Good.Con)) (λ n → succ.πTy (S^ n))
  Ix-≃-Ty = Σ-≃-CΣ A-≃-CA λ a → ≃-refl

  module limit-Ty (ϕ : Ix-Ty limit-Con.t) (a : pre.Ty) = limit-sort
    (λ n → Ix-Ty (S^ n .Good.Con))
    (λ n → succ.πTy (S^ n))
    (λ n ϕ → S^ n .Good.Ty ϕ a)
    (λ n ϕ → succ.E.Ty (S^ n) a ϕ .fst)
    (λ n ϕ → succ.E.Ty (S^ n) a ϕ .snd)
    (λ n ϕ y → y)
    (Ix-≃-Ty .fst ϕ)

  module limit-ε (ϕ : Ix-Con) where
    ≃ : Arg-ε ϕ ≃ limit-Con.t ϕ pre.ε
    ≃ = ≃-trans
      (Σ-≃-CΣ A-≃-CA (λ _ → P-≃-CP λ i → Ix-≃-Con))
      (limit-Con.st-≃-t ϕ pre.ε)
    f = ≃ .fst
    isEq = ≃ .snd

  module limit-join (p : Σ[ _ ∈ pre.Con ] pre.Ty) (ϕ : Ix-Con) where
    ≃ : Arg-join limit-Con.t limit-Ty.t p ϕ ≃ limit-Con.t ϕ (pre.join (p .fst) (p .snd))
    ≃ = ≃-trans
      (Σ-≃-CΣ (Σ-≃-CΣ ≃-refl λ _ → ≃-refl) λ _ → P-≃-CP λ i → Ix-≃-Con)
      (limit-Con.st-≃-t ϕ (pre.join (p .fst) (p .snd)))
    f = ≃ .fst
    isEq = ≃ .snd

  module limit-U (a : pre.Con) (ϕ : Ix-Ty limit-Con.t) where
    ≃ : Arg-U limit-Con.t a ϕ ≃ limit-Ty.t ϕ (pre.U a)
    ≃ = ≃-trans
      (Σ-≃-CΣ ≃-refl λ _ → P-≃-CP λ i → Ix-≃-Ty)
      (limit-Ty.st-≃-t ϕ (pre.U a))
    f = ≃ .fst
    isEq = ≃ .snd

  module limit-El (a : pre.Con) (ϕ : Ix-Ty limit-Con.t) where
    ≃ : Arg-El limit-Con.t limit-Ty.t limit-join.f limit-U.f a ϕ ≃ limit-Ty.t ϕ (pre.El a)
    ≃ = ≃-trans
      (Σ-≃-CΣ ≃-refl λ _ → P-≃-CP λ i → Ix-≃-Ty)
      (limit-Ty.st-≃-t ϕ (pre.El a))
    f = ≃ .fst
    isEq = ≃ .snd

  L : Good
  L .Good.Con = limit-Con.t
  L .Good.Ty = limit-Ty.t
  L .Good.ε = limit-ε.f
  L .Good.join = limit-join.f
  L .Good.U = limit-U.f
  L .Good.El = limit-El.f

  LN : Nice L
  LN .Nice.Nε = limit-ε.isEq
  LN .Nice.Njoin = limit-join.isEq
  LN .Nice.NU = limit-U.isEq
  LN .Nice.NEl = limit-El.isEq

T : Alg
T = Good→Alg (limit.L O)
T-elim : ∀ ℓ → simple-eliminators ℓ T
T-elim ℓ = nice-goodness-to-simple-eliminators (limit.L O) (limit.LN O) ℓ
