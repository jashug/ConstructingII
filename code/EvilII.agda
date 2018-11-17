{-# OPTIONS --cubical --safe #-}

module EvilII where

open import Prelude
open import Chain

-- This is close to the most convoluted inductive-inductive type I could come up with.
-- We have constructors in the premises of joinA and in the conclusion of Bι,
-- infinitary indices for B and C, constructor ηA in the sort C, which means that the constructors of A
-- cannot be brought into one block because joinA takes a C and produces an A.
-- To summarize, it's pretty ugly, but I claim we can define sensible simple eliminators and construct
-- types that satisfy them. The details aren't particularly important, because the construction
-- is a straightforward (though involved) transformation; no tricks are being used.

module _ (KA : Set) (g : KA → ℕ) where
  record Alg : Set₁ where
    field
      A : Set
      ηA : (n : ℕ) → A
      B : (KA → A) → A → Set
      BtoA : ∀ a → B (λ _ → a) a → A
      ηB : ∀ f a → B f a
      Bsuc : ∀ f a → B f a → B f a
      Bι : B (λ _ → ηA 3) (ηA 3)
      C : (fA : ℕ → A) → B (λ ka → fA (g ka)) (ηA 3) → Set
      joinA : (b1 : B (λ _ → ηA 3) (ηA 3)) (b2 : B (λ _ → BtoA (ηA 3) b1) (ηA 3)) → C (λ _ → BtoA (ηA 3) b1) b2 → A
      ηC : ∀ fA b → C fA b

  record Motives-Methods ℓ (T : Alg) : Set (lsuc ℓ) where
    open Alg T
    field
      PA : A → Set ℓ
      PηA : ∀ n → PA (ηA n)
      PB : ∀ f a → B f a → Set
      PBtoA : ∀ a → PA a → ∀ b → PB _ _ b → PA (BtoA a b)
      PηB : ∀ f → (∀ ka → PA (f ka)) → ∀ a → PA a → PB f a (ηB f a)
      PBsuc : ∀ f → (∀ ka → PA (f ka)) → ∀ a → PA a → ∀ b → PB f a b → PB f a (Bsuc f a b)
      PBι : PB _ _ Bι
      PC : ∀ fA b → C fA b → Set
      PjoinA : ∀ b1 → PB _ _ b1 → ∀ b2 → PB _ _ b2 → ∀ c → PC _ _ c → PA (joinA b1 b2 c)
      PηC : ∀ fA → (∀ n → PA (fA n)) → ∀ b → PB _ _ b → PC _ _ (ηC fA b)

  record Eliminators-Equations ℓ (T : Alg) (P : Motives-Methods ℓ T) : Set ℓ where
    open Alg T
    open Motives-Methods P
    field
      EA : ∀ a → PA a
      EηA : ∀ n → EA (ηA n) ≡ PηA n
      EB : ∀ f a b → PB f a b
      EBtoA : ∀ a b → EA (BtoA a b) ≡ PBtoA a (EA a) b (EB _ _ b)
      EηB : ∀ f a → EB _ _ (ηB f a) ≡ PηB f (λ ka → EA (f ka)) a (EA a)
      EBsuc : ∀ f a b → EB _ _ (Bsuc f a b) ≡ PBsuc f (λ ka → EA (f ka)) a (EA a) b (EB f a b)
      EBι : EB _ _ Bι ≡ PBι
      EC : ∀ fA b c → PC fA b c
      EjoinA : ∀ b1 b2 c → EA (joinA b1 b2 c) ≡ PjoinA b1 (EB _ _ b1) b2 (EB _ _ b2) c (EC _ _ c)
      EηC : ∀ fA b → EC _ _ (ηC fA b) ≡ PηC fA (λ n → EA (fA n)) b (EB _ _ b)

  simple-eliminators : ∀ ℓ → Alg → Set (lsuc ℓ)
  simple-eliminators ℓ T = (P : Motives-Methods ℓ T) → Eliminators-Equations ℓ T P

  module pre where
    -- this is a standard mutual inductive type
    data A : Set
    data B : Set
    data C : Set
    data A where
      ηA : ℕ → A
      BtoA : A → B → A
      joinA : B → B → C → A
    data B where
      ηB : (KA → A) → A → B
      Bsuc : (KA → A) → A → B → B
      Bι : B
    data C where
      ηC : (ℕ → A) → B → C

  Ix-A : Set
  Ix-A = ⊤
  Arg-ηA : ℕ → Ix-A → Set
  Arg-ηA n ϕ = Σ[ _ ∈ ⊤ ] (★ ≡ ϕ)
  Ix-B : (goodA : Ix-A → pre.A → Set) → Set
  Ix-B goodA = Σ[ _ ∈ (KA → Σ[ a ∈ pre.A ] goodA ★ a) ] (Σ[ a ∈ pre.A ] goodA ★ a)
  Arg-BtoA : (goodA : Ix-A → pre.A → Set) (goodB : Ix-B goodA → pre.B → Set) →
             Σ[ _ ∈ pre.A ] pre.B → Ix-A → Set
  Arg-BtoA goodA goodB (a , b) ϕ =
    Σ[ _ ∈ Σ[ good-a ∈ goodA ★ a ] goodB ((λ _ → a , good-a) , (a , good-a)) b ] (★ ≡ ϕ)
  Arg-ηB : (goodA : Ix-A → pre.A → Set) (goodB : Ix-B goodA → pre.B → Set) →
           Σ[ _ ∈ (KA → pre.A) ] pre.A → Ix-B goodA → Set
  Arg-ηB goodA goodB (f , a) ϕ = Σ[ p ∈ Σ[ _ ∈ (∀ ka → goodA ★ (f ka)) ] goodA ★ a ]
                                 (((λ ka → f ka , p .fst ka) , (a , p .snd)) ≡ ϕ)
  Arg-Bsuc : (goodA : Ix-A → pre.A → Set) (goodB : Ix-B goodA → pre.B → Set) →
             Σ[ _ ∈ Σ[ _ ∈ (KA → pre.A) ] pre.A ] pre.B → Ix-B goodA → Set
  Arg-Bsuc goodA goodB ((f , a) , b) ϕ =
    Σ[ p ∈ Σ[ p ∈ Σ[ _ ∈ (∀ ka → goodA ★ (f ka)) ] goodA ★ a ]
                  goodB ((λ ka → f ka , p .fst ka) , (a , p .snd)) b ]
    (((λ ka → f ka , p .fst .fst ka) , (a , p .fst .snd)) ≡ ϕ)
  Arg-Bι : (goodA : Ix-A → pre.A → Set) (good-ηA : ∀ n ϕ → Arg-ηA n ϕ → goodA ϕ (pre.ηA n)) →
           Ix-B goodA → Set
  Arg-Bι goodA good-ηA ϕ = Σ[ _ ∈ ⊤ ]
    (((λ _ → pre.ηA 3 , good-ηA 3 _ (★ , refl)) , (pre.ηA 3 , good-ηA 3 _ (★ , refl))) ≡ ϕ)
  Ix-C : (goodA : Ix-A → pre.A → Set) (good-ηA : ∀ n ϕ → Arg-ηA n ϕ → goodA ϕ (pre.ηA n))
         (goodB : Ix-B goodA → pre.B → Set) → Set
  Ix-C goodA good-ηA goodB =
    Σ[ fA ∈ (ℕ → Σ[ a ∈ pre.A ] goodA ★ a) ]
    (Σ[ b ∈ pre.B ] goodB ((λ ka → fA (g ka)) , (pre.ηA 3 , good-ηA 3 _ (★ , refl))) b)
  Arg-joinA : (goodA : Ix-A → pre.A → Set) (good-ηA : ∀ n ϕ → Arg-ηA n ϕ → goodA ϕ (pre.ηA n))
              (goodB : Ix-B goodA → pre.B → Set)
              (good-BtoA : ∀ p ϕ → Arg-BtoA goodA goodB p ϕ → goodA ϕ (pre.BtoA (p .fst) (p .snd)))
              (goodC : Ix-C goodA good-ηA goodB → pre.C → Set) →
              Σ[ _ ∈ Σ[ _ ∈ pre.B ] pre.B ] pre.C → Ix-A → Set
  Arg-joinA goodA good-ηA goodB good-BtoA goodC ((b1 , b2) , c) ϕ =
    Σ[ _ ∈ (Σ[ p ∈ Σ[ good-b1 ∈
      goodB (((λ _ → pre.ηA 3 , good-ηA 3 _ (★ , refl)) , (pre.ηA 3 , good-ηA 3 _ (★ , refl)))) b1 ]
      goodB (((λ ka → pre.BtoA (pre.ηA 3) _ ,
                      good-BtoA _ _ ((good-ηA 3 _ (★ , refl) , good-b1) , refl)) ,
              (pre.ηA 3 , good-ηA 3 _ (★ , refl)))) b2 ]
      goodC (((λ n → pre.BtoA (pre.ηA 3) _ ,
                      good-BtoA _ _ (((good-ηA 3 _ (★ , refl) , p .fst) , refl)))) ,
               (b2 , p .snd)) c) ]
    (★ ≡ ϕ)
  Arg-ηC : (goodA : Ix-A → pre.A → Set) (good-ηA : ∀ n ϕ → Arg-ηA n ϕ → goodA ϕ (pre.ηA n))
           (goodB : Ix-B goodA → pre.B → Set) →
           Σ[ _ ∈ (ℕ → pre.A) ] pre.B → Ix-C goodA good-ηA goodB → Set
  Arg-ηC goodA good-ηA goodB (fA , b) ϕ =
    Σ[ p ∈ Σ[ good-fA ∈ ((n : ℕ) → goodA ★ (fA n)) ]
           goodB (((λ ka → fA (g ka) , good-fA (g ka)) , (pre.ηA 3 , good-ηA 3 _ (★ , refl)))) b ]
    ((((λ n → fA n , p .fst n) , (b , p .snd))) ≡ ϕ)

  record Good : Set₁ where
    field
      A : Ix-A → pre.A → Set
      ηA : ∀ n ϕ → Arg-ηA n ϕ → A ϕ (pre.ηA n)
      B : Ix-B A → pre.B → Set
      BtoA : ∀ p ϕ → Arg-BtoA A B p ϕ → A ϕ (pre.BtoA (p .fst) (p .snd))
      ηB : ∀ p ϕ → Arg-ηB A B p ϕ → B ϕ (pre.ηB (p .fst) (p .snd))
      Bsuc : ∀ p ϕ → Arg-Bsuc A B p ϕ → B ϕ (pre.Bsuc (p .fst .fst) (p .fst .snd) (p .snd))
      Bι : ∀ ϕ → Arg-Bι A ηA ϕ → B ϕ pre.Bι
      C : Ix-C A ηA B → pre.C → Set
      joinA : ∀ p ϕ → Arg-joinA A ηA B BtoA C p ϕ → A ϕ (pre.joinA (p .fst .fst) (p .fst .snd) (p .snd))
      ηC : ∀ p ϕ → Arg-ηC A ηA B p ϕ → C ϕ (pre.ηC (p .fst) (p .snd))

  Good→Alg : Good → Alg
  Good→Alg G .Alg.A = Σ[ a ∈ pre.A ] G .Good.A ★ a
  Good→Alg G .Alg.ηA n = pre.ηA n , G .Good.ηA n _ (★ , refl)
  Good→Alg G .Alg.B fA a = Σ[ b ∈ pre.B ] G .Good.B (fA , a) b
  Good→Alg G .Alg.BtoA a b = pre.BtoA (a .fst) (b .fst) , G .Good.BtoA _ _ ((a .snd , b .snd) , refl)
  Good→Alg G .Alg.ηB fA a = pre.ηB (λ ka → fA ka .fst) (a .fst) , G .Good.ηB _ _ (((λ ka → fA ka .snd) , a .snd) , refl)
  Good→Alg G .Alg.Bsuc fA a b =
    pre.Bsuc (λ ka → fA ka .fst) (a .fst) (b .fst) ,
    G .Good.Bsuc _ _ ((((λ ka → fA ka .snd) , a .snd) , b .snd) , refl)
  Good→Alg G .Alg.Bι = pre.Bι , G .Good.Bι _ (★ , refl)
  Good→Alg G .Alg.C fA b = Σ[ c ∈ pre.C ] G .Good.C (fA , b) c
  Good→Alg G .Alg.joinA b1 b2 c = 
    pre.joinA (b1 .fst) (b2 .fst) (c .fst) ,
    G .Good.joinA _ _ (((b1 .snd , b2 .snd) , c .snd) , refl)
  Good→Alg G .Alg.ηC fA b = pre.ηC (λ n → fA n .fst) (b .fst) , G .Good.ηC _ _ (((λ n → fA n .snd) , b .snd) , refl)

  O : Good
  O .Good.A _ _ = ⊤
  O .Good.ηA _ _ _ = ★
  O .Good.B _ _ = ⊤
  O .Good.BtoA _ _ _ = ★
  O .Good.ηB _ _ _ = ★
  O .Good.Bsuc _ _ _ = ★
  O .Good.Bι _ _ = ★
  O .Good.C _ _ = ⊤
  O .Good.joinA _ _ _ = ★
  O .Good.ηC _ _ _ = ★

  record Nice (G : Good) : Set where
    open Good G
    field
      NηA : ∀ n ϕ → isEquiv _ _ (ηA n ϕ)
      NBtoA : ∀ p ϕ → isEquiv _ _ (BtoA p ϕ)
      NηB : ∀ p ϕ → isEquiv _ _ (ηB p ϕ)
      NBsuc : ∀ p ϕ → isEquiv _ _ (Bsuc p ϕ)
      NBι : ∀ ϕ → isEquiv _ _ (Bι ϕ)
      NjoinA : ∀ p ϕ → isEquiv _ _ (joinA p ϕ)
      NηC : ∀ p ϕ → isEquiv _ _ (ηC p ϕ)

  nice-goodness-to-simple-eliminators : ∀ G → Nice G → ∀ ℓ → simple-eliminators ℓ (Good→Alg G)
  nice-goodness-to-simple-eliminators G N ℓ P = record
    {
      EA = λ a → EA (a .fst) ★ (a .snd);
      EηA = λ n → equiv-pullback-J
        (λ ϕ → ηA n ϕ , NηA n ϕ)
        (λ ϕ g → PA (pre.ηA n , g))
        (λ _ → PηA n)
        .snd ★;
      EB = λ fA a b → EB (b .fst) (fA , a) (b .snd);
      EBtoA = λ { (a , good-a) (b , good-b) → equiv-pullback-J
        (λ ϕ → BtoA (a , b) ϕ , NBtoA (a , b) ϕ)
        (λ ϕ g → PA (pre.BtoA a b , g))
        (λ { (good-a , good-b) → PBtoA (a , good-a) (EA a _ good-a) (b , good-b) (EB b _ good-b) })
        .snd (good-a , good-b) };
      EηB = λ { fA (a , good-a) → equiv-pullback-J
        (λ ϕ → ηB ((λ ka → fA ka .fst) , a) ϕ , NηB ((λ ka → fA ka .fst) , a) ϕ)
        (λ ϕ g → PB (ϕ .fst) (ϕ .snd) (pre.ηB (λ ka → fA ka .fst) a , g))
        (λ { (good-fA , good-a) → PηB
               (λ ka → fA ka .fst , good-fA ka) (λ ka → EA (fA ka .fst) _ (good-fA ka))
               (a , good-a) (EA a _ good-a) })
        .snd ((λ ka → fA ka .snd) , good-a) };
      EBsuc = λ { fA (a , good-a) (b , good-b) → equiv-pullback-J
        (λ ϕ → Bsuc ((fst ∘ fA , a) , b) ϕ , NBsuc ((fst ∘ fA , a) , b) ϕ)
        (λ ϕ g → PB (ϕ .fst) (ϕ .snd) (pre.Bsuc (fst ∘ fA) a b , g))
        (λ { ((good-fA , good-a) , good-b) → PBsuc
                 (λ ka → fA ka .fst , good-fA ka) (λ ka → EA (fA ka .fst) _ (good-fA ka))
                 (a , good-a) (EA a _ good-a)
                 (b , good-b) (EB b _ good-b) })
        .snd (((λ ka → fA ka .snd) , good-a) , good-b) };
      EBι = equiv-pullback-J
        (λ ϕ → Bι ϕ , NBι ϕ)
        (λ ϕ g → PB (ϕ .fst) (ϕ .snd) (pre.Bι , g))
        (λ _ → PBι)
        .snd ★;
      EC = λ fA b c → EC (c .fst) (fA , b) (c .snd);
      EjoinA = λ { (b1 , b1-good) (b2 , b2-good) (c , c-good) → equiv-pullback-J
        (λ ϕ → joinA ((b1 , b2) , c) ϕ , NjoinA ((b1 , b2) , c) ϕ)
        (λ ϕ g → PA (pre.joinA b1 b2 c , g))
        (λ { ((good-b1 , good-b2) , good-c) → PjoinA
                (b1 , good-b1) (EB b1 _ good-b1)
                (b2 , good-b2) (EB b2 _ good-b2)
                (c , good-c) (EC c _ good-c) })
        .snd ((b1-good , b2-good) , c-good)};
      EηC = λ { fA (b , b-good) → equiv-pullback-J
        (λ ϕ → ηC (fst ∘ fA , b) ϕ , NηC (fst ∘ fA , b) ϕ)
        (λ ϕ g → PC (ϕ .fst) (ϕ .snd) (pre.ηC (fst ∘ fA) b , g))
        (λ { (good-fA , good-b) → PηC
               (λ n → fA n .fst , good-fA n) (λ n → EA (fA n .fst) _ (good-fA n))
               (b , good-b) (EB b _ good-b) })
        .snd (snd ∘ fA , b-good) }
    }
    where
    open Good G
    open Nice N
    open Motives-Methods P

    EA : (pre-a : pre.A) → ∀ ϕ → (good-a : A ϕ pre-a) → PA (pre-a , good-a)
    EB : (pre-b : pre.B) → ∀ ϕ → (good-b : B ϕ pre-b) → PB (ϕ .fst) (ϕ .snd) (pre-b , good-b)
    EC : (pre-c : pre.C) → ∀ ϕ → (good-c : C ϕ pre-c) → PC (ϕ .fst) (ϕ .snd) (pre-c , good-c)
    EA (pre.ηA n) ϕ = 
      equiv-pullback-J
      (λ ϕ → ηA n ϕ , NηA n ϕ)
      (λ ϕ g → PA (pre.ηA n , g))
      (λ _ → PηA n)
      .fst ϕ
    EA (pre.BtoA a b) ϕ = 
      equiv-pullback-J
      (λ ϕ → BtoA (a , b) ϕ , NBtoA (a , b) ϕ)
      (λ ϕ g → PA (pre.BtoA a b , g))
      (λ { (good-a , good-b) → PBtoA (a , good-a) (EA a _ good-a) (b , good-b) (EB b _ good-b) })
      .fst ϕ
    EA (pre.joinA b1 b2 c) ϕ = 
      equiv-pullback-J
      (λ ϕ → joinA ((b1 , b2) , c) ϕ , NjoinA ((b1 , b2) , c) ϕ)
      (λ ϕ g → PA (pre.joinA b1 b2 c , g))
      (λ { ((good-b1 , good-b2) , good-c) → PjoinA
              (b1 , good-b1) (EB b1 _ good-b1)
              (b2 , good-b2) (EB b2 _ good-b2)
              (c , good-c) (EC c _ good-c) })
      .fst ϕ
    EB (pre.ηB fA a) ϕ = 
      equiv-pullback-J
      (λ ϕ → ηB (fA , a) ϕ , NηB (fA , a) ϕ)
      (λ ϕ g → PB (ϕ .fst) (ϕ .snd) (pre.ηB fA a , g))
      (λ { (good-fA , good-a) → PηB
             (λ ka → fA ka , good-fA ka) (λ ka → EA (fA ka) _ (good-fA ka))
             (a , good-a) (EA a _ good-a) })
      .fst ϕ
    EB (pre.Bsuc fA a b) ϕ = 
      equiv-pullback-J
      (λ ϕ → Bsuc ((fA , a) , b) ϕ , NBsuc ((fA , a) , b) ϕ)
      (λ ϕ g → PB (ϕ .fst) (ϕ .snd) (pre.Bsuc fA a b , g))
      (λ { ((good-fA , good-a) , good-b) → PBsuc
               (λ ka → fA ka , good-fA ka) (λ ka → EA (fA ka) _ (good-fA ka))
               (a , good-a) (EA a _ good-a)
               (b , good-b) (EB b _ good-b) })
      .fst ϕ
    EB pre.Bι ϕ = 
      equiv-pullback-J
      (λ ϕ → Bι ϕ , NBι ϕ)
      (λ ϕ g → PB (ϕ .fst) (ϕ .snd) (pre.Bι , g))
      (λ _ → PBι)
      .fst ϕ
    EC (pre.ηC fA b) ϕ = 
      equiv-pullback-J
      (λ ϕ → ηC (fA , b) ϕ , NηC (fA , b) ϕ)
      (λ ϕ g → PC (ϕ .fst) (ϕ .snd) (pre.ηC fA b , g))
      (λ { (good-fA , good-b) → PηC
             (λ n → fA n , good-fA n) (λ n → EA (fA n) _ (good-fA n))
             (b , good-b) (EB b _ good-b) })
      .fst ϕ

  module succ (G : Good) where
    module E where
      A : (a : pre.A) → (ϕ : Ix-A) → Σ[ Y ∈ Set ] (Y → G .Good.A ϕ a)
      B : (b : pre.B) → (ϕ : Ix-B (G .Good.A)) → Σ[ Y ∈ Set ] (Y → G .Good.B ϕ b)
      C : (c : pre.C) → (ϕ : Ix-C (G .Good.A) (G .Good.ηA) (G .Good.B)) → Σ[ Y ∈ Set ] (Y → G .Good.C ϕ c)
      A (pre.ηA n) ϕ = Arg-ηA n ϕ , G .Good.ηA n ϕ
      A (pre.BtoA a b) ϕ = Arg-BtoA (G .Good.A) (G .Good.B) (a , b) ϕ , G .Good.BtoA (a , b) ϕ
      A (pre.joinA b1 b2 c) ϕ =
        Arg-joinA (G .Good.A) (G .Good.ηA) (G .Good.B) (G .Good.BtoA) (G .Good.C) ((b1 , b2) , c) ϕ ,
        G .Good.joinA ((b1 , b2) , c) ϕ
      B (pre.ηB fA a) ϕ = Arg-ηB (G .Good.A) (G .Good.B) (fA , a) ϕ , G .Good.ηB (fA , a) ϕ
      B (pre.Bsuc fA a b) ϕ = Arg-Bsuc (G .Good.A) (G .Good.B) ((fA , a) , b) ϕ , G .Good.Bsuc ((fA , a) , b) ϕ
      B pre.Bι ϕ = Arg-Bι (G .Good.A) (G .Good.ηA) ϕ , G .Good.Bι ϕ
      C (pre.ηC fA b) ϕ = Arg-ηC (G .Good.A) (G .Good.ηA) (G .Good.B) (fA , b) ϕ , G .Good.ηC (fA , b) ϕ

    πA : Ix-A → Ix-A
    πA ★ = ★
    newA : Ix-A → pre.A → Set
    newA ϕ a = E.A a (πA ϕ) .fst

    πηA : ∀ n ϕ → Arg-ηA n ϕ → Arg-ηA n (πA ϕ)
    πηA n ϕ (★ , p) = ★ , cong πA p

    πB : Ix-B newA → Ix-B (G .Good.A)
    πB (fA , a) = (λ ka → fA ka .fst , E.A _ _ .snd (fA ka .snd)) , (a .fst , E.A _ _ .snd (a .snd))
    newB : Ix-B newA → pre.B → Set
    newB ϕ b = E.B b (πB ϕ) .fst

    πBtoA : ∀ p ϕ → Arg-BtoA newA newB p ϕ → Arg-BtoA (G .Good.A) (G .Good.B) p (πA ϕ)
    πBtoA (a , b) ϕ ((good-a , good-b) , p) = (E.A _ _ .snd good-a , E.B _ _ .snd good-b) , cong πA p

    πηB : ∀ p ϕ → Arg-ηB newA newB p ϕ → Arg-ηB (G .Good.A) (G .Good.B) p (πB ϕ)
    πηB (fA , a) ϕ ((good-fA , good-a) , p) = ((λ ka → E.A _ _ .snd (good-fA ka)) , E.A _ _ .snd good-a) , cong πB p

    πBsuc : ∀ p ϕ → Arg-Bsuc newA newB p ϕ → Arg-Bsuc (G .Good.A) (G .Good.B) p (πB ϕ)
    πBsuc ((fA , a) , b) ϕ (((good-fA , good-a) , good-b) , p) =
      (((λ ka → E.A _ _ .snd (good-fA ka)) , E.A _ _ .snd good-a) , E.B _ _ .snd good-b) , cong πB p

    πBι : ∀ ϕ → Arg-Bι newA πηA ϕ → Arg-Bι (G .Good.A) (G .Good.ηA) (πB ϕ)
    πBι ϕ (★ , p) = ★ , cong πB p

    πC : Ix-C newA πηA newB → Ix-C (G .Good.A) (G .Good.ηA) (G .Good.B)
    πC (fA , b) = (λ n → fA n .fst , E.A _ _ .snd (fA n .snd)) , (b .fst , E.B _ _ .snd (b .snd))
    newC : Ix-C newA πηA newB → pre.C → Set
    newC ϕ c = E.C c (πC ϕ) .fst

    πjoinA : ∀ p ϕ → Arg-joinA newA πηA newB πBtoA newC p ϕ →
                     Arg-joinA (G .Good.A) (G .Good.ηA) (G .Good.B) (G .Good.BtoA) (G .Good.C) p (πA ϕ)
    πjoinA ((b1 , b2) , c) ϕ (((good-b1 , good-b2) , good-c) , p) = 
      ((E.B _ _ .snd good-b1 , E.B _ _ .snd good-b2) , E.C _ _ .snd good-c) , cong πA p

    πηC : ∀ p ϕ → Arg-ηC newA πηA newB p ϕ → Arg-ηC (G .Good.A) (G .Good.ηA) (G .Good.B) p (πC ϕ)
    πηC (fA , b) ϕ ((good-fA , good-b) , p) = ((λ n → E.A _ _ .snd (good-fA n)) , E.B _ _ .snd good-b) , cong πC p

    alg : Good
    alg .Good.A = newA
    alg .Good.ηA = πηA
    alg .Good.B = newB
    alg .Good.BtoA = πBtoA
    alg .Good.ηB = πηB
    alg .Good.Bsuc = πBsuc
    alg .Good.Bι = πBι
    alg .Good.C = newC
    alg .Good.joinA = πjoinA
    alg .Good.ηC = πηC

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

    module limit-ηA (n : ℕ) (ϕ : Ix-A) where
      ≃ : Arg-ηA n ϕ ≃ limit-A.t ϕ (pre.ηA n)
      ≃ = ≃-trans
        (Σ-≃-CΣ A-≃-CA λ _ → P-≃-CP λ i → Ix-≃-A)
        (limit-A.st-≃-t ϕ (pre.ηA n))
      f = ≃ .fst
      isEq = ≃ .snd

    Ix-≃-B : Ix-B limit-A.t ≃ chain.t (λ n i → Ix-B (S^ n .Good.A)) (λ n → succ.πB (S^ n))
    Ix-≃-B = Σ-≃-CΣ (∀-≃-C∀ λ _ → Σ-≃-CΣ A-≃-CA λ _ → ≃-refl) λ _ → Σ-≃-CΣ A-≃-CA λ _ → ≃-refl

    module limit-B (ϕ : Ix-B limit-A.t) (b : pre.B) = limit-sort
      (λ n → Ix-B (S^ n .Good.A))
      (λ n → succ.πB (S^ n))
      (λ n ϕ → S^ n .Good.B ϕ b)
      (λ n ϕ → succ.E.B (S^ n) b ϕ .fst)
      (λ n ϕ → succ.E.B (S^ n) b ϕ .snd)
      (λ n ϕ y → y)
      (Ix-≃-B .fst ϕ)

    module limit-BtoA (p : Σ[ _ ∈ pre.A ] pre.B) (ϕ : Ix-A) where
      ≃ : Arg-BtoA limit-A.t limit-B.t p ϕ ≃ limit-A.t ϕ (pre.BtoA (p .fst) (p .snd))
      ≃ = ≃-trans
        (Σ-≃-CΣ (Σ-≃-CΣ ≃-refl λ _ → ≃-refl) λ _ → P-≃-CP λ i → Ix-≃-A)
        (limit-A.st-≃-t ϕ (pre.BtoA (p .fst) (p .snd)))
      f = ≃ .fst
      isEq = ≃ .snd

    module limit-ηB (p : Σ[ _ ∈ (KA → pre.A) ] pre.A) (ϕ : Ix-B limit-A.t) where
      ≃ : Arg-ηB limit-A.t limit-B.t p ϕ ≃ limit-B.t ϕ (pre.ηB (p .fst) (p .snd))
      ≃ = ≃-trans
        (Σ-≃-CΣ (Σ-≃-CΣ (∀-≃-C∀ λ _ → ≃-refl) λ _ → ≃-refl) λ _ → P-≃-CP λ i → Ix-≃-B)
        (limit-B.st-≃-t ϕ (pre.ηB (p .fst) (p .snd)))
      f = ≃ .fst
      isEq = ≃ .snd

    module limit-Bsuc (p : Σ[ _ ∈ Σ[ _ ∈ (KA → pre.A) ] pre.A ] pre.B) (ϕ : Ix-B limit-A.t) where
      ≃ : Arg-Bsuc limit-A.t limit-B.t p ϕ ≃ limit-B.t ϕ (pre.Bsuc (p .fst .fst) (p .fst .snd) (p .snd))
      ≃ = ≃-trans
        (Σ-≃-CΣ (Σ-≃-CΣ (Σ-≃-CΣ (∀-≃-C∀ λ _ → ≃-refl) λ _ → ≃-refl) λ _ → ≃-refl) λ _ → P-≃-CP λ i → Ix-≃-B)
        (limit-B.st-≃-t ϕ (pre.Bsuc (p .fst .fst) (p .fst .snd) (p .snd)))
      f = ≃ .fst
      isEq = ≃ .snd

    module limit-Bι (ϕ : Ix-B limit-A.t) where
      ≃ : Arg-Bι limit-A.t limit-ηA.f ϕ ≃ limit-B.t ϕ pre.Bι
      ≃ = ≃-trans
        (Σ-≃-CΣ A-≃-CA λ _ → P-≃-CP λ i → Ix-≃-B)
        (limit-B.st-≃-t ϕ pre.Bι)
      f = ≃ .fst
      isEq = ≃ .snd

    Ix-≃-C : Ix-C limit-A.t limit-ηA.f limit-B.t ≃
             chain.t (λ n i → Ix-C (S^ n .Good.A) (S^ n .Good.ηA) (S^ n .Good.B)) (λ n → succ.πC (S^ n))
    Ix-≃-C = Σ-≃-CΣ (∀-≃-C∀ λ _ → Σ-≃-CΣ A-≃-CA λ _ → ≃-refl) λ _ → Σ-≃-CΣ A-≃-CA λ _ → ≃-refl

    module limit-C (ϕ : Ix-C limit-A.t limit-ηA.f limit-B.t) (c : pre.C) = limit-sort
      (λ n → Ix-C (S^ n .Good.A) (S^ n .Good.ηA) (S^ n .Good.B))
      (λ n → succ.πC (S^ n))
      (λ n ϕ → S^ n .Good.C ϕ c)
      (λ n ϕ → succ.E.C (S^ n) c ϕ .fst)
      (λ n ϕ → succ.E.C (S^ n) c ϕ .snd)
      (λ n ϕ y → y)
      (Ix-≃-C .fst ϕ)

    module limit-joinA (p : Σ[ _ ∈ Σ[ _ ∈ pre.B ] pre.B ] pre.C) (ϕ : Ix-A) where
      ≃ : Arg-joinA limit-A.t limit-ηA.f limit-B.t limit-BtoA.f limit-C.t p ϕ ≃
          limit-A.t ϕ (pre.joinA (p .fst .fst) (p .fst .snd) (p .snd))
      ≃ = ≃-trans
        (Σ-≃-CΣ (Σ-≃-CΣ (Σ-≃-CΣ ≃-refl λ _ → ≃-refl) λ _ → ≃-refl) λ _ → P-≃-CP λ i → Ix-≃-A)
        (limit-A.st-≃-t ϕ (pre.joinA (p .fst .fst) (p .fst .snd) (p .snd)))
      f = ≃ .fst
      isEq = ≃ .snd

    module limit-ηC (p : Σ[ _ ∈ (ℕ → pre.A) ] pre.B) (ϕ : Ix-C limit-A.t limit-ηA.f limit-B.t) where
      ≃ : Arg-ηC limit-A.t limit-ηA.f limit-B.t p ϕ ≃ limit-C.t ϕ (pre.ηC (p .fst) (p .snd))
      ≃ = ≃-trans
        (Σ-≃-CΣ (Σ-≃-CΣ (∀-≃-C∀ λ _ → ≃-refl) λ _ → ≃-refl) λ _ → P-≃-CP λ i → Ix-≃-C)
        (limit-C.st-≃-t ϕ (pre.ηC (p .fst) (p .snd)))
      f = ≃ .fst
      isEq = ≃ .snd

    L : Good
    L .Good.A = limit-A.t
    L .Good.ηA = limit-ηA.f
    L .Good.B = limit-B.t
    L .Good.BtoA = limit-BtoA.f
    L .Good.ηB = limit-ηB.f
    L .Good.Bsuc = limit-Bsuc.f
    L .Good.Bι = limit-Bι.f
    L .Good.C = limit-C.t
    L .Good.joinA = limit-joinA.f
    L .Good.ηC = limit-ηC.f

    LN : Nice L
    LN .Nice.NηA = limit-ηA.isEq
    LN .Nice.NBtoA = limit-BtoA.isEq
    LN .Nice.NηB = limit-ηB.isEq
    LN .Nice.NBsuc = limit-Bsuc.isEq
    LN .Nice.NBι = limit-Bι.isEq
    LN .Nice.NjoinA = limit-joinA.isEq
    LN .Nice.NηC = limit-ηC.isEq

  T : Alg
  T = Good→Alg (limit.L O)
  T-elim : ∀ ℓ → simple-eliminators ℓ T
  T-elim ℓ = nice-goodness-to-simple-eliminators (limit.L O) (limit.LN O) ℓ
