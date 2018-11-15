{-# OPTIONS --cubical --safe #-}
module Chain where

-- contains lemmas about chains

open import Prelude

module chain where
  record t {ℓ} (X : ℕ → I → Set ℓ) (pi : ∀ n → X (suc n) i0 → X n i1) : Set ℓ where
    constructor cone
    field
      {f} : ∀ n → X n i0
      p : ∀ n → PathP (X n) (f n) (pi n (f (suc n)))
open chain using (cone)

-- proofs that chains commute with other type formers
module chain-≃ where
  ∀-≃-C∀ : ∀ {ℓC ℓX ℓY} {C : Set ℓC} →
    {X : C → ℕ → I → Set ℓX} → {pi : ∀ c n → X c (suc n) i0 → X c n i1} →
    {Y : C → Set ℓY} → ((c : C) → Y c ≃ chain.t (X c) (pi c)) →
    (∀ c → Y c) ≃ chain.t (λ n i → ∀ c → X c n i) (λ n x (c : C) → pi c n (x c))
  ∀-≃-C∀ eqs .fst y = cone λ n j c → eqs c .fst (y c) .chain.t.p n j
  ∀-≃-C∀ eqs .snd (cone xp) .fst .fst c = eqs c .snd (cone λ n j → xp n j c) .fst .fst
  ∀-≃-C∀ eqs .snd (cone xp) .fst .snd i = cone λ n j c → eqs c .snd (cone λ n j → xp n j c) .fst .snd i .chain.t.p n j
  ∀-≃-C∀ eqs .snd (cone xp) .snd (y , sec) =
    let cfib : ∀ c → fiber (eqs c .fst) (cone λ n j → xp n j c)
        cfib c = y c , λ i → cone λ n j → sec i .chain.t.p n j c
        cfib-path : ∀ c → eqs c .snd (cone λ n j → xp n j c) .fst ≡ cfib c
        cfib-path c = eqs c .snd (cone λ n j → xp n j c) .snd (cfib c)
    in λ k → (λ c → cfib-path c k .fst) , λ i → cone λ n j c → cfib-path c k .snd i .chain.t.p n j

  ΣC-≃-CΣ : ∀ {ℓX ℓY} {X : ℕ → I → Set ℓX} → {piX : ∀ n → X (suc n) i0 → X n i1} →
         {Y : ∀ n i → X n i → Set ℓY} → {piY : ∀ n x → Y (suc n) i0 x → Y n i1 (piX n x)} →
         Σ (chain.t X piX) (λ x → chain.t (λ n i → Y n i (x .chain.t.p n i)) (λ n → piY n (x .chain.t.f (suc n)))) ≃
         chain.t (λ n i → Σ (X n i) (Y n i)) (λ n x → piX n (x .fst) , piY n (x .fst) (x .snd))
  ΣC-≃-CΣ .fst (x , y) = cone λ n j → x .chain.t.p n j , y .chain.t.p n j
  ΣC-≃-CΣ .snd (cone xp) .fst .fst = (cone λ n j → xp n j .fst) , (cone λ n j → xp n j .snd)
  ΣC-≃-CΣ .snd (cone xp) .fst .snd = refl
  ΣC-≃-CΣ .snd (cone xp) .snd ((x , y) , sec) k = ((cone λ n j → sec k .chain.t.p n j .fst) , (cone λ n j → sec k .chain.t.p n j .snd)) ,
    λ i → sec (i ∧ k)

  Σ-≃-CΣ : ∀ {ℓX ℓY} {X : ℕ → I → Set ℓX} → {piX : ∀ n → X (suc n) i0 → X n i1} →
         {Y : ∀ n i → X n i → Set ℓY} → {piY : ∀ n x → Y (suc n) i0 x → Y n i1 (piX n x)} →
         ∀ {ℓA ℓB} → {A : Set ℓA} → {B : A → Set ℓB} →
         (eqA : A ≃ chain.t X piX) →
         (eqB : (a : A) → B a ≃ chain.t (λ n i → Y n i (eqA .fst a .chain.t.p n i)) (λ n → piY n _)) →
         Σ A B ≃ chain.t (λ n i → Σ (X n i) (Y n i)) (λ n x → piX n (x .fst) , piY n (x .fst) (x .snd))
  Σ-≃-CΣ {piX = piX} {piY = piY} eqA eqB = ≃-trans (equiv-Σ eqA eqB) (ΣC-≃-CΣ {piX = piX} {piY = piY})

  PC-≃-CP : ∀ {ℓX} {X : I → ℕ → I → Set ℓX} → {pi : ∀ k n → X k (suc n) i0 → X k n i1} → ∀ {x1 x2} →
             PathP (λ k → chain.t (X k) (pi k)) x1 x2 ≃
             chain.t (λ n i → PathP (λ k → X k n i) (x1 .chain.t.p n i) (x2 .chain.t.p n i)) (λ n p k → pi k n (p k))
  PC-≃-CP .fst p = cone λ n j k → p k .chain.t.p n j
  PC-≃-CP .snd (cone pp) .fst .fst i = cone λ n j → pp n j i
  PC-≃-CP .snd (cone pp) .fst .snd = refl
  PC-≃-CP .snd (cone pp) .snd (p , sec) = λ k → (λ i → cone λ n j → sec k .chain.t.p n j i) , λ i → sec (i ∧ k)

  P-≃-CP : ∀ {ℓX} {X : I → ℕ → I → Set ℓX} → {pi : ∀ k n → X k (suc n) i0 → X k n i1} →
           ∀ {ℓA} {A : I → Set ℓA} → (eqs : (i : I) → A i ≃ chain.t (X i) (pi i)) →
           ∀ {x1 x2} →
           PathP A x1 x2 ≃
           chain.t (λ n i → PathP (λ k → X k n i) (eqs i0 .fst x1 .chain.t.p n i) (eqs i1 .fst x2 .chain.t.p n i)) (λ n p k → pi k n (p k))
  P-≃-CP {X = X} {pi = pi} eqs {x1 = x1} {x2 = x2} = ≃-trans (path-equivs.P≃ eqs x1 x2) (PC-≃-CP {X = X} {pi})

  A-≃-CA : ∀ {ℓ} {A : Set ℓ} → A ≃ chain.t (λ _ _ → A) (λ n a → a)
  A-≃-CA {A = A} .fst a = cone λ n i → a
  A-≃-CA {A = A} .snd (cone {xf} xp) =
    (xf zero , λ k → cone λ n j → eq n j k) , λ fib i → fib .snd i .chain.t.f zero , λ k → cone λ n j → fib-all-a fib n j k i
    where
      eq : ∀ n (j : I) → xp n j ≡ xf zero
      eq zero j = λ i → xp zero (j ∧ ~ i)
      eq (suc n) j = coep (λ k → xp (suc n) k ≡ xf zero) (eq n i1) j

      module _ (fib : fiber {B = chain.t (λ _ _ → A) (λ n a → a)}  (λ a → cone λ n j → a) (cone xp)) where
        fib-all-a : ∀ n j → PathP (λ k → eq n j k ≡ fib .snd k .chain.t.p n j) refl λ i → fib .snd i .chain.t.f zero
        fib-all-a zero j = λ k i → primComp (λ _ → A) (i ∨ ~ i ∨ k ∨ ~ k)
          (λ { l (i = i0) → xp 0 (j ∧ ~ k) ; l (k = i1) → fib .snd i .chain.t.f zero ;
               l (k = i0) → fib .snd (i ∧ ~ l) .chain.t.p zero j ; l (i = i1) → fib .snd (k ∨ ~ l) .chain.t.p zero j })
          (fib .snd i .chain.t.p zero (j ∧ ~ k))
        fib-all-a (suc n) j = coep
          (λ j → PathP (λ k → eq (suc n) j k ≡ fib .snd k .chain.t.p (suc n) j) refl λ i → fib .snd i .chain.t.f zero)
          (fib-all-a n i1) j

-- Lemma 7
module limit-sort {ℓX ℓY0 ℓY1}
  (X : ℕ → Set ℓX) (piX : ∀ n → X (suc n) → X n)
  (Y0 : ∀ n → X n → Set ℓY0) (Y1 : ∀ n → X n → Set ℓY1)
  (fwd : ∀ n x → Y1 n x → Y0 n x)
  (rev : ∀ n x → Y0 (suc n) x → Y1 n (piX n x))
  (x : chain.t (λ n _ → X n) piX)
  where

  t : Set ℓY0
  t = chain.t (λ n i → Y0 n (x .chain.t.p n i)) (λ n y → fwd n _ (rev n _ y))

  st : Set ℓY1
  st = chain.t (λ n i → Y1 n (x .chain.t.p n i)) (λ n y → rev n _ (fwd (suc n) _ y))

  f : st → t
  f y = cone λ n i → fwd n (x .chain.t.p n i) (y .chain.t.p n i)

  abstract
    f-isEquiv : isEquiv st t f
    f-isEquiv = make-equiv-approx.f-isEquiv
      {X = chain.t (λ n _ → X n) piX}
      {A = λ x → chain.t (λ n i → Y1 n (x .chain.t.p n i)) (λ n → rev n _ ∘ fwd (suc n) _)}
      {B = λ x → chain.t (λ n i → Y0 n (x .chain.t.p n i)) (λ n → fwd n _ ∘ rev n _)}
      (λ x y → cone λ n i → fwd n (x .chain.t.p n i) (y .chain.t.p n i))
      x (cone λ n i → piX n (x .chain.t.p (suc n) i))
      (λ i → cone λ n j → deg-sq.expand (x .chain.t.p n) (cong (piX n) (x .chain.t.p (suc n))) i1 (~ i) j)
      (λ y → cone λ n i → rev n (x .chain.t.p (suc n) i) (y .chain.t.p (suc n) i))
      (λ y → λ i → cone λ n j → deg-sq.dep.expand-dep {B = Y0 n}
       {p = x .chain.t.p n} {q = cong (piX n) (x .chain.t.p (suc n))}
       (y .chain.t.p n) (λ i → fwd n _ (rev n _ (y .chain.t.p (suc n) i)))
       i1 (~ i) j)
      (λ y i → cone λ n j → deg-sq.dep.expand-dep {B = Y1 n}
       {p = x .chain.t.p n} {q = cong (piX n) (x .chain.t.p (suc n))}
       (y .chain.t.p n) (λ i → rev n _ (fwd (suc n) _ (y .chain.t.p (suc n) i)))
         i1 (~ i) j)

  st-≃-t : st ≃ t
  st-≃-t .fst = f
  st-≃-t .snd = f-isEquiv
