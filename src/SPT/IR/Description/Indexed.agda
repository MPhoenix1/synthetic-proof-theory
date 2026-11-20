{-# OPTIONS --safe --without-K #-}

module SPT.IR.Description.Indexed where

-- Dybjer–Setzer's codes for indexed induction–recursion (Indexed
-- induction–recursion, JLAP 2006, §4.5): ι gives an output, σ a small sum,
-- and δ an A-indexed family of recursive inputs at the indices i a, whose
-- decodings select the continuation (`IDS`). A code acts on an indexed
-- family of carriers with readouts (Polynomial's `Family`) by its shapes,
-- outputs and hypotheses (`Shape`, `Mark`, `IH`, `map-IH`: their F^U, F^T,
-- F^IH and F^map). A general code ends at an index with a decoding there
-- (`General`, their §4.7); a restricted code is a general code σ I (λ i → …
-- ι (i , e)), as their §4.5 notes. Every code is a polynomial code of
-- Polynomial with an output (`Information`, `polynomial`, `result`):
--
--   polynomial (ι e)     = con 𝟙
--   polynomial (σ A f)   = sigma (con A) (λ x → polynomial (f (lower x)))
--   polynomial (δ A i F) =
--     sigma (pi A (λ a → var (i a))) (λ g → polynomial (F g)).
--
-- A general code is a scheme once the index its argument computes is
-- identified with the index of the rule, the identification being part
-- of the argument (`located`, `relocated`, `general`). No
-- induction–recursion is used here.

open import SPT.Base

open import SPT.IR.Polynomial using
  (Poly; var; con; sigma; pi; Family; carrier; readout; described; Scheme)

------------------------------------------------------------------------
-- Codes

-- Mathematical shape:
--
--   ι : E → IDS I D E
--   σ : (A : Set ℓ) → (A → IDS I D E) → IDS I D E
--   δ : (A : Set ℓ) (i : A → I) → (((a : A) → D (i a)) → IDS I D E)
--       → IDS I D E.

data IDS {ε : Level} (ℓ κ : Level) (I : Set ℓ) (D : I → Set (ℓ ⊔ κ))
  (E : Set ε) : Set (lsuc ℓ ⊔ κ ⊔ ε) where
  ι : E → IDS ℓ κ I D E
  σ : (A : Set ℓ) → (A → IDS ℓ κ I D E) → IDS ℓ κ I D E
  δ : (A : Set ℓ) (i : A → I) → (((a : A) → D (i a)) → IDS ℓ κ I D E)
    → IDS ℓ κ I D E

-- A general code returns an index with a decoding at it.

General :
  (ℓ κ : Level) (I : Set ℓ) → (I → Set (ℓ ⊔ κ)) → Set (lsuc ℓ ⊔ κ)
General ℓ κ I D = IDS ℓ κ I D (Σ I D)

------------------------------------------------------------------------
-- The action on an indexed family

-- Mathematical shape, writing T for the readout of Z:
--
--   Shape (ι e) Z = 𝟙
--   Shape (σ A f) Z = Σ (a : A). Shape (f a) Z
--   Shape (δ A i F) Z =
--     Σ (g : (a : A) → carrier Z (i a)). Shape (F (λ a → T (i a) (g a))) Z.

module _
  {ε ℓ κ : Level} {I : Set ℓ} {D : I → Set (ℓ ⊔ κ)} {E : Set ε}
  where

  Shape : IDS ℓ κ I D E → Family ℓ κ D → Set ℓ
  Shape (ι e) Z = Lift ℓ 𝟙
  Shape (σ A f) Z = Σ A (λ a → Shape (f a) Z)
  Shape (δ A i F) Z =
    Σ ((a : A) → carrier Z (i a))
      (λ g → Shape (F (λ a → readout Z (i a) (g a))) Z)

  Mark : (γ : IDS ℓ κ I D E) (Z : Family ℓ κ D) → Shape γ Z → E
  Mark (ι e) Z x = e
  Mark (σ A f) Z (a , x) = Mark (f a) Z x
  Mark (δ A i F) Z (g , x) = Mark (F (λ a → readout Z (i a) (g a))) Z x

  -- A hypothesis at every recursive input, for a motive over the family,
  -- and the hypotheses that a section of the motive supplies.

  IH :
    {ν : Level} (γ : IDS ℓ κ I D E) (Z : Family ℓ κ D)
    → ((i : I) → carrier Z i → Set ν) → Shape γ Z → Set (ℓ ⊔ ν)
  IH {ν} (ι e) Z P x = Lift (ℓ ⊔ ν) 𝟙
  IH (σ A f) Z P (a , x) = IH (f a) Z P x
  IH (δ A i F) Z P (g , x) =
    Σ ((a : A) → P (i a) (g a))
      (λ _ → IH (F (λ a → readout Z (i a) (g a))) Z P x)

  map-IH :
    {ν : Level} (γ : IDS ℓ κ I D E) (Z : Family ℓ κ D)
    (P : (i : I) → carrier Z i → Set ν)
    → ((i : I) (u : carrier Z i) → P i u) → (x : Shape γ Z) → IH γ Z P x
  map-IH (ι e) Z P h x = lift ⋆
  map-IH (σ A f) Z P h (a , x) = map-IH (f a) Z P h x
  map-IH (δ A i F) Z P h (g , x) =
    (λ a → h (i a) (g a)) ,
    map-IH (F (λ a → readout Z (i a) (g a))) Z P h x

------------------------------------------------------------------------
-- Codes as polynomial codes

-- The information of a code is that of its polynomial code: one point at
-- ι, a lifted point and the rest at σ, and at δ the decodings of the
-- inputs and the rest.

  Information : IDS ℓ κ I D E → Set (ℓ ⊔ κ)
  Information (ι e) = Lift κ (Lift ℓ 𝟙)
  Information (σ A f) = Σ (Lift κ A) (λ x → Information (f (lower x)))
  Information (δ A i F) = Σ ((a : A) → D (i a)) (λ g → Information (F g))

  polynomial : (γ : IDS ℓ κ I D E) → Poly ℓ κ D (Information γ)
  polynomial (ι e) = con (Lift ℓ 𝟙)
  polynomial (σ A f) = sigma (con A) (λ x → polynomial (f (lower x)))
  polynomial (δ A i F) =
    sigma (pi A (λ a → var (i a))) (λ g → polynomial (F g))

  result : (γ : IDS ℓ κ I D E) → Information γ → E
  result (ι e) x = e
  result (σ A f) (x , y) = result (f (lower x)) y
  result (δ A i F) (g , y) = result (F g) y

------------------------------------------------------------------------
-- General codes as schemes

-- At an index i the rule takes an argument of the code with an
-- identification of the index it computes with i, and returns its
-- decoding transported along that identification.

module _
  {ℓ κ : Level} {I : Set ℓ} {D : I → Set (ℓ ⊔ κ)} (γ : General ℓ κ I D)
  where

  located :
    (i : I) (x : Information γ) → Poly ℓ κ D (Lift κ (pr₁ (result γ x) ＝ i))
  located i x = con (pr₁ (result γ x) ＝ i)

  relocated :
    (i : I) → Σ (Information γ) (λ x → Lift κ (pr₁ (result γ x) ＝ i)) → D i
  relocated i (x , e) = transport D (lower e) (pr₂ (result γ x))

  general : Scheme ℓ κ
  general = record
    { Index = I
    ; Data = D
    ; rule = λ i → described (sigma (polynomial γ) (located i)) (relocated i)
    }
