{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Residence.Membership where

-- Generated membership: the closure of a Tarski family under the formers
-- and an operator, as an inductive family of witnesses over its names
-- (Form), with no induction–recursion. Names may lie at any level κ; the
-- total Σ C Form then lies at κ ⊔ ℓ. For a small family (κ = ℓ) the total
-- is a closure (generated) and the least one (least), every law by refl, so
-- closure is free; what remains is that the total be named (Residence), and
-- residence gives absorption (residence-absorbs).

open import SPT.Base
open import SPT.Mahlo.Specification using
  (Family; Operator; Formers; Closure)
open import SPT.Mahlo.Residence.Absorption using
  (Methods; Induction; Small-Least; Absorption; named)

------------------------------------------------------------------------
-- Witnesses of generated membership

-- A family along a map into the names: the names of its head and of its
-- branches.
along :
    {κ ℓ α : Level} {C : Set κ} {A : Set α}
    (D : C → Set ℓ)
    (f : A → C)
  → Family (λ a → D (f a))
  → Family D
along D f F = f (pr₁ F) , (λ x → f (pr₂ F x))

-- Each constructor witnesses that a name is formed from witnessed names:
-- by a former, or as the result or a branch of Ψ at a witnessed family.

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Formers C D) (Ψ : Operator D)
  where

  data Form : C → Set (κ ⊔ ℓ) where
    emptyᶠ : Form (Formers.empty Q)
    unitᶠ : Form (Formers.unit Q)
    twoᶠ : Form (Formers.two Q)
    naturalᶠ : Form (Formers.natural Q)
    productᶠ :
        (X : Family (λ (a : Σ C Form) → D (pr₁ a)))
      → Form (Formers.product Q (along D pr₁ X))
    sumᶠ :
        (X : Family (λ (a : Σ C Form) → D (pr₁ a)))
      → Form (Formers.sum Q (along D pr₁ X))
    treeᶠ :
        (X : Family (λ (a : Σ C Form) → D (pr₁ a)))
      → Form (Formers.tree Q (along D pr₁ X))
    identityᶠ :
        (a : Σ C Form)
        (x y : D (pr₁ a))
      → Form (Formers.identity Q (pr₁ a) x y)
    resultᶠ :
        (X : Family (λ (a : Σ C Form) → D (pr₁ a)))
      → Form (pr₁ (Ψ (along D pr₁ X)))
    branchᶠ :
        (X : Family (λ (a : Σ C Form) → D (pr₁ a)))
        (y : D (pr₁ (Ψ (along D pr₁ X))))
      → Form (pr₂ (Ψ (along D pr₁ X)) y)

------------------------------------------------------------------------
-- The generated closure of a small family

-- With names at the decodings' level, a code is a name with a witness,
-- read by the first projection. Induction over the witnesses is the
-- induction of the closure, so the generated closure is least.

module _
  {ℓ : Level} {C : Set ℓ} {D : C → Set ℓ}
  (Q : Formers C D) (Ψ : Operator D)
  where

  generated : Closure Q Ψ (Σ C (Form Q Ψ))
  generated = record
    { interpret = pr₁
    ; empty = (Formers.empty Q , emptyᶠ) , refl
    ; unit = (Formers.unit Q , unitᶠ) , refl
    ; two = (Formers.two Q , twoᶠ) , refl
    ; natural = (Formers.natural Q , naturalᶠ) , refl
    ; product = λ F → (Formers.product Q (along D pr₁ F) , productᶠ F) , refl
    ; sum = λ F → (Formers.sum Q (along D pr₁ F) , sumᶠ F) , refl
    ; tree = λ F → (Formers.tree Q (along D pr₁ F) , treeᶠ F) , refl
    ; identity = λ a x y →
        (Formers.identity Q (pr₁ a) x y , identityᶠ a x y) , refl
    ; inner = λ F →
        (pr₁ (Ψ (along D pr₁ F)) , resultᶠ F)
        , (λ y → pr₂ (Ψ (along D pr₁ F)) y , branchᶠ F y)
    ; inner-β = λ F → refl
    }

  induction :
      {ν : Level}
      (P : Σ C (Form Q Ψ) → Set ν)
    → Methods generated P
    → {c : C}
      (w : Form Q Ψ c)
    → P (c , w)
  induction P m emptyᶠ = Methods.on-empty m
  induction P m unitᶠ = Methods.on-unit m
  induction P m twoᶠ = Methods.on-two m
  induction P m naturalᶠ = Methods.on-natural m
  induction P m (productᶠ X) =
    Methods.on-product m X
      ( induction P m (pr₂ (pr₁ X)))
      ( λ x → induction P m (pr₂ (pr₂ X x)))
  induction P m (sumᶠ X) =
    Methods.on-sum m X
      ( induction P m (pr₂ (pr₁ X)))
      ( λ x → induction P m (pr₂ (pr₂ X x)))
  induction P m (treeᶠ X) =
    Methods.on-tree m X
      ( induction P m (pr₂ (pr₁ X)))
      ( λ x → induction P m (pr₂ (pr₂ X x)))
  induction P m (identityᶠ a x y) =
    Methods.on-identity m a x y (induction P m (pr₂ a))
  induction P m (resultᶠ X) =
    Methods.on-result m X
      ( induction P m (pr₂ (pr₁ X)))
      ( λ x → induction P m (pr₂ (pr₂ X x)))
  induction P m (branchᶠ X y) =
    Methods.on-branch m X y
      ( induction P m (pr₂ (pr₁ X)))
      ( λ x → induction P m (pr₂ (pr₂ X x)))

  least : (ν : Level) → Induction generated ν
  least ν = record
    { induction = λ P m a → induction P m (pr₂ a)
    ; induction-empty = λ P m → refl
    ; induction-unit = λ P m → refl
    ; induction-two = λ P m → refl
    ; induction-natural = λ P m → refl
    ; induction-product = λ P m φ → refl
    ; induction-sum = λ P m φ → refl
    ; induction-tree = λ P m φ → refl
    ; induction-identity = λ P m a x y → refl
    ; induction-result = λ P m φ → refl
    ; induction-branch = λ P m φ y → refl
    }

  generated-least : (ν : Level) → Small-Least Q Ψ ν
  generated-least ν = record
    { carrier = Σ C (Form Q Ψ)
    ; closure = generated
    ; induction = least ν
    }

------------------------------------------------------------------------
-- Residence

-- Mathematical shape: for every operator Ψ, a name whose decoding is the
-- generated total of Ψ. No induction–recursion is involved: the total is
-- small because the names are, and residence asks only that it be named.

module _
  {ℓ : Level} {C : Set ℓ} {D : C → Set ℓ}
  where

  Residence : Formers C D → Set (lsuc ℓ)
  Residence Q = (Ψ : Operator D) → Σ C (λ c → D c ＝ Σ C (Form Q Ψ))

  residence-absorbs :
      (Q : Formers C D)
    → Residence Q
    → (ν : Level)
    → Absorption Q ν
  residence-absorbs Q names ν = record
    { absorb = λ Ψ →
        named (generated-least Q Ψ ν) (pr₁ (names Ψ)) (pr₂ (names Ψ))
    }
