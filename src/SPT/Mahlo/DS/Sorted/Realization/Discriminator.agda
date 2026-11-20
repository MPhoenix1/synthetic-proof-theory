{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Sorted.Realization.Discriminator where

-- The two-sorted Mahlo rule is inhabited, and the realization computes
-- through it. The reflector is the induction–recursive closure of each
-- operator on two-sorted families (`Code`, `interpret`, `closure`,
-- `reflector`), whose names hold by refl: in Agda, induction–recursion with
-- outputs in Sort ℓ O gives the rule. For the closed description with the
-- identity operator and negation as outputs (Sorted.Discriminator), the
-- small algebra built from it decodes both operations by refl
-- (`identity-β`, `negation-β`). This is the only induction–recursive
-- definition in Mahlo.DS.Sorted.

open import SPT.Base
import SPT.Mahlo.Specification as Specification

open import SPT.IR.Algebra using (Algebra)
open import SPT.Mahlo.DS.Sorted using (Sort; decode; formers)
import SPT.Mahlo.DS.Sorted.Discriminator as Operators
import SPT.Mahlo.DS.Sorted.Mahlo as Mahlo

------------------------------------------------------------------------
-- The induction–recursive closure of an operator

mutual
  data Code {ℓ κ : Level} {O : Set κ}
    (Ψ : Specification.Operator (decode ℓ O)) : Set ℓ where
    empty unit two natural : Code Ψ
    product sum tree result :
      (a : Code Ψ) → (decode ℓ O (interpret Ψ a) → Code Ψ) → Code Ψ
    identity :
      (a : Code Ψ) → decode ℓ O (interpret Ψ a)
      → decode ℓ O (interpret Ψ a) → Code Ψ
    branch :
      (a : Code Ψ) (b : decode ℓ O (interpret Ψ a) → Code Ψ)
      → decode ℓ O (pr₁ (Ψ (interpret Ψ a , (λ x → interpret Ψ (b x)))))
      → Code Ψ

  interpret :
    {ℓ κ : Level} {O : Set κ} (Ψ : Specification.Operator (decode ℓ O))
    → Code Ψ → Sort ℓ O
  interpret {ℓ} {κ} {O} Ψ empty =
    Specification.Formers.empty (formers ℓ O)
  interpret {ℓ} {κ} {O} Ψ unit = Specification.Formers.unit (formers ℓ O)
  interpret {ℓ} {κ} {O} Ψ two = Specification.Formers.two (formers ℓ O)
  interpret {ℓ} {κ} {O} Ψ natural =
    Specification.Formers.natural (formers ℓ O)
  interpret {ℓ} {κ} {O} Ψ (product a b) =
    Specification.Formers.product (formers ℓ O)
      (interpret Ψ a , (λ x → interpret Ψ (b x)))
  interpret {ℓ} {κ} {O} Ψ (sum a b) =
    Specification.Formers.sum (formers ℓ O)
      (interpret Ψ a , (λ x → interpret Ψ (b x)))
  interpret {ℓ} {κ} {O} Ψ (tree a b) =
    Specification.Formers.tree (formers ℓ O)
      (interpret Ψ a , (λ x → interpret Ψ (b x)))
  interpret {ℓ} {κ} {O} Ψ (identity a x y) =
    Specification.Formers.identity (formers ℓ O) (interpret Ψ a) x y
  interpret Ψ (result a b) =
    pr₁ (Ψ (interpret Ψ a , (λ x → interpret Ψ (b x))))
  interpret Ψ (branch a b y) =
    pr₂ (Ψ (interpret Ψ a , (λ x → interpret Ψ (b x)))) y

closure :
  {ℓ κ : Level} {O : Set κ} (Ψ : Specification.Operator (decode ℓ O))
  → Specification.Closure (formers ℓ O) Ψ (Code Ψ)
closure Ψ = record
  { interpret = interpret Ψ
  ; empty = empty , refl
  ; unit = unit , refl
  ; two = two , refl
  ; natural = natural , refl
  ; product = λ F → product (pr₁ F) (pr₂ F) , refl
  ; sum = λ F → sum (pr₁ F) (pr₂ F) , refl
  ; tree = λ F → tree (pr₁ F) (pr₂ F) , refl
  ; identity = λ a x y → identity a x y , refl
  ; inner = λ F → result (pr₁ F) (pr₂ F) , (λ y → branch (pr₁ F) (pr₂ F) y)
  ; inner-β = λ F → refl
  }

reflector :
  {κ : Level} (ℓ : Level) (O : Set κ) → Specification.Mahlo (formers ℓ O)
reflector ℓ O = record
  { reflect = λ Ψ → record { carrier = inl (Code Ψ) ; closure = closure Ψ }
  }

------------------------------------------------------------------------
-- Operator outputs decode by conversion

small : Algebra lzero (Operators.description {lzero})
small = Mahlo.outputs (reflector lzero (Set → Set)) Operators.description

identity-β :
  Algebra.value small (Algebra.operation small (lift ₀ , lift ⋆))
  ＝ (λ X → X)
identity-β = refl

negation-β :
  Algebra.value small (Algebra.operation small (lift ₁ , lift ⋆))
  ＝ (λ X → X → Lift lzero 𝟘)
negation-β = refl
