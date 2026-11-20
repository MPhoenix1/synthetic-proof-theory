{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Polynomial.Outputs.Discriminator where

-- Outputs in families of types keep their fibers. The code of a family of
-- types has a base and a type at each of its points (`fibered`). Two rules
-- with that output (`rule`, `outputs`): at ₀ the point family, a unit base
-- with empty fibers; at ₁ the complement of a family from ₀, the same base
-- with each fiber replaced by its negation. For any extensionality and
-- smallness, the derived point and its complement read out by the output
-- law (`point-β`, `complement-β`). The point's base is inhabited (`base`)
-- and all its fibers are empty (`empty`), while all fibers of its
-- complement are inhabited (`inhabited`): the structured codes carry the
-- fibers, not only the base.

open import SPT.Base

open import SPT.IR.Polynomial using
  (Poly; var; con; sigma; pi; Description; described; Extensionality;
   readout)
import SPT.IR.Polynomial.Generated as Generated
open import SPT.IR.Polynomial.Outputs using (Outputs)
open import SPT.IR.Smallness using (Smallness)
open import SPT.Mahlo.DS.Polynomial.Outputs using (small)

------------------------------------------------------------------------
-- Families of types and two rules

module _ {ℓ : Level} where

  fibered :
    Poly ℓ (lsuc ℓ) (λ (_ : 𝟙) → Set ℓ) (Σ (Set ℓ) (λ X → X → Set ℓ))
  fibered = sigma (var ⋆) (λ X → pi X (λ _ → var ⋆))

  -- ₀ ↦ the point family; ₁ ↦ the complement of a family from ₀.
  rule :
    (i : Lift ℓ 𝟚)
    → Description ℓ (lsuc ℓ)
        (λ (_ : Lift ℓ 𝟚) → Σ (Set ℓ) (λ X → X → Set ℓ))
        (Σ (Set ℓ) (λ X → X → Set ℓ))
  rule (lift ₀) =
    described (con (Lift ℓ 𝟙)) (λ _ → Lift ℓ 𝟙 , (λ _ → Lift ℓ 𝟘))
  rule (lift ₁) =
    described (var (lift ₀)) (λ d → pr₁ d , (λ b → pr₂ d b → Lift ℓ 𝟘))

  outputs : Outputs ℓ
  outputs = record
    { underlying = record
        { Index = Lift ℓ 𝟚
        ; Data = λ (_ : Lift ℓ 𝟚) → Σ (Set ℓ) (λ X → X → Set ℓ)
        ; rule = rule
        }
    ; form = λ _ → fibered
    }

-- Fibers along an identity of families.
fiber-at :
  {ℓ : Level} {v w : Σ (Set ℓ) (λ X → X → Set ℓ)} (e : v ＝ w) (b : pr₁ v)
  → pr₂ v b ＝ pr₂ w (transport (λ X → X) (ap pr₁ e) b)
fiber-at refl b = refl

------------------------------------------------------------------------
-- The derived point and its complement

module _
  {ℓ : Level} (extensionality : Extensionality ℓ (lsuc ℓ))
  (smallness : Smallness ℓ)
  where

  point : Generated.Carrier (small extensionality smallness outputs) (lift ₀)
  point =
    Generated.make (small extensionality smallness outputs) extensionality
      (lift ₀) (lift ⋆)

  complement :
    Generated.Carrier (small extensionality smallness outputs) (lift ₁)
  complement =
    Generated.make (small extensionality smallness outputs) extensionality
      (lift ₁) point

  point-β :
    readout (Generated.generated (small extensionality smallness outputs))
      (lift ₀) point
    ＝ (Lift ℓ 𝟙 , (λ _ → Lift ℓ 𝟘))
  point-β =
    Generated.make-β (small extensionality smallness outputs) extensionality
      (lift ₀) (lift ⋆)

  complement-β :
    readout (Generated.generated (small extensionality smallness outputs))
      (lift ₁) complement
    ＝ ( pr₁
           (readout
             (Generated.generated (small extensionality smallness outputs))
             (lift ₀) point)
       , (λ b →
           pr₂
             (readout
               (Generated.generated (small extensionality smallness outputs))
               (lift ₀) point)
             b
           → Lift ℓ 𝟘))
  complement-β =
    Generated.make-β (small extensionality smallness outputs) extensionality
      (lift ₁) point

  base :
    pr₁
      (readout (Generated.generated (small extensionality smallness outputs))
        (lift ₀) point)
  base = transport (λ X → X) (ap pr₁ point-β ⁻¹) (lift ⋆)

  empty :
    (b :
      pr₁
        (readout
          (Generated.generated (small extensionality smallness outputs))
          (lift ₀) point))
    → pr₂
        (readout
          (Generated.generated (small extensionality smallness outputs))
          (lift ₀) point)
        b
    → 𝟘
  empty b x = lower (transport (λ X → X) (fiber-at point-β b) x)

  inhabited :
    (b :
      pr₁
        (readout
          (Generated.generated (small extensionality smallness outputs))
          (lift ₁) complement))
    → pr₂
        (readout
          (Generated.generated (small extensionality smallness outputs))
          (lift ₁) complement)
        b
  inhabited b =
    transport (λ X → X) (fiber-at complement-β b ⁻¹)
      (λ x →
        lift (empty (transport (λ X → X) (ap pr₁ complement-β) b) x))
