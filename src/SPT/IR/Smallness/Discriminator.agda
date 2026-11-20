{-# OPTIONS --safe --without-K #-}

module SPT.IR.Smallness.Discriminator where

-- The law of a small algebra has content. For the description with two
-- outputs, unit and empty, the one-point algebra decoding to unit fails the
-- law (`one-point-fails`), and every algebra keeps its two operations apart
-- (`distinct`): the carrier must separate what the outputs separate. So do
-- the decoding laws of a lowering: its `down` keeps the two raised codes
-- apart (`separates`).

open import SPT.Base

open import SPT.IR.Algebra using (Algebra; Law; identity)
open import SPT.IR.Description using (Desc; ι; σ)
import SPT.IR.Generated as Generated
open import SPT.IR.Smallness.Lowering using (Lowering)

------------------------------------------------------------------------
-- Two outputs

-- ₀ ↦ unit, ₁ ↦ empty.
outputs : {ℓ : Level} → Lift ℓ 𝟚 → Desc {s = ℓ} (Set ℓ)
outputs {ℓ} (lift ₀) = ι (Lift ℓ 𝟙)
outputs {ℓ} (lift ₁) = ι (Lift ℓ 𝟘)

description : {ℓ : Level} → Desc {s = ℓ} (Set ℓ)
description {ℓ} = σ (Lift ℓ 𝟚) outputs

------------------------------------------------------------------------
-- The law refutes a one-point carrier and separates the operations

one-point : {ℓ : Level} → Algebra ℓ (description {ℓ})
one-point {ℓ} = record
  { K = Lift ℓ 𝟙
  ; value = λ _ → Lift ℓ 𝟙
  ; operation = λ _ → lift ⋆
  }

one-point-fails : {ℓ : Level} → Law (one-point {ℓ}) → 𝟘
one-point-fails law =
  lower (transport (λ X → X) (law (lift ₁ , lift ⋆)) (lift ⋆))

distinct :
  {ℓ : Level} (M : Algebra ℓ (description {ℓ})) → Law M
  → Algebra.operation M (lift ₀ , lift ⋆)
    ＝ Algebra.operation M (lift ₁ , lift ⋆)
  → 𝟘
distinct M law same =
  lower
    ( transport (λ X → X)
        ( law (lift ₀ , lift ⋆) ⁻¹
        ∙ ( ap (Algebra.value M) same
          ∙ law (lift ₁ , lift ⋆)))
        (lift ⋆))

------------------------------------------------------------------------
-- A lowering separates the two raised codes

-- The raised codes of the two operations decode to unit and empty by refl,
-- so the decoding law of `down` keeps their images apart.

separates :
  {ℓ : Level} (lowering : Lowering (description {ℓ}))
  → Lowering.down lowering
      (Generated.make (identity (description {ℓ})) (lift ₀ , lift ⋆))
    ＝ Lowering.down lowering
        (Generated.make (identity (description {ℓ})) (lift ₁ , lift ⋆))
  → 𝟘
separates {ℓ} lowering same =
  lower
    ( transport (λ X → X)
        ( Lowering.down-β lowering
            (Generated.make (identity (description {ℓ})) (lift ₀ , lift ⋆))
            ⁻¹
        ∙ ( ap (Lowering.value lowering) same
          ∙ Lowering.down-β lowering
              (Generated.make (identity (description {ℓ}))
                (lift ₁ , lift ⋆))))
        (lift ⋆))
