{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Sorted.Discriminator where

-- Outputs in operators on types, which are not polynomial in types. For
-- O = Set ℓ → Set ℓ, a description with two outputs, the identity
-- operator and negation (`operators`, `description`). Every algebra of it
-- keeps its two operations apart, since at the unit type the identity and
-- negation differ (`distinct`). A Mahlo reflection of the two-sorted
-- family gives it a small algebra (`algebra`, `law`, by Mahlo.outputs),
-- which therefore separates them too (`apart`).

open import SPT.Base
import SPT.Mahlo.Specification as Specification

open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.IR.Description using (Desc; ι; σ)
open import SPT.Mahlo.DS.Sorted using (formers)
import SPT.Mahlo.DS.Sorted.Mahlo as Mahlo

------------------------------------------------------------------------
-- Two operator outputs

-- ₀ ↦ the identity operator; ₁ ↦ negation.
operators : {ℓ : Level} → Lift ℓ 𝟚 → Desc {s = ℓ} (Set ℓ → Set ℓ)
operators (lift ₀) = ι (λ X → X)
operators {ℓ} (lift ₁) = ι (λ X → X → Lift ℓ 𝟘)

description : {ℓ : Level} → Desc {s = ℓ} (Set ℓ → Set ℓ)
description {ℓ} = σ (Lift ℓ 𝟚) operators

------------------------------------------------------------------------
-- The law separates the operations

distinct :
  {ℓ : Level} (M : Algebra ℓ (description {ℓ})) → Law M
  → Algebra.operation M (lift ₀ , lift ⋆)
    ＝ Algebra.operation M (lift ₁ , lift ⋆)
  → 𝟘
distinct {ℓ} M law same =
  let operators-equal =
        law (lift ₀ , lift ⋆) ⁻¹
        ∙ (ap (Algebra.value M) same ∙ law (lift ₁ , lift ⋆))
      at-unit = ap (λ f → f (Lift ℓ 𝟙)) operators-equal
  in lower (transport (λ X → X) at-unit (lift ⋆) (lift ⋆))

------------------------------------------------------------------------
-- From the two-sorted Mahlo rule

algebra :
  {ℓ : Level} → Specification.Mahlo (formers ℓ (Set ℓ → Set ℓ))
  → Algebra ℓ (description {ℓ})
algebra reflections = Mahlo.outputs reflections description

law :
  {ℓ : Level} (reflections : Specification.Mahlo (formers ℓ (Set ℓ → Set ℓ)))
  → Law (algebra reflections)
law reflections = Mahlo.outputs-law reflections description

apart :
  {ℓ : Level} (reflections : Specification.Mahlo (formers ℓ (Set ℓ → Set ℓ)))
  → Algebra.operation (algebra reflections) (lift ₀ , lift ⋆)
    ＝ Algebra.operation (algebra reflections) (lift ₁ , lift ⋆)
  → 𝟘
apart reflections =
  distinct (algebra reflections) (law reflections)
