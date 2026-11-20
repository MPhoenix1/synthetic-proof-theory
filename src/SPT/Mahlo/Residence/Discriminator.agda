{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Residence.Discriminator where

-- Closure without residence. A small family with one name decoding to the
-- empty type, every former selecting that name, has the generated closure
-- of every operator, and its total is inhabited (generated-inhabited). The
-- total is therefore not the decoding of any name (no-residence), and the
-- family has no reflection at all (no-mahlo): its only carrier is empty and
-- cannot name the empty former. So the closure being free does not make the
-- family Mahlo; residence is the content.

open import SPT.Base
open import SPT.Mahlo.Specification using
  (Operator; Formers; Closure; Reflection; Mahlo)
open import SPT.Mahlo.Residence.Membership using
  (Form; emptyᶠ; generated; Residence)

module _
  {ℓ : Level}
  where

  -- One name, decoding to the empty type.
  Empty : Lift ℓ 𝟙 → Set ℓ
  Empty t = Lift ℓ 𝟘

  point-formers : Formers (Lift ℓ 𝟙) Empty
  point-formers = record
    { empty = lift ⋆
    ; unit = lift ⋆
    ; two = lift ⋆
    ; natural = lift ⋆
    ; product = λ F → lift ⋆
    ; sum = λ F → lift ⋆
    ; tree = λ F → lift ⋆
    ; identity = λ a x y → lift ⋆
    }

  -- The operator returning its argument.
  unchanged : Operator Empty
  unchanged F = F

  generated-closure :
      (Ψ : Operator Empty)
    → Closure point-formers Ψ (Σ (Lift ℓ 𝟙) (Form point-formers Ψ))
  generated-closure Ψ = generated point-formers Ψ

  generated-inhabited :
      (Ψ : Operator Empty)
    → Σ (Lift ℓ 𝟙) (Form point-formers Ψ)
  generated-inhabited Ψ = lift ⋆ , emptyᶠ

  no-residence : Residence point-formers → Lift ℓ 𝟘
  no-residence names =
    transport (λ X → X)
      ( pr₂ (names unchanged) ⁻¹)
      ( generated-inhabited unchanged)

  no-mahlo : Mahlo point-formers → Lift ℓ 𝟘
  no-mahlo mahlo =
    pr₁
      ( Closure.empty
          ( Reflection.closure (Mahlo.reflect mahlo unchanged)))
