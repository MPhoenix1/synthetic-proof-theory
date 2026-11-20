{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Stationary.Discriminator where

-- The universes of stationary reflection have content. A universe's code
-- type has a point, its code of the natural numbers, so the empty child is
-- no universe (`inhabited`). Inclusion keeps the formers of the included
-- universe's child literally, and its resident family is the composite of
-- Residence.Families, both by refl (`included-formers`,
-- `included-resident`). A reflection whose closure is least has no Mahlo
-- child (`not-least`, from Residence.Unreflected), so the reflections the
-- rule gives at the unit predicate are never least closures.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Mahlo.Decoding using (child-formers)
open import SPT.Mahlo.Retraction using (Retracts)
import SPT.Mahlo.Specification as Specification
open import SPT.Mahlo.Residence.Absorption using (Induction)
import SPT.Mahlo.Residence.Families as Families
open import SPT.Mahlo.Residence.Reflection using (resident)
open import SPT.Mahlo.Residence.Unreflected using (not-mahlo)
import SPT.Mahlo.DS.Stationary as Stationarity

------------------------------------------------------------------------
-- Universes are inhabited, and inclusion is literal

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} (Q : Specification.Formers C D)
  where

  inhabited :
    (u : Stationarity.Universe Q) → D (Specification.Reflection.carrier u)
  inhabited u =
    pr₁ (Specification.Closure.natural (Specification.Reflection.closure u))

  included-formers :
    (u : Stationarity.Universe Q)
    (v : Stationarity.Universe
      (child-formers (Specification.Reflection.closure u)))
    → child-formers
        (Specification.Reflection.closure (Stationarity.included Q u v))
      ＝ child-formers (Specification.Reflection.closure v)
  included-formers u v = refl

  included-resident :
    (u : Stationarity.Universe Q)
    (v : Stationarity.Universe
      (child-formers (Specification.Reflection.closure u)))
    → resident (Stationarity.included Q u v)
      ＝ Families.compose D (resident u) (resident v)
  included-resident u v = refl

------------------------------------------------------------------------
-- Least closures are not witnesses

-- The child of a least closure is not Mahlo (Residence.Unreflected). The
-- universe of a reflection names what the reflection names, so a
-- reflection whose closure is least has no universe of degree one.

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} (Q : Specification.Formers C D)
  where

  not-least :
    Retracts Q
    → ((X : Set ℓ) (B : X → Set ℓ) → FunExt X B)
    → (Ψ : Specification.Operator D)
      (r : Specification.Reflection Q Ψ)
    → Induction (Specification.Reflection.closure r) ℓ
    → ¬ Stationarity.Mahlo-Of Q (suc zero) (Stationarity.universe Q r)
  not-least retracts extensionality Ψ r least m =
    not-mahlo retracts extensionality
      ( Specification.Reflection.closure r)
      least
      ( Stationarity.child-mahlo Q (Stationarity.universe Q r) m)
