{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Formers where

-- The decoding laws of a universe's formers (Core.Mahlo.Decoding), read
-- as equivalences of types.  The unit code decodes to a point and the
-- empty code to nothing; two, natural, sum and product decode to 𝟐, ℕ, Σ
-- and Π.  So the power code of a,
--
--   power a = product (a , λ _ → two),   D (power a) ≃ (D a → 𝟐),
--
-- names the Boolean power set of D a, and under excluded middle every
-- proposition-valued family P on D a has a subset code with
-- D (subset P) ≃ Σ (D a) P.

open import Agda.Primitive using (Level)
open import Data.Empty using (⊥-elim)
import Data.Empty as StandardEmpty
open import Data.Nat using (ℕ)
open import Level using (Lift; lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Cubical.Data.Bool as Bool
open Bool using (Bool)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality.Conversion as EqualityConversion
import Cubical.Data.Sigma.Properties as SigmaProperties
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Isomorphism as Isomorphism
import Cubical.Foundations.Prelude as Cubical
import Cubical.Foundations.Univalence as Univalence
import Cubical.Relation.Nullary as Nullary
open Nullary using (Dec; yes; no)

open import SPT.Cubical.Core.Mahlo.Specification using (Formers)
open import SPT.Cubical.Core.Mahlo.Decoding using (DecodingLaws)
open import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Countability using
  (ExcludedMiddle)

private
  variable
    ℓ : Level

module _ {C : Set ℓ} {D : C → Set ℓ} (Q : Formers C D)
  (laws : DecodingLaws Q) where

  private
    law : {X Y : Set ℓ} → X ≡ Y → X Equiv.≃ Y
    law p = Univalence.pathToEquiv (EqualityConversion.eqToPath p)

    unlift : {X : Set} → Lift ℓ X Equiv.≃ X
    unlift =
      Isomorphism.isoToEquiv
        (Isomorphism.iso lower lift (λ _ → Cubical.refl) (λ _ → Cubical.refl))

  ----------------------------------------------------------------------
  -- Unit and empty

  unit-point : D (Formers.unit Q)
  unit-point =
    Equiv.invEq (law (DecodingLaws.unit-β laws)) (lift _)

  unit-prop : Cubical.isProp (D (Formers.unit Q))
  unit-prop =
    HLevels.isOfHLevelRespectEquiv 1
      (Equiv.invEquiv (law (DecodingLaws.unit-β laws)))
      (λ _ _ → Cubical.refl)

  empty-absurd : D (Formers.empty Q) → StandardEmpty.⊥
  empty-absurd z = lower (Equiv.equivFun (law (DecodingLaws.empty-β laws)) z)

  ----------------------------------------------------------------------
  -- 𝟐, ℕ, Σ and Π

  two-≃ : D (Formers.two Q) Equiv.≃ Bool
  two-≃ = Equiv.compEquiv (law (DecodingLaws.two-β laws)) unlift

  natural-≃ : D (Formers.natural Q) Equiv.≃ ℕ
  natural-≃ = Equiv.compEquiv (law (DecodingLaws.natural-β laws)) unlift

  sum-≃ : (a : C) (b : D a → C)
    → D (Formers.sum Q (a Cubical., b)) Equiv.≃ Cubical.Σ (D a) (λ x → D (b x))
  sum-≃ a b = law (DecodingLaws.sum-β laws a b)

  product-≃ : (a : C) (b : D a → C)
    → D (Formers.product Q (a Cubical., b)) Equiv.≃ ((x : D a) → D (b x))
  product-≃ a b = law (DecodingLaws.product-β laws a b)

  -- The code of the Boolean power set of D a.
  power : C → C
  power a = Formers.product Q (a Cubical., λ _ → Formers.two Q)

  power-≃ : (a : C) → D (power a) Equiv.≃ (D a → Bool)
  power-≃ a =
    Equiv.compEquiv (product-≃ a (λ _ → Formers.two Q))
      (Equiv.equivΠCod λ _ → two-≃)

  ----------------------------------------------------------------------
  -- Decided subsets

  module _ (lem : ExcludedMiddle ℓ) (a : C) (P : D a → Set ℓ)
    (P-prop : (x : D a) → Cubical.isProp (P x)) where

    private
      member : (x : D a) → Dec (P x) → C
      member x (yes _) = Formers.unit Q
      member x (no _) = Formers.empty Q

      member-≃ : (x : D a) (d : Dec (P x)) → D (member x d) Equiv.≃ P x
      member-≃ x (yes p) =
        Equiv.propBiimpl→Equiv unit-prop (P-prop x)
          (λ _ → p) (λ _ → unit-point)
      member-≃ x (no outside) =
        Equiv.propBiimpl→Equiv
          (λ z → ⊥-elim (empty-absurd z)) (P-prop x)
          (λ z → ⊥-elim (empty-absurd z)) (λ p → Empty.rec (outside p))

    -- Mathematical shape: D (subset P) ≃ Σ (x : D a). P x.
    subset : C
    subset =
      Formers.sum Q (a Cubical., λ x → member x (lem (P x) (P-prop x)))

    subset-≃ : D subset Equiv.≃ Cubical.Σ (D a) P
    subset-≃ =
      Equiv.compEquiv
        (sum-≃ a (λ x → member x (lem (P x) (P-prop x))))
        (SigmaProperties.Σ-cong-equiv-snd λ x →
          member-≃ x (lem (P x) (P-prop x)))
