{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Hartogs.Representative
  where

-- Small representatives of the principal segments of ω₁ in H_ℕ, under
-- excluded middle.

open import Agda.Primitive using (Level; lsuc)

import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Countability
  as NatCountability
import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Base as Hartogs
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType as Reflection
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Base as Omega
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Countability
  as OmegaCountability
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Cut as OmegaCut

import Cubical.Data.Sigma.Properties as SigmaProperties
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.Prelude as Cubical
import Cubical.HITs.PropositionalTruncation as Truncation
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

private
  variable
    ℓ : Level

-- Representative(q) = Σ(α : H_ℕ(ℓ)). α ≃ ω₁ ↓ q.  It is a proposition, so a
-- merely given presentation of ω₁ ↓ q produces one without choice.

Representative :
    (point : Cubical.fst (Omega.ω₁ ℓ))
  → Set (lsuc ℓ)
Representative {ℓ} point =
  Cubical.Σ
    (Hartogs.Carrier ℓ)
    (λ ordinal →
      Woset.WosetEquiv
        (Cubical.fst ordinal)
        (Simulation._↓_ (Omega.ω₁ ℓ) point))

Representative-isProp :
    (point : Cubical.fst (Omega.ω₁ ℓ))
  → Cubical.isProp (Representative point)
Representative-isProp point left right =
  SigmaProperties.Σ≡Prop
    (λ _ → Simulation.isPropValuedWosetEquiv)
    (SigmaProperties.Σ≡Prop
      (λ _ → NatCountability.isPropMerelyEmbedsInNat)
      (Equiv.equivFun
        (Woset.WosetPath
          (Cubical.fst (Cubical.fst left))
          (Cubical.fst (Cubical.fst right)))
        (Woset.compWosetEquiv
          (Cubical.snd left)
          (Woset.invWosetEquiv (Cubical.snd right)))))

abstract
  representative :
      NatCountability.ExcludedMiddle ℓ
    → (point : Cubical.fst (Omega.ω₁ ℓ))
    → Representative point
  representative {ℓ} excluded-middle point =
    Truncation.rec
      (Representative-isProp point)
      (λ represented →
        let
          presentation = Cubical.fst represented
          ordinal = Reflection.orderType presentation
          strict = Omega.orderType-strict presentation
          nat-countable =
            OmegaCountability.strict→embeds
              excluded-middle ordinal
              strict
        in
        (ordinal Cubical., nat-countable)
        Cubical., Cubical.snd represented)
      (OmegaCut.segment-presented point)
