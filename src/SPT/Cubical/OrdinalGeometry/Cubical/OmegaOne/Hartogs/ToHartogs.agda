{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Hartogs.ToHartogs
  where

-- The map ω₁ → H_ℕ under excluded middle: a point goes to the small
-- representative of its principal segment, which embeds into ℕ.

open import Agda.Primitive using (Level)

import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Countability
  as NatCountability
import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Base as Hartogs
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Base as Omega
open import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Hartogs.Representative

import Cubical.Foundations.Prelude as Cubical
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

private
  variable
    ℓ : Level

toHartogs :
    NatCountability.ExcludedMiddle ℓ
  → Cubical.fst (Omega.ω₁ ℓ)
  → Hartogs.Carrier ℓ
toHartogs excluded-middle point =
  Cubical.fst (representative excluded-middle point)

toHartogs-segment :
    (excluded-middle : NatCountability.ExcludedMiddle ℓ)
  → (point : Cubical.fst (Omega.ω₁ ℓ))
  → Woset.WosetEquiv
      (Cubical.fst (toHartogs excluded-middle point))
      (Simulation._↓_ (Omega.ω₁ ℓ) point)
toHartogs-segment excluded-middle point =
  Cubical.snd (representative excluded-middle point)
