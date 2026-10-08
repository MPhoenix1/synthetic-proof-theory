{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Hartogs.Below
  where

-- Under excluded middle, every point of H_ℕ lies strictly below ω₁: its
-- well-order embeds into ℕ, hence is countable, hence presented.

open import Agda.Primitive using (Level)

import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Countability
  as NatCountability
import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Base as Hartogs
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Base as Omega
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Countability
  as OmegaCountability

import Cubical.Foundations.Prelude as Cubical
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

private
  variable
    ℓ : Level

abstract
  below :
      NatCountability.ExcludedMiddle ℓ
    → (point : Hartogs.Carrier ℓ)
    → Simulation._≺_
        (Cubical.fst point)
        (Omega.ω₁ ℓ)
  below excluded-middle point =
    OmegaCountability.embeds→strict
      excluded-middle (Cubical.fst point)
      (Cubical.snd point)
