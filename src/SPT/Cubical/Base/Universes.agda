{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Base.Universes where

-- Types live in Agda's universes `Set ℓ`, indexed by levels: `lzero` is the
-- lowest, `lsuc ℓ` the next above `ℓ`, and `ℓ ⊔ κ` the least above both. SPT
-- writes universes as Agda does, `Set ℓ`, with no wrapper of its own, since a
-- wrapper would be a second spelling of every universe.
--
-- A type moves to a higher universe by lifting, which keeps its points and
-- changes only the level.

open import Agda.Primitive public
  using (Level; lzero; lsuc; _⊔_; Setω)

------------------------------------------------------------------------
-- Lifting

record Lift {ℓ : Level} (κ : Level) (A : Set ℓ) : Set (ℓ ⊔ κ) where
  constructor lift
  field
    lower : A

open Lift public
