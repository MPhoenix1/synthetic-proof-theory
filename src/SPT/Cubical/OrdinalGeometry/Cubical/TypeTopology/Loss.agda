{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Loss
  where

-- The projections into TypeTopology's ordinals and what they forget:
-- re-exports Bridge, PositionLoss (unbounded higher structure in a position
-- fiber), IdentityFiberLoss (the same in TypeTopology's own fibers and
-- h-levels), OmegaOneLoss (G ↦ ω₁ᴳ(G)′ is not an embedding) and
-- HeightLoss (the rank of heights as a TypeTopology ordinal has fibers
-- without finite h-level, so it is not an embedding).

open import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Bridge public
open import
  SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.PositionLoss public
open import
  SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.IdentityFiberLoss public
open import
  SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.OmegaOneLoss public
open import
  SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.HeightLoss public
