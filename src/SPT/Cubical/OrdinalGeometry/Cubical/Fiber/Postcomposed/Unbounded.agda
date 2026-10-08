{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Postcomposed.Unbounded
  where

-- Unbounded higher structure in every postcomposed fiber: one point of the
-- fiber of A ∘ q_G over A(1), for a level-zero geometry, carries a
-- nontrivial cell in every iterated loop space.  So that fiber, and the map
-- A ∘ q_G, have no finite h-level.

open import Agda.Primitive using (Level; lzero)
open import Data.Empty using (⊥)
import Data.Nat.Base as Nat

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Position
  as Position
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Postcomposed
  as Postcomposition
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.IteratedLoop
  as Iterated
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.PointedUniverse
  as PointedUniverse
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.SplitEmbedding
  as Split

import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Prelude as Cubical
import Cubical.Relation.Binary.Order.Woset.Base as Woset

private
  variable
    ℓ-target : Level
    Target : Set ℓ-target

------------------------------------------------------------------------
-- The base point

basePoint :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
    (adapter : Woset.Woset lzero lzero → Target)
  → Postcomposition.PostcomposedFiber geometry adapter
basePoint geometry adapter =
  Postcomposition.retain
    geometry adapter PointedUniverse.RigidPointedType

pointedEmbedding :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
    (adapter : Woset.Woset lzero lzero → Target)
  → Iterated.PointedSplitEmbedding
      (Position.PointedType lzero)
      PointedUniverse.RigidPointedType
      (Postcomposition.PostcomposedFiber geometry adapter)
      (basePoint geometry adapter)
pointedEmbedding geometry adapter =
  Iterated.pointed-split-embedding
    (Postcomposition.universeEmbedding
      geometry adapter)
    Cubical.refl

------------------------------------------------------------------------
-- Cells at every height

-- Ω^(n+1)(PointedType 0, RigidPointedType) embeds into Ω^(n+1) of the
-- fiber at basePoint, for every n (Fiber.Higher.PointedUniverse).

iteratedEmbedding :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
    (adapter : Woset.Woset lzero lzero → Target)
    (height : Nat.ℕ)
  → Iterated.PointedSplitEmbedding
      (Iterated.IteratedLoop (Nat.suc height)
        (Position.PointedType lzero)
        PointedUniverse.RigidPointedType)
      (Iterated.iteratedLoopPoint (Nat.suc height)
        (Position.PointedType lzero)
        PointedUniverse.RigidPointedType)
      (Iterated.IteratedLoop (Nat.suc height)
        (Postcomposition.PostcomposedFiber geometry adapter)
        (basePoint geometry adapter))
      (Iterated.iteratedLoopPoint (Nat.suc height)
        (Postcomposition.PostcomposedFiber geometry adapter)
        (basePoint geometry adapter))
iteratedEmbedding
    geometry adapter height =
  Iterated.iteratePointedSplitEmbedding (Nat.suc height)
    (pointedEmbedding geometry adapter)

-- cell(G,A,n) : Ω^(n+1)(fiber, basePoint) is not refl, for every n.

cell :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
    (adapter : Woset.Woset lzero lzero → Target)
    (height : Nat.ℕ)
  → Iterated.IteratedLoop (Nat.suc height)
      (Postcomposition.PostcomposedFiber geometry adapter)
      (basePoint geometry adapter)
cell geometry adapter height =
  Split.include
    (Iterated.splitEmbedding
      (iteratedEmbedding
        geometry adapter height))
    (PointedUniverse.pointedUniverseCell height)

cell-nontrivial :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
    (adapter : Woset.Woset lzero lzero → Target)
    (height : Nat.ℕ)
  → cell geometry adapter height Cubical.≡
      Iterated.iteratedLoopPoint (Nat.suc height)
        (Postcomposition.PostcomposedFiber geometry adapter)
        (basePoint geometry adapter)
  → ⊥
cell-nontrivial geometry adapter height =
  Iterated.preserves-nonbase
    (iteratedEmbedding
      geometry adapter height)
    (PointedUniverse.pointedUniverseCell height)
    (PointedUniverse.pointedUniverseCell-nontrivial height)

------------------------------------------------------------------------
-- No finite h-level

fiber-not-hlevel :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
    (adapter : Woset.Woset lzero lzero → Target)
    (height : Nat.ℕ)
  → HLevels.isOfHLevel (Nat.suc (Nat.suc height))
      (Postcomposition.PostcomposedFiber geometry adapter)
  → ⊥
fiber-not-hlevel
    geometry adapter height fiber-hlevel =
  cell-nontrivial geometry adapter height
    (Iterated.iteratedLoop-isProp
      height
      (basePoint geometry adapter)
      fiber-hlevel
      (cell geometry adapter height)
      (Iterated.iteratedLoopPoint (Nat.suc height)
        (Postcomposition.PostcomposedFiber geometry adapter)
        (basePoint geometry adapter)))

-- The fiber has no finite h-level: heights from two on are refuted by the
-- cells, and heights zero and one would imply height two.

fiber-not-finite-hlevel :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
    (adapter : Woset.Woset lzero lzero → Target)
    (height : Nat.ℕ)
  → HLevels.isOfHLevel height
      (Postcomposition.PostcomposedFiber geometry adapter)
  → ⊥
fiber-not-finite-hlevel
    geometry adapter Nat.zero fiber-contractible =
  fiber-not-hlevel geometry adapter Nat.zero
    (HLevels.isOfHLevelSuc (Nat.suc Nat.zero)
      (HLevels.isOfHLevelSuc Nat.zero fiber-contractible))
fiber-not-finite-hlevel
    geometry adapter (Nat.suc Nat.zero) fiber-proposition =
  fiber-not-hlevel geometry adapter Nat.zero
    (HLevels.isOfHLevelSuc (Nat.suc Nat.zero) fiber-proposition)
fiber-not-finite-hlevel
    geometry adapter (Nat.suc (Nat.suc height)) =
  fiber-not-hlevel geometry adapter height

-- Hence A ∘ q_G has no finite h-level as a map.

projection-not-finite-hlevel :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
    (adapter : Woset.Woset lzero lzero → Target)
    (height : Nat.ℕ)
  → HLevels.isOfHLevelFun height
      (Postcomposition.projection geometry adapter)
  → ⊥
projection-not-finite-hlevel
    geometry adapter height projection-hlevel =
  fiber-not-finite-hlevel geometry adapter height
    (projection-hlevel
      (adapter (Position.UnitOrderType lzero)))
