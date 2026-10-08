{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Principal.Unbounded
  where

-- One point of UnitPresentations(G), for a level-zero geometry, carries a
-- nontrivial cell in every iterated loop space; so the space has no finite
-- h-level.

open import Agda.Primitive using (lzero)
open import Data.Empty using (⊥)
import Data.Nat.Base as Nat

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Position
  as Position
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Principal
  as Principal
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Principal.Retraction
  as Retraction
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

------------------------------------------------------------------------
-- The base point

basePoint :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
  → Principal.UnitPresentations geometry
basePoint geometry =
  Retraction.retain
    geometry PointedUniverse.RigidPointedType

universeEmbedding :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
  → Split.SplitEmbedding
      (Position.PointedType lzero)
      (Principal.UnitPresentations geometry)
universeEmbedding geometry =
  Split.split-embedding
    (Retraction.retain geometry)
    (Retraction.recover geometry)
    (Retraction.recover-retain geometry)

pointedEmbedding :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
  → Iterated.PointedSplitEmbedding
      (Position.PointedType lzero)
      PointedUniverse.RigidPointedType
      (Principal.UnitPresentations geometry)
      (basePoint geometry)
pointedEmbedding geometry =
  Iterated.pointed-split-embedding
    (universeEmbedding geometry)
    Cubical.refl

------------------------------------------------------------------------
-- Cells at every height

-- cell(G,n) : Ω^(n+1)(UnitPresentations(G), basePoint(G)) is not refl.

iteratedEmbedding :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
    (height : Nat.ℕ)
  → Iterated.PointedSplitEmbedding
      (Iterated.IteratedLoop (Nat.suc height)
        (Position.PointedType lzero)
        PointedUniverse.RigidPointedType)
      (Iterated.iteratedLoopPoint (Nat.suc height)
        (Position.PointedType lzero)
        PointedUniverse.RigidPointedType)
      (Iterated.IteratedLoop (Nat.suc height)
        (Principal.UnitPresentations geometry)
        (basePoint geometry))
      (Iterated.iteratedLoopPoint (Nat.suc height)
        (Principal.UnitPresentations geometry)
        (basePoint geometry))
iteratedEmbedding geometry height =
  Iterated.iteratePointedSplitEmbedding (Nat.suc height)
    (pointedEmbedding geometry)

cell :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
    (height : Nat.ℕ)
  → Iterated.IteratedLoop (Nat.suc height)
      (Principal.UnitPresentations geometry)
      (basePoint geometry)
cell geometry height =
  Split.include
    (Iterated.splitEmbedding
      (iteratedEmbedding geometry height))
    (PointedUniverse.pointedUniverseCell height)

cell-nontrivial :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
    (height : Nat.ℕ)
  → cell geometry height Cubical.≡
      Iterated.iteratedLoopPoint (Nat.suc height)
        (Principal.UnitPresentations geometry)
        (basePoint geometry)
  → ⊥
cell-nontrivial geometry height =
  Iterated.preserves-nonbase
    (iteratedEmbedding geometry height)
    (PointedUniverse.pointedUniverseCell height)
    (PointedUniverse.pointedUniverseCell-nontrivial height)

------------------------------------------------------------------------
-- No finite h-level

not-hlevel :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
    (height : Nat.ℕ)
  → HLevels.isOfHLevel (Nat.suc (Nat.suc height))
      (Principal.UnitPresentations geometry)
  → ⊥
not-hlevel
    geometry height principal-hlevel =
  cell-nontrivial geometry height
    (Iterated.iteratedLoop-isProp
      height
      (basePoint geometry)
      principal-hlevel
      (cell geometry height)
      (Iterated.iteratedLoopPoint (Nat.suc height)
        (Principal.UnitPresentations geometry)
        (basePoint geometry)))

-- No finite h-level: heights from two on are refuted by the cells, and
-- heights zero and one would imply height two.

not-finite-hlevel :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
    (height : Nat.ℕ)
  → HLevels.isOfHLevel height
      (Principal.UnitPresentations geometry)
  → ⊥
not-finite-hlevel
    geometry Nat.zero principal-contractible =
  not-hlevel geometry Nat.zero
    (HLevels.isOfHLevelSuc (Nat.suc Nat.zero)
      (HLevels.isOfHLevelSuc Nat.zero principal-contractible))
not-finite-hlevel
    geometry (Nat.suc Nat.zero) principal-proposition =
  not-hlevel geometry Nat.zero
    (HLevels.isOfHLevelSuc (Nat.suc Nat.zero) principal-proposition)
not-finite-hlevel
    geometry (Nat.suc (Nat.suc height)) =
  not-hlevel geometry height
