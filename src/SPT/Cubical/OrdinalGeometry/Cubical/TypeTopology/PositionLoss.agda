{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.PositionLoss
  where

-- What the projection into TypeTopology's ordinals forgets at positions:
-- the case A = toOrdinal of Fiber.Postcomposed.  One fiber of
-- q′_G : Position(G) → Ordinal contains the pointed universe and the
-- pointed automorphisms as loops, has unbounded higher structure, and so
-- has no finite h-level.

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
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Postcomposed.Automorphism
  as Automorphism
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Postcomposed.PointedUnivalence
  as PointedUnivalence
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Postcomposed.Unbounded
  as Unbounded
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.IteratedLoop
  as Iterated
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.SplitEmbedding
  as Split
import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Bridge as Bridge

import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Prelude as Cubical
import Cubical.Functions.Embedding as Embedding
import SPT.Cubical.TypeTopology.Ordinals.Type as TypeTopologyOrdinal

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- The projection and its fiber

-- q′_G(u) = toOrdinal(q_G(u)), from positions to TypeTopology's ordinals.

projection :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → Presented.ω₁.Geometry.Position geometry
  → TypeTopologyOrdinal.Ordinal ℓ
projection geometry =
  Postcomposition.projection geometry
    Bridge.toOrdinal

-- PositionFiber(G) = hofib(q′_G, toOrdinal(1)), the fiber over the
-- one-point ordinal.

PositionFiber :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → Set _
PositionFiber geometry =
  Postcomposition.PostcomposedFiber geometry
    Bridge.toOrdinal

------------------------------------------------------------------------
-- The pointed universe and its automorphisms

-- PointedType(ℓ) ◁ PositionFiber(G); recovery reads only the presentation,
-- never the ordinal.

universeEmbedding :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → Split.SplitEmbedding
      (Position.PointedType ℓ)
      (PositionFiber geometry)
universeEmbedding geometry =
  Postcomposition.universeEmbedding
    geometry Bridge.toOrdinal

-- Aut∗(T,t) ◁∗ Loop(PositionFiber(G), retain(T,t)).

automorphismEmbedding :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (pointed : Position.PointedType ℓ)
  → Iterated.PointedSplitEmbedding
      (PointedUnivalence.PointedAutomorphism pointed)
      (PointedUnivalence.identityAutomorphism pointed)
      (Iterated.Loop
        (PositionFiber geometry)
        (Postcomposition.retain
          geometry Bridge.toOrdinal pointed))
      Cubical.refl
automorphismEmbedding
    geometry pointed =
  Automorphism.automorphismEmbedding
    geometry Bridge.toOrdinal pointed

iteratedEmbedding :
    (height : Nat.ℕ)
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (pointed : Position.PointedType ℓ)
  → Iterated.PointedSplitEmbedding
      (Iterated.IteratedLoop height
        (PointedUnivalence.PointedAutomorphism pointed)
        (PointedUnivalence.identityAutomorphism pointed))
      (Iterated.iteratedLoopPoint height
        (PointedUnivalence.PointedAutomorphism pointed)
        (PointedUnivalence.identityAutomorphism pointed))
      (Iterated.IteratedLoop (Nat.suc height)
        (PositionFiber geometry)
        (Postcomposition.retain
          geometry Bridge.toOrdinal pointed))
      (Iterated.iteratedLoopPoint (Nat.suc height)
        (PositionFiber geometry)
        (Postcomposition.retain
          geometry Bridge.toOrdinal pointed))
iteratedEmbedding
    height geometry pointed =
  Automorphism.iteratedEmbedding
    height geometry Bridge.toOrdinal pointed

------------------------------------------------------------------------
-- Unbounded higher structure

basePoint :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
  → PositionFiber geometry
basePoint geometry =
  Unbounded.basePoint geometry
    Bridge.toOrdinal

-- cell(G,n) : Ω^(n+1)(PositionFiber(G), basePoint) is not refl.

cell :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
    (height : Nat.ℕ)
  → Iterated.IteratedLoop (Nat.suc height)
      (PositionFiber geometry)
      (basePoint geometry)
cell geometry height =
  Unbounded.cell geometry
    Bridge.toOrdinal height

cell-nontrivial :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
    (height : Nat.ℕ)
  → cell geometry height
      Cubical.≡
    Iterated.iteratedLoopPoint (Nat.suc height)
      (PositionFiber geometry)
      (basePoint geometry)
  → ⊥
cell-nontrivial geometry height =
  Unbounded.cell-nontrivial geometry
    Bridge.toOrdinal height

-- PositionFiber(G) has no finite h-level, q′_G has none as a map, and q′_G
-- is not an embedding.

positionFiber-not-finite-hlevel :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
    (height : Nat.ℕ)
  → HLevels.isOfHLevel height
      (PositionFiber geometry)
  → ⊥
positionFiber-not-finite-hlevel geometry height =
  Unbounded.fiber-not-finite-hlevel geometry
    Bridge.toOrdinal height

projection-not-finite-hlevel :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
    (height : Nat.ℕ)
  → HLevels.isOfHLevelFun height
      (projection geometry)
  → ⊥
projection-not-finite-hlevel geometry height =
  Unbounded.projection-not-finite-hlevel geometry
    Bridge.toOrdinal height

projection-not-embedding :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
  → Embedding.isEmbedding
      (projection geometry)
  → ⊥
projection-not-embedding geometry embedding =
  projection-not-finite-hlevel
    geometry (Nat.suc Nat.zero)
    (Embedding.isEmbedding→hasPropFibers embedding)
