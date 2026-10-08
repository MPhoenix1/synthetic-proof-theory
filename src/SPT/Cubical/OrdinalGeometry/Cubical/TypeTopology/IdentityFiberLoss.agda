{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.IdentityFiberLoss
  where

-- The same loss in TypeTopology's own terms: the fiber of q′_G formed with
-- TypeTopology's Σ and identity type ＝ has no finite h-level in
-- TypeTopology's hierarchy (UF.HLevels, given univalence), and q′_G is not
-- an embedding in TypeTopology's sense.  Paths and ＝ are compared by
-- explicit maps and a retraction.

open import Agda.Primitive using (Level; lzero)
open import Data.Empty using (⊥)
import Data.Nat.Base as Nat

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Position
  as Position
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.SplitEmbedding
  as Split
import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Bridge as Bridge
import
  SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.PositionLoss
  as PositionLoss

import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Prelude as Cubical
import SPT.Cubical.TypeTopology.MLTT.Identity-Type as TypeTopologyIdentity
import SPT.Cubical.TypeTopology.MLTT.Sigma-Type as TypeTopologySigma
import SPT.Cubical.TypeTopology.Notation.General as TypeTopologyNotation
import SPT.Cubical.TypeTopology.UF.Embeddings as TypeTopologyEmbedding
import SPT.Cubical.TypeTopology.UF.HLevels as TypeTopologyHLevels
import SPT.Cubical.TypeTopology.UF.Univalence as TypeTopologyUnivalence

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- The identity fiber

-- PositionIdentityFiber(G) = Σ(u : Position(G)). q′_G(u) ＝ toOrdinal(1).

PositionIdentityFiber :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → Set _
PositionIdentityFiber {ℓ} geometry =
  TypeTopologyNotation.fiber
    (PositionLoss.projection geometry)
    (Bridge.toOrdinal
      (Position.UnitOrderType ℓ))

pathFiber→identityFiber :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → PositionLoss.PositionFiber geometry
  → PositionIdentityFiber geometry
pathFiber→identityFiber geometry fiber-point =
  TypeTopologySigma._,_
    (Cubical.fst fiber-point)
    (Bridge.path→＝ (Cubical.snd fiber-point))

identityFiber→pathFiber :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → PositionIdentityFiber geometry
  → PositionLoss.PositionFiber geometry
identityFiber→pathFiber geometry fiber-point =
  TypeTopologyNotation.fiber-point fiber-point
  Cubical.,
  Bridge.＝→path
    (TypeTopologyNotation.fiber-identification fiber-point)

identityFiber-retraction :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (fiber-point : PositionLoss.PositionFiber geometry)
  → identityFiber→pathFiber geometry
      (pathFiber→identityFiber geometry fiber-point)
      Cubical.≡ fiber-point
identityFiber-retraction
    geometry (position Cubical., path) =
  Cubical.cong
    (λ equality → position Cubical., equality)
    (Bridge.path→＝→path path)

pathFiber◁identityFiber :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → Split.SplitEmbedding
      (PositionLoss.PositionFiber geometry)
      (PositionIdentityFiber geometry)
pathFiber◁identityFiber geometry =
  Split.split-embedding
    (pathFiber→identityFiber geometry)
    (identityFiber→pathFiber geometry)
    (identityFiber-retraction geometry)

------------------------------------------------------------------------
-- No finite h-level

identityFiber-not-finite-hlevel :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
    (height : Nat.ℕ)
  → HLevels.isOfHLevel height
      (PositionIdentityFiber geometry)
  → ⊥
identityFiber-not-finite-hlevel
    geometry height identity-fiber-hlevel =
  PositionLoss.positionFiber-not-finite-hlevel
    geometry height
    (HLevels.isOfHLevelRetract height
      (pathFiber→identityFiber geometry)
      (identityFiber→pathFiber geometry)
      (identityFiber-retraction geometry)
      identity-fiber-hlevel)

-- For univalence ua and every h, PositionIdentityFiber(G) is not of
-- TypeTopology h-level h.  TypeTopology's height zero is proposition, which
-- is Cubical height one; the levels are compared by induction.

module HLevelComparison
    (ua : TypeTopologyUnivalence.Univalence) where

  open TypeTopologyHLevels ua using (_is-of-hlevel_)

  TT-hlevel→hlevel :
      (height : Nat.ℕ)
      (A : Set ℓ)
    → A is-of-hlevel height
    → HLevels.isOfHLevel (Nat.suc height) A
  TT-hlevel→hlevel Nat.zero A proposition left right =
    Bridge.＝→path (proposition left right)
  TT-hlevel→hlevel
      (Nat.suc height) A truncated left right =
    HLevels.isOfHLevelRetract (Nat.suc height)
      Bridge.path→＝
      Bridge.＝→path
      Bridge.path→＝→path
      (TT-hlevel→hlevel height
        (TypeTopologyIdentity._＝_ left right)
        (truncated left right))

  identityFiber-not-finite-TT-hlevel :
      (geometry : Presented.𝒫ω₁𝒢 lzero)
      (height : Nat.ℕ)
    → PositionIdentityFiber geometry is-of-hlevel height
    → ⊥
  identityFiber-not-finite-TT-hlevel
      geometry height identity-fiber-hlevel =
    identityFiber-not-finite-hlevel
      geometry (Nat.suc height)
      (TT-hlevel→hlevel height
        (PositionIdentityFiber geometry)
        identity-fiber-hlevel)

open HLevelComparison public

projection-not-TT-embedding :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
  → TypeTopologyEmbedding.is-embedding
      (PositionLoss.projection geometry)
  → ⊥
projection-not-TT-embedding
    geometry embedding =
  identityFiber-not-finite-hlevel
    geometry (Nat.suc Nat.zero)
    (λ left right →
      Bridge.＝→path
        (embedding
          (Bridge.toOrdinal
            (Position.UnitOrderType lzero))
          left right))
