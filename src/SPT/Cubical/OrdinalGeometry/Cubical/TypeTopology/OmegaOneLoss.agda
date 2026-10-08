{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.OmegaOneLoss
  where

-- The ω₁ of a geometry as a TypeTopology ordinal, ω₁ᴳ′(G), and its loss:
-- the map G ↦ ω₁ᴳ′(G) identifies the two distinct geometries of
-- Fiber.Geometry, so it is not an embedding, with paths or with ＝.

open import Agda.Primitive using (Level; lzero; lsuc)
open import Data.Empty using (⊥)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Base as Omega
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Geometry
  as GeometryLoss
import
  SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Specification
  as Specification
import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Bridge as Bridge

import Cubical.Foundations.Prelude as Cubical
import Cubical.Functions.Embedding as CubicalEmbedding
import SPT.Cubical.TypeTopology.MLTT.Identity-Type as TypeTopologyIdentity
import SPT.Cubical.TypeTopology.MLTT.Sigma-Type as TypeTopologySigma
import SPT.Cubical.TypeTopology.Notation.General as TypeTopologyNotation
import SPT.Cubical.TypeTopology.Ordinals.Type as TypeTopologyOrdinal
import SPT.Cubical.TypeTopology.UF.Embeddings as TypeTopologyEmbedding
import SPT.Cubical.TypeTopology.UF.Subsingletons as TypeTopologyPropositions

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- ω₁ as a TypeTopology ordinal

-- ω₁ᴳ′(G) = smallToOrdinal(ω₁ᴳ(G)) : Ordinal(lsuc ℓ), and ω₁′.

ω₁ᴳ′ :
    Presented.𝒫ω₁𝒢 ℓ
  → TypeTopologyOrdinal.Ordinal (lsuc ℓ)
ω₁ᴳ′ geometry =
  Bridge.smallToOrdinal
    (Omega.ω₁ᴳ geometry)

ω₁′ :
  (level : Level) → TypeTopologyOrdinal.Ordinal (lsuc level)
ω₁′ level =
  Bridge.smallToOrdinal
    (Omega.ω₁ level)

------------------------------------------------------------------------
-- Independence of the geometry

-- ω₁ᴳ′(G) = ω₁ᴳ′(H) for any two geometries, as a path and as ＝.

ω₁ᴳ′-path :
    (left right : Presented.𝒫ω₁𝒢 ℓ)
  → ω₁ᴳ′ left Cubical.≡
    ω₁ᴳ′ right
ω₁ᴳ′-path left right =
  Cubical.cong Bridge.smallToOrdinal
    (Specification.pathᴳ left right)

ω₁ᴳ′-identity :
    (left right : Presented.𝒫ω₁𝒢 ℓ)
  → TypeTopologyIdentity._＝_
      (ω₁ᴳ′ left)
      (ω₁ᴳ′ right)
ω₁ᴳ′-identity left right =
  Bridge.path→＝
    (ω₁ᴳ′-path left right)

------------------------------------------------------------------------
-- The fibers of G ↦ ω₁ᴳ′(G)

-- The Cubical homotopy fiber, and TypeTopology's `fiber` built from its own
-- Σ and ＝.

GeometryPathFiber : Set _
GeometryPathFiber =
  Cubical.Σ
    (Presented.𝒫ω₁𝒢 lzero)
    (λ geometry →
      ω₁ᴳ′ geometry Cubical.≡
      ω₁ᴳ′ GeometryLoss.canonicalGeometry)

GeometryIdentityFiber : Set _
GeometryIdentityFiber =
  TypeTopologyNotation.fiber
    (ω₁ᴳ′ {lzero})
    (ω₁ᴳ′ GeometryLoss.canonicalGeometry)

canonicalPathPoint :
  GeometryPathFiber
canonicalPathPoint =
  GeometryLoss.canonicalGeometry Cubical., Cubical.refl

raisedPathPoint :
  GeometryPathFiber
raisedPathPoint =
  GeometryLoss.raisedGeometry
  Cubical.,
  ω₁ᴳ′-path
    GeometryLoss.raisedGeometry
    GeometryLoss.canonicalGeometry

canonicalIdentityPoint :
  GeometryIdentityFiber
canonicalIdentityPoint =
  TypeTopologyNotation.to-fiber
    (ω₁ᴳ′ {lzero})
    GeometryLoss.canonicalGeometry

raisedIdentityPoint :
  GeometryIdentityFiber
raisedIdentityPoint =
  TypeTopologySigma._,_
    GeometryLoss.raisedGeometry
    (ω₁ᴳ′-identity
      GeometryLoss.raisedGeometry
      GeometryLoss.canonicalGeometry)

canonical≠raised-path :
    canonicalPathPoint Cubical.≡
    raisedPathPoint
  → ⊥
canonical≠raised-path fiber-path =
  GeometryLoss.canonical≢raised
    (Cubical.cong Cubical.fst fiber-path)

canonical≠raised-identity :
    canonicalIdentityPoint Cubical.≡
    raisedIdentityPoint
  → ⊥
canonical≠raised-identity fiber-path =
  GeometryLoss.canonical≢raised
    (Cubical.cong TypeTopologyNotation.fiber-point fiber-path)

------------------------------------------------------------------------
-- Loss

-- Neither fiber is a proposition, in either library, and G ↦ ω₁ᴳ′(G) is
-- not an embedding: the two geometries of Fiber.Geometry differ but have
-- the same ordinal.

geometryPathFiber-not-prop :
  Cubical.isProp GeometryPathFiber → ⊥
geometryPathFiber-not-prop proposition =
  canonical≠raised-path
    (proposition canonicalPathPoint raisedPathPoint)

geometryIdentityFiber-not-prop :
  Cubical.isProp GeometryIdentityFiber → ⊥
geometryIdentityFiber-not-prop proposition =
  canonical≠raised-identity
    (proposition
      canonicalIdentityPoint
      raisedIdentityPoint)

geometryIdentityFiber-not-TT-prop :
  TypeTopologyPropositions.is-prop
    GeometryIdentityFiber
  → ⊥
geometryIdentityFiber-not-TT-prop
    proposition =
  canonical≠raised-identity
    (Bridge.＝→path
      (proposition
        canonicalIdentityPoint
        raisedIdentityPoint))

ω₁ᴳ′-not-embedding :
  CubicalEmbedding.isEmbedding
    (ω₁ᴳ′ {lzero})
  → ⊥
ω₁ᴳ′-not-embedding embedding =
  geometryPathFiber-not-prop
    (CubicalEmbedding.isEmbedding→hasPropFibers embedding
      (ω₁ᴳ′ GeometryLoss.canonicalGeometry))

ω₁ᴳ′-not-TT-embedding :
  TypeTopologyEmbedding.is-embedding
    (ω₁ᴳ′ {lzero})
  → ⊥
ω₁ᴳ′-not-TT-embedding embedding =
  geometryIdentityFiber-not-TT-prop
    (embedding
      (ω₁ᴳ′ GeometryLoss.canonicalGeometry))

geometryPathFiber-not-contractible :
  Cubical.isContr GeometryPathFiber → ⊥
geometryPathFiber-not-contractible contraction =
  canonical≠raised-path
    (Cubical.sym
      (Cubical.snd contraction canonicalPathPoint)
    Cubical.∙
      Cubical.snd contraction raisedPathPoint)
