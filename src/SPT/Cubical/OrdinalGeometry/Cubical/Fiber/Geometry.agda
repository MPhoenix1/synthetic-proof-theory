{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Geometry
  where

-- The map G ↦ ω₁ᴳ(G) from geometries to well-orders is not an embedding.
-- Two geometries that differ only in their diagonal field (the second
-- raises every diagonal upper bound once more) are not equal, while their
-- well-orders are equal by uniqueness.  So the fiber over ω₁ is not a
-- proposition, nor contractible.

open import Agda.Primitive using (lzero)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero)
open import Data.Product using (_,_; proj₁; proj₂)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Base as Omega
import
  SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Specification
  as Specification

import Cubical.Foundations.Prelude as Cubical
import Cubical.Functions.Embedding as Embedding

------------------------------------------------------------------------
-- A family to observe the diagonal

-- The empty presentation and the constant family at it, used to observe
-- the diagonal field of a geometry.

emptyPresentation : Presented.CountableOrdinal𝒫 lzero
emptyPresentation = record
  { X = ⊥
  ; _≈_ = λ _ _ → ⊥
  ; _<_ = λ _ _ → ⊥
  ; ≈-refl = λ ()
  ; ≈-sym = λ equivalent → ⊥-elim equivalent
  ; ≈-trans = λ equivalent → ⊥-elim equivalent
  ; <-trans = λ strict → ⊥-elim strict
  ; <-respˡ-≈ = λ equivalent strict → ⊥-elim strict
  ; <-respʳ-≈ = λ equivalent strict → ⊥-elim strict
  ; <-wf = λ ()
  ; compare = λ ()
  ; enum = λ _ → nothing
  ; covers = λ ()
  }

emptyFamily : ℕ → Presented.CountableOrdinal𝒫 lzero
emptyFamily _ = emptyPresentation

------------------------------------------------------------------------
-- A raised diagonal

-- From the diagonal (U , u) of a family, the diagonal U⁺ of the constant
-- family at U: each member lies below U, and U below U⁺.  This is a second
-- strict upper bound, not a least one.

raisedDiagonal :
    ∀ {ℓ}
  → (family : ℕ → Presented.CountableOrdinal𝒫 ℓ)
  → Presented.Diagonal.Upper family
raisedDiagonal family =
  Presented.Diagonal.𝒫 (λ _ → upper)
  , λ index →
      Presented.Embedding.trans
        (proj₂ selected index)
        upper<raised
  where
    selected : Presented.Diagonal.Upper family
    selected = Presented.Diagonal.upper family

    upper : Presented.CountableOrdinal𝒫 _
    upper = proj₁ selected

    upper<raised :
      Presented._≺𝒫_
        upper
        (Presented.Diagonal.𝒫 (λ _ → upper))
    upper<raised =
      Presented.Diagonal.member (λ _ → upper) zero

------------------------------------------------------------------------
-- Two distinct geometries

canonicalGeometry :
  Presented.𝒫ω₁𝒢 lzero
canonicalGeometry = Presented.ω₁.Geometry.canonical

-- The canonical geometry with its diagonal field replaced by the raised
-- diagonal; the other three fields are unchanged.

raisedGeometry :
  Presented.𝒫ω₁𝒢 lzero
raisedGeometry = record
  { upper =
      Presented.𝒫ω₁𝒢.upper canonicalGeometry
  ; spectrum =
      Presented.𝒫ω₁𝒢.spectrum canonicalGeometry
  ; diagonal =
      raisedDiagonal
  ; noCover =
      Presented.𝒫ω₁𝒢.noCover canonicalGeometry
  }

canonicalDiagonal : Presented.Diagonal.Upper emptyFamily
canonicalDiagonal =
  Presented.𝒫ω₁𝒢.diagonal canonicalGeometry emptyFamily

canonicalDiagonal<raised :
  Presented._≺𝒫_
    (proj₁ canonicalDiagonal)
    (proj₁
      (Presented.𝒫ω₁𝒢.diagonal
        raisedGeometry emptyFamily))
canonicalDiagonal<raised =
  Presented.Diagonal.member
    (λ _ → proj₁ canonicalDiagonal)
    zero

-- The two geometries are not equal: a path would give a path between their
-- diagonals at the empty family, and transporting the strict embedding of U
-- into U⁺ along it would give a strict self-embedding.

canonical≢raised :
  (canonicalGeometry Cubical.≡ raisedGeometry) → ⊥
canonical≢raised geometry-equality =
  Presented.Embedding.irrefl
    (proj₁ canonicalDiagonal)
    (Cubical.subst
      (Presented._≺𝒫_ (proj₁ canonicalDiagonal))
      (Cubical.sym upper-equality)
      canonicalDiagonal<raised)
  where
    upper-equality :
      proj₁ canonicalDiagonal Cubical.≡
      proj₁
        (Presented.𝒫ω₁𝒢.diagonal
          raisedGeometry emptyFamily)
    upper-equality =
      Cubical.cong
        (λ geometry →
          proj₁
            (Presented.𝒫ω₁𝒢.diagonal geometry emptyFamily))
        geometry-equality

------------------------------------------------------------------------
-- Equal well-orders and the fiber

-- Their well-orders are equal, by uniqueness (Specification).

outputs-equal :
  Omega.ω₁ᴳ canonicalGeometry Cubical.≡
  Omega.ω₁ᴳ raisedGeometry
outputs-equal =
  Specification.pathᴳ
    canonicalGeometry raisedGeometry

-- The fiber of G ↦ ω₁ᴳ(G) over the canonical output,
--
--   GeometryFiber = Σ(G : 𝒫ω₁𝒢 0). ω₁ᴳ(G) = ω₁ᴳ(G₀),
--
-- with the two points given by the two geometries.

GeometryFiber : Set₂
GeometryFiber =
  Cubical.Σ
    (Presented.𝒫ω₁𝒢 lzero)
    (λ geometry →
      Omega.ω₁ᴳ geometry Cubical.≡
      Omega.ω₁ᴳ canonicalGeometry)

canonicalPoint : GeometryFiber
canonicalPoint = canonicalGeometry Cubical., Cubical.refl

raisedPoint : GeometryFiber
raisedPoint =
  raisedGeometry Cubical., Cubical.sym outputs-equal

canonicalPoint≢raisedPoint :
  (canonicalPoint Cubical.≡
    raisedPoint)
  → ⊥
canonicalPoint≢raisedPoint fiber-equality =
  canonical≢raised
    (Cubical.cong Cubical.fst fiber-equality)

-- The fiber is not a proposition and not contractible, so G ↦ ω₁ᴳ(G) is not
-- an embedding.  No nontrivial loop is constructed here.

geometryFiber-not-prop :
  Cubical.isProp GeometryFiber → ⊥
geometryFiber-not-prop proposition =
  canonicalPoint≢raisedPoint
    (proposition
      canonicalPoint
      raisedPoint)

ω₁ᴳ-not-embedding :
  Embedding.isEmbedding
    (Omega.ω₁ᴳ {lzero}) → ⊥
ω₁ᴳ-not-embedding embedding =
  geometryFiber-not-prop
    (Embedding.isEmbedding→hasPropFibers embedding
      (Omega.ω₁ᴳ canonicalGeometry))

geometryFiber-not-contractible :
  Cubical.isContr GeometryFiber → ⊥
geometryFiber-not-contractible contraction =
  canonicalPoint≢raisedPoint
    (Cubical.sym
      (Cubical.snd contraction canonicalPoint)
      Cubical.∙
     Cubical.snd contraction raisedPoint)
