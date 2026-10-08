{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Postcomposed
  where

-- The pointed universe survives every postcomposition: for any map A out of
-- well-orders, the fiber of A ∘ q_G over A(1) still contains the pointed
-- small universe as a split retract.  Recovery reads the presentation of
-- the position, so it needs no property of A.

open import Agda.Primitive using (Level)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero)
open import Data.Unit.Polymorphic as PolyUnit using ()

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Position
  as Position
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.SplitEmbedding
  as Split

import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Prelude as Cubical
import Cubical.Relation.Binary.Order.Woset.Base as Woset

private
  variable
    ℓ ℓ-target : Level
    Target : Set ℓ-target

------------------------------------------------------------------------
-- The postcomposed projection and its fiber

-- A ∘ q_G for an arbitrary map A out of well-orders.

projection :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (adapter : Woset.Woset ℓ ℓ → Target)
  → Presented.ω₁.Geometry.Position geometry
  → Target
projection geometry adapter position =
  adapter
    (Position.projection geometry position)

-- PostcomposedFiber(G,A) = Σ(u : Position(G)). A(q_G(u)) = A(1).

PostcomposedFiber :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (adapter : Woset.Woset ℓ ℓ → Target)
  → Set _
PostcomposedFiber {ℓ} geometry adapter =
  Cubical.Σ
    (Presented.ω₁.Geometry.Position geometry)
    (λ position →
      projection geometry adapter position
        Cubical.≡
      adapter (Position.UnitOrderType ℓ))

-- A point (u , p) of PositionFiber(G, 1) gives (u , cong A p).

postcompose :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (adapter : Woset.Woset ℓ ℓ → Target)
  → Position.PositionFiber
      geometry (Position.UnitOrderType ℓ)
  → PostcomposedFiber geometry adapter
postcompose geometry adapter fiber-point =
  Cubical.fst fiber-point
  Cubical.,
  Cubical.cong adapter (Cubical.snd fiber-point)

------------------------------------------------------------------------
-- The pointed universe as a retract

retain :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (adapter : Woset.Woset ℓ ℓ → Target)
  → Position.PointedType ℓ
  → PostcomposedFiber geometry adapter
retain geometry adapter pointed =
  postcompose geometry adapter
    (Position.retain geometry pointed)

-- Recovery as in Position: the carrier of the presentation of u, pointed by
-- its entry at index 0; the route and the path are ignored.

recover :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (adapter : Woset.Woset ℓ ℓ → Target)
  → PostcomposedFiber geometry adapter
  → Position.PointedType ℓ
recover geometry adapter fiber-point
    with Presented.CountableOrdinal𝒫.enum
      (Cubical.fst (Cubical.fst fiber-point)) zero
... | nothing = PolyUnit.⊤ Cubical., PolyUnit.tt
... | just point =
  Presented.CountableOrdinal𝒫.X (Cubical.fst (Cubical.fst fiber-point))
  Cubical., point

-- recover (retain (T , base)) = (T , base), by refl.

recover-retain :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (adapter : Woset.Woset ℓ ℓ → Target)
    (pointed : Position.PointedType ℓ)
  → recover geometry adapter
      (retain
        geometry adapter pointed)
    Cubical.≡ pointed
recover-retain
    geometry adapter (T Cubical., base) = Cubical.refl

-- The pointed small universe is a split retract of the fiber of A ∘ q_G
-- over A(1).

universeEmbedding :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (adapter : Woset.Woset ℓ ℓ → Target)
  → Split.SplitEmbedding
      (Position.PointedType ℓ)
      (PostcomposedFiber geometry adapter)
universeEmbedding geometry adapter =
  Split.split-embedding
    (retain geometry adapter)
    (recover geometry adapter)
    (recover-retain geometry adapter)

-- So an h-level bound on that fiber bounds the pointed universe.

reflects-hlevel :
    (height : ℕ)
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (adapter : Woset.Woset ℓ ℓ → Target)
  → HLevels.isOfHLevel height
      (PostcomposedFiber geometry adapter)
  → HLevels.isOfHLevel height (Position.PointedType ℓ)
reflects-hlevel
    height geometry adapter =
  HLevels.isOfHLevelRetract height
    (retain geometry adapter)
    (recover geometry adapter)
    (recover-retain geometry adapter)
