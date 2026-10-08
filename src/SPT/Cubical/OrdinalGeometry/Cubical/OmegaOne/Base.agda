{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Base where

-- ω₁ as a supremum: for an ω₁ geometry G, ω₁ᴳ(G) is the supremum of the
-- order types ord(P) of all positions (P , route) of G, a well-order with
-- carrier one universe up.  Every ord(P) lies strictly below it, and it is
-- least among well-orders above every ord(P).  ω₁ is ω₁ᴳ at the canonical
-- geometry.

open import Agda.Primitive using (Level; lsuc)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
import SPT.Cubical.OrdinalGeometry.Presentation.Successor as Successor
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType as Reflection
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Successor
  as SuccessorReflection

import Cubical.Foundations.Prelude as Cubical
import Cubical.HITs.PropositionalTruncation as Truncation
import Cubical.HITs.SetQuotients as Quotient
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- The order types of the positions

-- A position (P , route) is sent to ord(P); the route is part of the index
-- of the supremum, but only P determines the order type.

module 𝒫ω₁ where

  positionOrderType :
      (geometry : Presented.𝒫ω₁𝒢 ℓ)
    → Presented.ω₁.Geometry.Position geometry
    → Woset.Woset ℓ ℓ
  positionOrderType geometry position =
    Reflection.orderType (Cubical.fst position)

------------------------------------------------------------------------
-- The supremum over the positions of a geometry

-- ω₁ᴳ(G) = sup((P , route) ↦ ord(P)), with its upper-bound and leastness
-- laws.  The cut is proved in Cut and Specification.

ω₁ᴳ :
    Presented.𝒫ω₁𝒢 ℓ
  → Woset.Woset (lsuc ℓ) ℓ
ω₁ᴳ geometry =
  Cubical.fst
    (Simulation.sup
      (𝒫ω₁.positionOrderType geometry))

position-upperᴳ :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (position : Presented.ω₁.Geometry.Position geometry)
  → Simulation._≼_
      (𝒫ω₁.positionOrderType geometry position)
      (ω₁ᴳ geometry)
position-upperᴳ geometry =
  Cubical.fst
    (Cubical.snd
      (Simulation.sup
        (𝒫ω₁.positionOrderType geometry)))

upperᴳ :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
  → Simulation._≼_
      (Reflection.orderType presentation)
      (ω₁ᴳ geometry)
upperᴳ geometry presentation =
  position-upperᴳ
    geometry
    (Presented.ω₁.Geometry.position geometry presentation)

leastᴳ :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (upper : Woset.Woset ℓ ℓ)
  → ((position : Presented.ω₁.Geometry.Position geometry) →
      Simulation._≼_
        (𝒫ω₁.positionOrderType geometry position)
        upper)
  → Simulation._≼_ (ω₁ᴳ geometry) upper
leastᴳ geometry =
  Cubical.snd
    (Cubical.snd
      (Simulation.sup
        (𝒫ω₁.positionOrderType geometry)))

position-point-strictᴳ :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (position : Presented.ω₁.Geometry.Position geometry)
    (point :
      Cubical.fst
        (𝒫ω₁.positionOrderType geometry position))
  → Simulation._≺_
      (Simulation._↓_
        (𝒫ω₁.positionOrderType geometry position)
        point)
      (ω₁ᴳ geometry)
position-point-strictᴳ
    geometry position point =
  Simulation.≺Trans≼
    (Simulation._↓_
      (𝒫ω₁.positionOrderType geometry position)
      point)
    (𝒫ω₁.positionOrderType geometry position)
    (ω₁ᴳ geometry)
    (Simulation.↓Decreasing
      (𝒫ω₁.positionOrderType geometry position)
      point)
    (position-upperᴳ geometry position)

-- ord(P) ≺ ω₁ᴳ(G) for every presentation P: the successor P + 1 has a
-- position in G, and ord(P) is a principal segment of ord(P + 1).

orderType-strictᴳ :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
  → Simulation._≺_
      (Reflection.orderType presentation)
      (ω₁ᴳ geometry)
orderType-strictᴳ
    geometry presentation =
  Simulation.≺Trans≼
    (Reflection.orderType presentation)
    (Reflection.orderType
      (Successor.successor presentation))
    (ω₁ᴳ geometry)
    (SuccessorReflection.successor-strict
      presentation)
    (upperᴳ
      geometry
      (Successor.successor presentation))

-- Every point of ω₁ᴳ(G) comes from a point of some ord(P), at a position:
--
--   Representativeᴳ(G,q) = Σ(position). Σ(x : ord(P)). upper(position)(x) = q.

Representativeᴳ :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (point : Cubical.fst (ω₁ᴳ geometry))
  → Set (lsuc ℓ)
Representativeᴳ geometry point =
  Cubical.Σ
    (Presented.ω₁.Geometry.Position geometry)
    (λ position →
      Cubical.Σ
        (Cubical.fst
          (𝒫ω₁.positionOrderType geometry position))
        (λ family-point →
          Cubical.fst
            (position-point-strictᴳ
              geometry position family-point)
          Cubical.≡ point))

point-coveredᴳ :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (point : Cubical.fst (ω₁ᴳ geometry))
  → Truncation.∥
      Representativeᴳ geometry point
    ∥₁
point-coveredᴳ geometry point =
  Truncation.map
    (λ representative →
      Cubical._,_
        (Cubical.fst (Cubical.fst representative))
        (Cubical._,_
          (Cubical.snd (Cubical.fst representative))
          (Cubical.snd representative)))
    (Quotient.[]surjective point)

------------------------------------------------------------------------
-- The canonical geometry

ω₁ : (level : Level) → Woset.Woset (lsuc level) level
ω₁ level =
  ω₁ᴳ
    (Presented.ω₁.Geometry.canonical {level})

-- ω₁ is ω₁ᴳ at the canonical geometry; the path is abstract, so that later
-- theorems transport along it instead of unfolding the geometry.

abstract
  ω₁-canonical :
      ω₁ᴳ
        (Presented.ω₁.Geometry.canonical {ℓ})
    Cubical.≡ ω₁ ℓ
  ω₁-canonical = Cubical.refl

position-upper :
    (position :
      Presented.ω₁.Geometry.Position
        (Presented.ω₁.Geometry.canonical {ℓ}))
  → Simulation._≼_
      (𝒫ω₁.positionOrderType
        Presented.ω₁.Geometry.canonical
        position)
      (ω₁ ℓ)
position-upper {ℓ} =
  position-upperᴳ
    (Presented.ω₁.Geometry.canonical {ℓ})

upper :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
  → Simulation._≼_
      (Reflection.orderType presentation)
      (ω₁ ℓ)
upper {ℓ} =
  upperᴳ
    (Presented.ω₁.Geometry.canonical {ℓ})

-- A point of ord(P) gives a principal segment strictly below ω₁.

position-point-strict :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
    (point : Cubical.fst (Reflection.orderType presentation))
  → Simulation._≺_
      (Simulation._↓_
        (Reflection.orderType presentation)
        point)
      (ω₁ ℓ)
position-point-strict {ℓ} presentation point =
  Simulation.≺Trans≼
    (Simulation._↓_
      (Reflection.orderType presentation)
      point)
    (Reflection.orderType presentation)
    (ω₁ ℓ)
    (Simulation.↓Decreasing
      (Reflection.orderType presentation)
      point)
    (upper presentation)

Representative :
    (point : Cubical.fst (ω₁ ℓ))
  → Set (lsuc ℓ)
Representative {ℓ} =
  Representativeᴳ
    (Presented.ω₁.Geometry.canonical {ℓ})

point-covered :
    (point : Cubical.fst (ω₁ ℓ))
  → Truncation.∥ Representative point ∥₁
point-covered {ℓ} =
  point-coveredᴳ
    (Presented.ω₁.Geometry.canonical {ℓ})

-- Leastness: ord(P) ≼ γ for every P gives ω₁(ℓ) ≼ γ, for γ : Woset ℓ ℓ.
-- Leastness among well-orders of any carrier level is in Specification.

least :
    (upper : Woset.Woset ℓ ℓ)
  → ((presentation : Presented.CountableOrdinal𝒫 ℓ) →
      Simulation._≼_
        (Reflection.orderType presentation)
        upper)
  → Simulation._≼_ (ω₁ ℓ) upper
least {ℓ} upper presentation-upper =
  leastᴳ
    (Presented.ω₁.Geometry.canonical {ℓ})
    upper
    (λ position → presentation-upper (Cubical.fst position))

------------------------------------------------------------------------
-- Every presentation lies strictly below ω₁

-- ord(P) ≺ ω₁(ℓ).  The supremum only gives ord(P) ≼ ω₁; strictness comes
-- from P + 1, whose top bounds a principal segment equivalent to ord(P).

orderType-strict :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
  → Simulation._≺_
      (Reflection.orderType presentation)
      (ω₁ ℓ)
orderType-strict {ℓ} presentation =
  Simulation.≺Trans≼
    (Reflection.orderType presentation)
    (Reflection.orderType
      (Successor.successor presentation))
    (ω₁ ℓ)
    (SuccessorReflection.successor-strict
      presentation)
    (upper
      (Successor.successor presentation))
