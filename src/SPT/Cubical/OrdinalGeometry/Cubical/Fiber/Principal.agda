{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Principal
  where

-- Spaces of presentations of a principal segment, untruncated:
-- Presentations(H,h) = Σ P. ord(P) ≃ H ↓ h.  The point of ω₁ᴳ(G) whose
-- principal segment is the one-point order, and its space of presentations.
-- The calibration, the retraction and the higher cells are in submodules,
-- each normalized separately.

open import Agda.Primitive using (Level; lsuc; _⊔_)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType as Reflection
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Base as Omega
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Position
  as Position

import Cubical.Foundations.Prelude as Cubical
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- Presentations of a principal segment

-- Presentations(H,h) = Σ(P : CountableOrdinal𝒫). ord(P) ≃ H ↓ h.  Unlike
-- MerelyPresented, nothing is truncated.

Presentations :
    ∀ {presentation-level target-level}
  → (H : Woset.Woset target-level presentation-level)
  → Cubical.fst H
  → Set (lsuc presentation-level ⊔ target-level)
Presentations {presentation-level} H point =
  Cubical.Σ
    (Presented.CountableOrdinal𝒫 presentation-level)
    (λ presentation →
      Woset.WosetEquiv
        (Reflection.orderType presentation)
        (Simulation._↓_ H point))

------------------------------------------------------------------------
-- The one-point segment

-- The one-point order lies strictly below ω₁ᴳ(G); `unitPoint` bounds it and
-- `unitSegment` is its principal segment.

abstract
  unit-strict :
      (geometry : Presented.𝒫ω₁𝒢 ℓ)
    → Simulation._≺_
        (Position.UnitOrderType ℓ)
        (Omega.ω₁ᴳ geometry)
  unit-strict geometry =
    Omega.orderType-strictᴳ
      geometry Position.unitPresentation

unitPoint :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → Cubical.fst (Omega.ω₁ᴳ geometry)
unitPoint geometry =
  Cubical.fst (unit-strict geometry)

unitSegment :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → Woset.Woset (lsuc ℓ) ℓ
unitSegment geometry =
  Simulation._↓_
    (Omega.ω₁ᴳ geometry)
    (unitPoint geometry)

-- UnitPresentations(G) = Presentations(ω₁ᴳ(G), unitPoint(G)).

UnitPresentations :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → Set _
UnitPresentations geometry =
  Presentations
    (Omega.ω₁ᴳ geometry)
    (unitPoint geometry)
