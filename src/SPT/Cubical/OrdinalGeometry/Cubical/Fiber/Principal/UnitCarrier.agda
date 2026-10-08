{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Principal.UnitCarrier
  where

-- The carrier equivalence |UnitOrderType| ≃ |unitSegment(G)|.

open import Agda.Primitive using (Level)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Position
  as Position
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Principal
  as Principal

import Cubical.Foundations.Equiv as CubicalEquiv
import Cubical.Foundations.Prelude as Cubical

private
  variable
    ℓ : Level

-- The inverse of the carrier equivalence of the strict witness for the
-- one-point order; no order law is stated here.

abstract
  unitCarrier-equivalence :
      (geometry : Presented.𝒫ω₁𝒢 ℓ)
    → Cubical.fst (Position.UnitOrderType ℓ)
        CubicalEquiv.≃
      Cubical.fst (Principal.unitSegment geometry)
  unitCarrier-equivalence geometry =
    CubicalEquiv.invEquiv
      (Cubical.fst
        (Cubical.snd
          (Principal.unit-strict geometry)))
