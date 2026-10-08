{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Principal.Calibration
  where

-- ord(collapsed(T , base)) ≃ unitSegment(G), composed from the two
-- equivalences of PresentationCalibration and UnitCalibration.

open import Agda.Primitive using (Level)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType as Reflection
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Position
  as Position
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Principal
  as Principal
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Principal.CollapsedOrder
  as PresentationCalibration
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Principal.UnitCalibration
  as UnitCalibration

import Cubical.Relation.Binary.Order.Woset.Base as Woset

private
  variable
    ℓ : Level

-- ord(collapsed(T,base)) ≃ UnitOrderType ≃ unitSegment(G).

abstract
  collapsed-unitSegment :
      (geometry : Presented.𝒫ω₁𝒢 ℓ)
      (T : Set ℓ)
      (base : T)
    → Woset.WosetEquiv
        (Reflection.orderType
          (Position.collapsed T base))
        (Principal.unitSegment geometry)
  collapsed-unitSegment geometry T base =
    Woset.compWosetEquiv
      (PresentationCalibration.collapsed-unitOrderType T base)
      (UnitCalibration.unitOrderType-unitSegment geometry)
