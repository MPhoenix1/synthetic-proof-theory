{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Principal.CollapsedOrder
  where

-- ord(collapsed(T , base)) ≃ UnitOrderType, from collapsed ≃𝒫 unit.

open import Agda.Primitive using (Level)

import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType as Reflection
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Position
  as Position

import Cubical.Relation.Binary.Order.Woset.Base as Woset

private
  variable
    ℓ : Level

-- ord(collapsed(T,base)) ≃ UnitOrderType.

abstract
  collapsed-unitOrderType :
      (T : Set ℓ)
      (base : T)
    → Woset.WosetEquiv
        (Reflection.orderType
          (Position.collapsed T base))
        (Position.UnitOrderType ℓ)
  collapsed-unitOrderType T base =
    Reflection.orderType-equivalence
      (Position.collapsed-unit T base)
