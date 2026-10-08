{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Principal.UnitOrder
  where

-- The order of UnitOrderType is empty.

open import Agda.Primitive using (Level)
open import Data.Empty using (⊥)

import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Position
  as Position
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType as Reflection

import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Prelude as Cubical
import Cubical.HITs.PropositionalTruncation as Truncation
import Cubical.HITs.SetQuotients as Quotient

private
  variable
    ℓ : Level

  ordinary-empty-is-prop : Cubical.isProp ⊥
  ordinary-empty-is-prop ()

-- No [x] < [y] in ord(unitPresentation): after eliminating the quotient
-- and the truncation, a witness of the empty order remains.

unitOrderType-strict-empty :
    (left right :
      Reflection.Class
        (Position.unitPresentation {ℓ}))
  → Reflection.Less
      (Position.unitPresentation {ℓ}) left right
  → ⊥
unitOrderType-strict-empty {ℓ} =
  Quotient.elimProp2
    (λ left right →
      HLevels.isPropΠ λ _ → ordinary-empty-is-prop)
    (λ left right strict →
      Truncation.rec
        ordinary-empty-is-prop
        (λ ())
        (Reflection.Less-elim
          (Position.unitPresentation {ℓ}) strict))
