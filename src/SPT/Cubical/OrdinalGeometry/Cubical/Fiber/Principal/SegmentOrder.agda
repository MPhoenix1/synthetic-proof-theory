{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Principal.SegmentOrder
  where

-- The order of unitSegment(G) is empty.

open import Agda.Primitive using (Level)
open import Data.Empty using (⊥)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Principal
  as Principal
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Principal.UnitOrder
  as UnitOrder

import Cubical.Foundations.Equiv as CubicalEquiv
import Cubical.Foundations.Prelude as Cubical
import Cubical.Relation.Binary.Order.Woset.Base as Woset

private
  variable
    ℓ : Level

-- No x < y in unitSegment(G): the equivalence with the one-point order
-- would send it to a comparison there.

segment-strict-empty :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (left right :
      Cubical.fst (Principal.unitSegment geometry))
  → Woset.WosetStr._≺_
      (Cubical.snd (Principal.unitSegment geometry))
      left right
  → ⊥
segment-strict-empty {ℓ} geometry left right strict =
  UnitOrder.unitOrderType-strict-empty
    (CubicalEquiv.equivFun
      (Cubical.fst
        (Cubical.snd
          (Principal.unit-strict geometry)))
      left)
    (CubicalEquiv.equivFun
      (Cubical.fst
        (Cubical.snd
          (Principal.unit-strict geometry)))
      right)
    (CubicalEquiv.equivFun
      (Woset.IsWosetEquiv.pres≺
        (Cubical.snd
          (Cubical.snd
            (Principal.unit-strict geometry)))
        left right)
      strict)
