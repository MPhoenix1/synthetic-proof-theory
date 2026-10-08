{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Principal.UnitCalibration
  where

-- UnitOrderType ≃ unitSegment(G), from the carrier equivalence of
-- UnitCarrier and the emptiness of both orders.

open import Agda.Primitive using (Level)
open import Data.Empty using (⊥-elim)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Position
  as Position
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Principal
  as Principal
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Principal.SegmentOrder
  as PrincipalOrder
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Principal.UnitCarrier
  as UnitCarrier
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Principal.UnitOrder
  as UnitOrder

import Cubical.Foundations.Equiv as CubicalEquiv
import Cubical.Foundations.Prelude as Cubical
import Cubical.Relation.Binary.Order.Woset.Base as Woset

private
  variable
    ℓ : Level

-- UnitOrderType ≃ unitSegment(G): the carrier equivalence inverted, and the
-- order laws hold because both orders are empty.

abstract
  unitOrderType-unitSegment :
      (geometry : Presented.𝒫ω₁𝒢 ℓ)
    → Woset.WosetEquiv
        (Position.UnitOrderType ℓ)
        (Principal.unitSegment geometry)
  unitOrderType-unitSegment {ℓ} geometry =
    UnitCarrier.unitCarrier-equivalence geometry
    Cubical.,
    Woset.iswosetequiv
      (λ left right →
        CubicalEquiv.propBiimpl→Equiv
          (Woset.WosetStr.is-prop-valued
            (Cubical.snd (Position.UnitOrderType ℓ)) left right)
          (Woset.WosetStr.is-prop-valued
            (Cubical.snd
              (Principal.unitSegment geometry))
            (CubicalEquiv.equivFun
              (UnitCarrier.unitCarrier-equivalence geometry)
              left)
            (CubicalEquiv.equivFun
              (UnitCarrier.unitCarrier-equivalence geometry)
              right))
          (λ strict →
            ⊥-elim
              (UnitOrder.unitOrderType-strict-empty left right strict))
          (λ strict →
            ⊥-elim
              (PrincipalOrder.segment-strict-empty geometry
                (CubicalEquiv.equivFun
                  (UnitCarrier.unitCarrier-equivalence
                    geometry)
                  left)
                (CubicalEquiv.equivFun
                  (UnitCarrier.unitCarrier-equivalence
                    geometry)
                  right)
                strict)))
