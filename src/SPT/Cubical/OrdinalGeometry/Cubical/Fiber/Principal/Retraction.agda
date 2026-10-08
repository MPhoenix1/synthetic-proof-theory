{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Principal.Retraction
  where

-- The pointed small universe is a split retract of UnitPresentations(G):
-- retain(T , base) is the collapsed presentation with its calibration, and
-- recovery reads the carrier and the entry at index 0.

open import Agda.Primitive using (Level)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero)
open import Data.Unit.Polymorphic as PolyUnit using ()

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Position
  as Position
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Principal
  as Principal
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Principal.Calibration
  as Calibration

import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Prelude as Cubical

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- Retract

-- retain(T,base) = (collapsed(T,base), calibration).

retain :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → Position.PointedType ℓ
  → Principal.UnitPresentations geometry
retain geometry (T Cubical., base) =
  Position.collapsed T base
  Cubical.,
  Calibration.collapsed-unitSegment geometry T base

-- recover(P,e): the carrier of P pointed by its entry at index 0, or the
-- unit type if there is none; e is ignored.

recover :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → Principal.UnitPresentations geometry
  → Position.PointedType ℓ
recover geometry represented
    with Presented.CountableOrdinal𝒫.enum (Cubical.fst represented) zero
... | nothing = PolyUnit.⊤ Cubical., PolyUnit.tt
... | just point =
  Presented.CountableOrdinal𝒫.X (Cubical.fst represented) Cubical., point

-- recover (retain (T,base)) = (T,base), by refl.

recover-retain :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (pointed : Position.PointedType ℓ)
  → recover geometry
      (retain geometry pointed)
    Cubical.≡ pointed
recover-retain
  geometry (T Cubical., base) = Cubical.refl

------------------------------------------------------------------------
-- Consequences

reflects-hlevel :
    (height : ℕ)
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → HLevels.isOfHLevel height
      (Principal.UnitPresentations geometry)
  → HLevels.isOfHLevel height (Position.PointedType ℓ)
reflects-hlevel height geometry =
  HLevels.isOfHLevelRetract height
    (retain geometry)
    (recover geometry)
    (recover-retain geometry)

-- Recovery also recovers paths: cong recover (cong retain p) = p.

recover-retain-path :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    {left right : Position.PointedType ℓ}
    (path : left Cubical.≡ right)
  → Cubical.cong
      (recover geometry)
      (Cubical.cong
        (retain geometry)
        path)
    Cubical.≡ path
recover-retain-path geometry {left} =
  Cubical.J
    (λ right path →
      Cubical.cong
        (recover geometry)
        (Cubical.cong
          (retain geometry)
          path)
      Cubical.≡ path)
    Cubical.refl
