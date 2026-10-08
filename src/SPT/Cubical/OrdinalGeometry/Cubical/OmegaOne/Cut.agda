{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Cut where

-- The cut of ω₁: a small well-order lies below ω₁ exactly when it is
-- merely presented,
--
--   α ≺ ω₁(ℓ) ⇔ ‖Σ P. ord(P) ≃ α‖,
--
-- constructively.  Every principal segment of ω₁ᴳ(G) is merely presented.

open import Agda.Primitive using (Level; lsuc; _⊔_)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.LowerCone as LowerCone
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType as Reflection
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Base as Omega

import Cubical.Data.Sigma.Base as Sigma
import Cubical.Foundations.Prelude as Cubical
import Cubical.HITs.PropositionalTruncation as Truncation
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- Merely presented well-orders

-- MerelyPresented(α) = ‖Σ(P : CountableOrdinal𝒫 ℓ). ord(P) ≃ α‖.

MerelyPresented :
    ∀ {presentation-level target-level}
  → Woset.Woset target-level presentation-level
  → Set (lsuc presentation-level ⊔ target-level)
MerelyPresented {presentation-level} ordinal =
  Truncation.∥
    Cubical.Σ
      (Presented.CountableOrdinal𝒫 presentation-level)
      (λ presentation →
        Woset.WosetEquiv
          (Reflection.orderType presentation)
          ordinal)
  ∥₁

isPropMerelyPresented :
    ∀ {presentation-level target-level}
    (ordinal : Woset.Woset target-level presentation-level)
  → Cubical.isProp (MerelyPresented ordinal)
isPropMerelyPresented ordinal = Truncation.isPropPropTrunc

------------------------------------------------------------------------
-- Principal segments of ω₁ are presented

private
  -- A point of ω₁ᴳ(G) comes from a point of ord(P) at some position; its
  -- principal segment is presented by the lower cone at that point.

  abstract
    segment-at-position :
        (geometry : Presented.𝒫ω₁𝒢 ℓ)
        (position : Presented.ω₁.Geometry.Position geometry)
        (point :
          Cubical.fst
            (Omega.𝒫ω₁.positionOrderType
              geometry position))
        (strict :
          Simulation._≺_
            (Simulation._↓_
              (Omega.𝒫ω₁.positionOrderType
                geometry position)
              point)
            (Omega.ω₁ᴳ geometry))
      → MerelyPresented
          (Simulation._↓_
            (Omega.ω₁ᴳ geometry)
            (Cubical.fst strict))
    segment-at-position
        {ℓ} geometry position point strict =
      Truncation.map
        (λ represented →
          Cubical._,_
            (Cubical.fst represented)
            (Woset.compWosetEquiv
              (Cubical.snd represented)
              (Woset.invWosetEquiv
                (Cubical.snd strict))))
        (LowerCone.segment-presented
          (Cubical.fst position)
          (Simulation._↓_
            (Omega.𝒫ω₁.positionOrderType
              geometry position)
            point)
          (Simulation.↓Decreasing
            (Omega.𝒫ω₁.positionOrderType
              geometry position)
            point))

abstract
  segment-presentedᴳ :
      (geometry : Presented.𝒫ω₁𝒢 ℓ)
      (point : Cubical.fst (Omega.ω₁ᴳ geometry))
    → MerelyPresented
        (Simulation._↓_
          (Omega.ω₁ᴳ geometry)
          point)
  segment-presentedᴳ {ℓ} geometry =
    λ point →
      Truncation.rec
        (isPropMerelyPresented
          (Simulation._↓_
            (Omega.ω₁ᴳ geometry)
            point))
        (λ representative →
          Cubical.subst
            (λ target →
              MerelyPresented
                (Simulation._↓_
                  (Omega.ω₁ᴳ geometry)
                  target))
            (Cubical.snd (Cubical.snd representative))
            (segment-at-position
              geometry
              (Cubical.fst representative)
              (Cubical.fst (Cubical.snd representative))
              (Omega.position-point-strictᴳ
                geometry
                (Cubical.fst representative)
                (Cubical.fst (Cubical.snd representative)))))
        (Omega.point-coveredᴳ geometry point)

private
  PrincipalPresented :
      Woset.Woset (lsuc ℓ) ℓ
    → Set (lsuc ℓ)
  PrincipalPresented order =
    (point : Cubical.fst order)
    → MerelyPresented (Simulation._↓_ order point)

segment-presented :
    (point : Cubical.fst (Omega.ω₁ ℓ))
  → MerelyPresented
      (Simulation._↓_ (Omega.ω₁ ℓ) point)
segment-presented {ℓ} =
  Cubical.subst
    PrincipalPresented
    Omega.ω₁-canonical
    (segment-presentedᴳ
      (Presented.ω₁.Geometry.canonical {ℓ}))

------------------------------------------------------------------------
-- The cut

strict→presented :
    (ordinal : Woset.Woset ℓ ℓ)
  → Simulation._≺_ ordinal (Omega.ω₁ ℓ)
  → MerelyPresented ordinal
strict→presented ordinal strict =
  Truncation.map
    (λ represented →
      Cubical._,_
        (Cubical.fst represented)
        (Woset.compWosetEquiv
          (Cubical.snd represented)
          (Cubical.snd strict)))
    (segment-presented (Cubical.fst strict))

presented→strict :
    (ordinal : Woset.Woset ℓ ℓ)
  → MerelyPresented ordinal
  → Simulation._≺_ ordinal (Omega.ω₁ ℓ)
presented→strict {ℓ} ordinal =
  Truncation.rec
    (Simulation.isPropValued≺ ordinal (Omega.ω₁ ℓ))
    (λ represented →
      Simulation.≺RespectsEquivL
        (Omega.ω₁ ℓ)
        (Cubical.snd represented)
        (Omega.orderType-strict
          (Cubical.fst represented)))

-- α ≺ ω₁(ℓ) ⇔ MerelyPresented(α), constructively.  Countability enters in
-- OmegaOne.Countability.

strict-cut :
    (ordinal : Woset.Woset ℓ ℓ)
  → (Simulation._≺_ ordinal (Omega.ω₁ ℓ)
      → MerelyPresented ordinal)
    Sigma.×
    (MerelyPresented ordinal
      → Simulation._≺_ ordinal (Omega.ω₁ ℓ))
strict-cut ordinal =
  Sigma._,_
    (strict→presented ordinal)
    (presented→strict ordinal)
