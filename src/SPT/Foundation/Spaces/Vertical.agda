{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Spaces.Vertical where

-- Vertical maps of displayed spaces: maps between two families over one
-- literally shared base. The base is selected before the varying state is
-- read, so a vertical map may change the kind of state but never the base:
--
--   Fiber-Map D S T = Π (d : D). S d → T d.
--
-- Fiber maps have an identity and a composite, and give split maps and total
-- maps of the family spaces (`fiber-map-split-map`, `fiber-map-total-map`),
-- whose computation laws hold by refl. Isomorphisms of the fibers over each
-- point give an isomorphism of the totals whose two maps keep the base point
-- by refl, and whose forward map is the total map of the fiberwise forward
-- maps (`fiberwise-total-isomorphism`). No uniqueness, normalization or
-- deepest determinant is asserted.

open import SPT.Base
open import SPT.Foundation.Isomorphisms using
  (_≅_; forward; backward; Σ-cong)
open import SPT.Foundation.Spaces using (DΣ; Base; Fiber; Total)
open import SPT.Foundation.Spaces.Maps using
  ( Total-Map; Split-Map; project-base; project-fiber; apply-total-map
  ; split-to-total; compose-total-map
  )

------------------------------------------------------------------------
-- The displayed space of a family

-- The canonical owner of a dependent state shape, so that source and target
-- families can share one determinant type. This is not a new carrier, a
-- universe, or evidence that the base is deepest or dependency-closed.

family-displayed-space : {ℓd ℓs : Level} (Determinant : Set ℓd)
  (State : Determinant → Set ℓs) → DΣ ℓd ℓs
family-displayed-space Determinant State = record
  { Base = Determinant
  ; Fiber = State
  }

------------------------------------------------------------------------
-- Maps over one shared determinant

Fiber-Map : {ℓd ℓs ℓt : Level} (Determinant : Set ℓd)
  (Source : Determinant → Set ℓs) (Target : Determinant → Set ℓt) →
  Set (ℓd ⊔ ℓs ⊔ ℓt)
Fiber-Map Determinant Source Target =
  (determinant : Determinant) → Source determinant → Target determinant

module _ {ℓd ℓs : Level} {Determinant : Set ℓd}
  {State : Determinant → Set ℓs} where

  identity-fiber-map : Fiber-Map Determinant State State
  identity-fiber-map determinant state = state

module _ {ℓd ℓs ℓm ℓt : Level} {Determinant : Set ℓd}
  {Source : Determinant → Set ℓs} {Middle : Determinant → Set ℓm}
  {Target : Determinant → Set ℓt} where

  compose-fiber-map : Fiber-Map Determinant Middle Target →
    Fiber-Map Determinant Source Middle → Fiber-Map Determinant Source Target
  compose-fiber-map second first determinant source =
    second determinant (first determinant source)

------------------------------------------------------------------------
-- Fiber maps as split and total maps

-- The total map forgets that base preservation was forced by typing; the
-- laws below recover it by refl.

module _ {ℓd ℓs ℓt : Level} {Determinant : Set ℓd}
  {Source : Determinant → Set ℓs} {Target : Determinant → Set ℓt} where

  fiber-map-split-map : Fiber-Map Determinant Source Target →
    Split-Map (family-displayed-space Determinant Source)
      (family-displayed-space Determinant Target)
  fiber-map-split-map transformation = record
    { on-base = λ determinant → determinant
    ; on-fiber = transformation
    }

  fiber-map-total-map : Fiber-Map Determinant Source Target →
    Total-Map (family-displayed-space Determinant Source)
      (family-displayed-space Determinant Target)
  fiber-map-total-map transformation =
    split-to-total (fiber-map-split-map transformation)

  fiber-map-total-map-determinant :
    (transformation : Fiber-Map Determinant Source Target)
    (determinant : Determinant) (source : Source determinant) →
    project-base (family-displayed-space Determinant Target)
      (fiber-map-total-map transformation determinant source)
      ＝ determinant
  fiber-map-total-map-determinant transformation determinant source = refl

  fiber-map-total-map-determinant-point :
    (transformation : Fiber-Map Determinant Source Target)
    (point : Total (family-displayed-space Determinant Source)) →
    project-base (family-displayed-space Determinant Target)
      (apply-total-map (family-displayed-space Determinant Source)
        (family-displayed-space Determinant Target)
        (fiber-map-total-map transformation) point)
      ＝ project-base (family-displayed-space Determinant Source) point
  fiber-map-total-map-determinant-point transformation
    (determinant , source) = refl

  fiber-map-total-map-state :
    (transformation : Fiber-Map Determinant Source Target)
    (determinant : Determinant) (source : Source determinant) →
    project-fiber (family-displayed-space Determinant Target)
      (fiber-map-total-map transformation determinant source)
      ＝ transformation determinant source
  fiber-map-total-map-state transformation determinant source = refl

module _ {ℓd ℓs ℓm ℓt : Level} {Determinant : Set ℓd}
  {Source : Determinant → Set ℓs} {Middle : Determinant → Set ℓm}
  {Target : Determinant → Set ℓt} where

  fiber-map-total-map-compose :
    (second : Fiber-Map Determinant Middle Target)
    (first : Fiber-Map Determinant Source Middle)
    (determinant : Determinant) (source : Source determinant) →
    fiber-map-total-map (compose-fiber-map second first) determinant source
      ＝ apply-total-map (family-displayed-space Determinant Source)
        (family-displayed-space Determinant Target)
        (compose-total-map (family-displayed-space Determinant Source)
          (family-displayed-space Determinant Middle)
          (family-displayed-space Determinant Target)
          (fiber-map-total-map second) (fiber-map-total-map first))
        (determinant , source)
  fiber-map-total-map-compose second first determinant source = refl

------------------------------------------------------------------------
-- Fiberwise isomorphisms over one shared determinant

-- The determinant is kept in both directions; only the fiber inhabitant is
-- mapped, by the isomorphism at its own base point.

module _ {ℓd ℓs ℓt : Level} {Determinant : Set ℓd}
  {Source : Determinant → Set ℓs} {Target : Determinant → Set ℓt}
  (fibers : (determinant : Determinant) →
    Source determinant ≅ Target determinant) where

  fiberwise-total-isomorphism :
    Total (family-displayed-space Determinant Source)
      ≅ Total (family-displayed-space Determinant Target)
  fiberwise-total-isomorphism = Σ-cong fibers

  fiberwise-total-isomorphism-forward-base :
    (point : Total (family-displayed-space Determinant Source)) →
    project-base (family-displayed-space Determinant Target)
      (forward fiberwise-total-isomorphism point)
      ＝ project-base (family-displayed-space Determinant Source) point
  fiberwise-total-isomorphism-forward-base (determinant , source) = refl

  fiberwise-total-isomorphism-backward-base :
    (point : Total (family-displayed-space Determinant Target)) →
    project-base (family-displayed-space Determinant Source)
      (backward fiberwise-total-isomorphism point)
      ＝ project-base (family-displayed-space Determinant Target) point
  fiberwise-total-isomorphism-backward-base (determinant , target) = refl

  fiberwise-total-isomorphism-forward-is-fiber-map :
    (point : Total (family-displayed-space Determinant Source)) →
    forward fiberwise-total-isomorphism point
      ＝ apply-total-map (family-displayed-space Determinant Source)
        (family-displayed-space Determinant Target)
        (fiber-map-total-map (λ determinant → forward (fibers determinant)))
        point
  fiberwise-total-isomorphism-forward-is-fiber-map (determinant , source) =
    refl
