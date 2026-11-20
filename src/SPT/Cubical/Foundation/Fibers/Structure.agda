{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Fibers.Structure where

-- Fibers of maps assemble their domain and compose. Every point of the
-- domain is exactly a point of the codomain with a point of the fiber over
-- it (`domain-fiber-isomorphism`):
--
--   A ≅ Σ (b : B). fiber f b.
--
-- The fiber of a composite is a fiber of the outer map with a fiber of the
-- inner map over its middle point, keeping that middle point and both paths
-- (`composite-fiber-isomorphism`):
--
--   Σ (m : fiber g c). fiber f (pr₁ m) ≅ fiber (λ a → g (f a)) c.
--
-- The fiber of the base projection of a pullback is the fiber of its first map:
-- the projection fiber isomorphism of SPT.Cubical.Foundation.Fibers.Projection
-- at the family of the pullback.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Isomorphisms using (_≅_)
open import SPT.Cubical.Foundation.Fibers using (fiber)

------------------------------------------------------------------------
-- The domain from the fibers

module _ {ℓ κ : Level} {A : Set ℓ} {B : Set κ} (f : A → B) where

  domain-fiber-forward-backward : (point : Σ B (fiber f)) →
    (f (pr₁ (pr₂ point)) , pr₁ (pr₂ point) , refl) ＝ point
  domain-fiber-forward-backward (.(f a) , a , refl) = refl

  domain-fiber-isomorphism : A ≅ Σ B (fiber f)
  domain-fiber-isomorphism = record
    { forward = λ a → f a , a , refl
    ; backward = λ point → pr₁ (pr₂ point)
    ; backward-forward = λ a → refl
    ; forward-backward = domain-fiber-forward-backward
    }

------------------------------------------------------------------------
-- Fibers of composites

module _ {ℓ κ μ : Level} {A : Set ℓ} {B : Set κ} {C : Set μ} (f : A → B)
  (g : B → C) (c : C) where

  flatten-composite-fiber :
    Σ (fiber g c) (λ middle → fiber f (pr₁ middle)) →
    fiber (λ a → g (f a)) c
  flatten-composite-fiber nested =
    pr₁ (pr₂ nested) , ap g (pr₂ (pr₂ nested)) ∙ pr₂ (pr₁ nested)

  expand-composite-fiber : fiber (λ a → g (f a)) c →
    Σ (fiber g c) (λ middle → fiber f (pr₁ middle))
  expand-composite-fiber point = (f (pr₁ point) , pr₂ point) , pr₁ point , refl

  expand-flatten-composite-fiber :
    (nested : Σ (fiber g c) (λ middle → fiber f (pr₁ middle))) →
    expand-composite-fiber (flatten-composite-fiber nested) ＝ nested
  expand-flatten-composite-fiber ((.(f a) , p) , a , refl) = refl

  flatten-expand-composite-fiber : (point : fiber (λ a → g (f a)) c) →
    flatten-composite-fiber (expand-composite-fiber point) ＝ point
  flatten-expand-composite-fiber point = refl

  composite-fiber-isomorphism :
    Σ (fiber g c) (λ middle → fiber f (pr₁ middle))
      ≅ fiber (λ a → g (f a)) c
  composite-fiber-isomorphism = record
    { forward = flatten-composite-fiber
    ; backward = expand-composite-fiber
    ; backward-forward = expand-flatten-composite-fiber
    ; forward-backward = flatten-expand-composite-fiber
    }
