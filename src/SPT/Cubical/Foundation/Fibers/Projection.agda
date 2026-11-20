{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Fibers.Projection where

-- The fiber of the first projection of a dependent pair type over a point
-- is the family at that point,
--
--   F a ≅ fiber pr₁ a,   y ↦ ((a , y) , refl),
--
-- the backward map transporting the second component along the
-- identification of the fiber (`projection-fiber-isomorphism`).

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Fibers using (fiber)
open import SPT.Cubical.Foundation.Isomorphisms using
  (_≅_; forward; backward; backward-forward; forward-backward)

module _ {ℓ κ : Level} {A : Set ℓ} (F : A → Set κ) where

  projection-fiber-forward-backward : (a : A)
    (z : fiber (pr₁ {A = A} {B = F}) a) →
    ((a , transport F (pr₂ z) (pr₂ (pr₁ z))) , refl) ＝ z
  projection-fiber-forward-backward a ((.a , y) , refl) = refl

  projection-fiber-isomorphism : (a : A) →
    F a ≅ fiber (pr₁ {A = A} {B = F}) a
  projection-fiber-isomorphism a = record
    { forward = λ y → (a , y) , refl
    ; backward = λ z → transport F (pr₂ z) (pr₂ (pr₁ z))
    ; backward-forward = λ y → refl
    ; forward-backward = projection-fiber-forward-backward a
    }
