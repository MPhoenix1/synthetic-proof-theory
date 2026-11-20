{-# OPTIONS --safe --without-K --two-level #-}

module SPT.TwoLevel.Mahlo.Branches where

-- Branches respect strict identification of families in context.
-- branches-along identifies the first family's branches, read along
-- the inverse identification of codes, with the second's branches.

open import SPT.Base
open import SPT.Mahlo.Specification using (Family)
open import SPT.TwoLevel.Coherence using
  (_≐_; same; fibrant; apˢ)

------------------------------------------------------------------------
-- Branches along a strict identification

module _ {ι ν κ ℓ : Level} {A : Set ι} {B : A → Set ν} {C : Set κ}
  {D : C → Set ℓ} where

  branches-along : {F G : (x : A) → B x → Family D} (e : F ≐ G) →
    (λ (x : A) (y : B x) (t : D (pr₁ (G x y))) →
      pr₂ (F x y)
        (transport D (fibrant (apˢ (λ H → pr₁ (H x y)) e) ⁻¹) t)) ≐
    (λ x y t → pr₂ (G x y) t)
  branches-along same = same
