{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Fibers where

-- The fiber of a map `f : A → B` over a point `b` is the type of points `a` of
-- `A` together with an identification `f a ＝ b`. The identification is kept:
-- this is the homotopy fiber, not the inverse image of a set map. A map has
-- contractible fibers when its fiber over every point is contractible. Two
-- points of one fiber with distinct sources refute the contractibility of that
-- fiber.

open import SPT.Base
open import SPT.Foundation.Contractible using (is-contractible)

module _ {ℓ κ : Level} {A : Set ℓ} {B : Set κ} where

  fiber : (A → B) → B → Set (ℓ ⊔ κ)
  fiber f b = Σ A (λ a → f a ＝ b)

  has-contractible-fibers : (A → B) → Set (ℓ ⊔ κ)
  has-contractible-fibers f = (b : B) → is-contractible (fiber f b)

------------------------------------------------------------------------
-- Properties

module _ {ℓ κ : Level} {A : Set ℓ} {B : Set κ} {f : A → B} {b : B} where

  separated-fiber-is-not-contractible : (u v : fiber f b) →
    pr₁ u ≠ pr₁ v → ¬ is-contractible (fiber f b)
  separated-fiber-is-not-contractible u v distinct (c , contraction) =
    distinct (ap pr₁ (contraction u ⁻¹ ∙ contraction v))
