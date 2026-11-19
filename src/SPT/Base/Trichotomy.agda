{-# OPTIONS --safe --without-K #-}

module SPT.Base.Trichotomy where

-- Two points `x` and `y` are in trichotomy for a strict relation `<` up to a
-- relation `≈` when `x < y`, `x ≈ y` or `y < x`. The relations come first, so
-- they fix the type of the points: a trichotomy of identified points is
-- `Trichotomy _＝_ _<_ x y`, and a pair such as `(a , x)` is read at the type of
-- `<` without naming it.

open import SPT.Base.Universes using (Level; _⊔_)
open import SPT.Base.Sum using (_⊎_)

module _ {ℓ κ μ : Level} {A : Set ℓ} where

  Trichotomy : (A → A → Set κ) → (A → A → Set μ) → A → A → Set (κ ⊔ μ)
  Trichotomy _≈_ _<_ x y = (x < y) ⊎ ((x ≈ y) ⊎ (y < x))
