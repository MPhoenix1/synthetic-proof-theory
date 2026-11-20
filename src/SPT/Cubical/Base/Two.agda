{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Base.Two where

-- The two-point type `𝟚` has the points `₀` and `₁`, which are distinct
-- (`₀-is-not-₁`), and its equality is decidable. It is the type of
-- `Agda.Builtin.Bool`, under SPT's names given in the renaming: `₀` is
-- `false` and `₁` is `true`.
--
-- A family over `𝟚` has a section given its points at `₀` and at `₁`
-- (`two-elim`). The map `𝟚-cases x y` sends `₀` to `x` and `₁` to `y`, so
-- `𝟚-cases x y b` is the conditional "if b then y else x".

open import Agda.Builtin.Bool public
  renaming (Bool to 𝟚; false to ₀; true to ₁)

open import SPT.Cubical.Base.Universes using (Level)
open import SPT.Cubical.Base.Identity using (_＝_; refl; _≠_)
open import SPT.Cubical.Base.Sum using (inl; inr)
open import SPT.Cubical.Base.Decidable using (has-decidable-equality)

------------------------------------------------------------------------
-- Properties

₀-is-not-₁ : ₀ ≠ ₁
₀-is-not-₁ ()

𝟚-has-decidable-equality : has-decidable-equality 𝟚
𝟚-has-decidable-equality ₀ ₀ = inl refl
𝟚-has-decidable-equality ₀ ₁ = inr ₀-is-not-₁
𝟚-has-decidable-equality ₁ ₀ = inr (λ ())
𝟚-has-decidable-equality ₁ ₁ = inl refl

------------------------------------------------------------------------
-- Elimination of the two-point type

module _ {κ : Level} where

  two-elim : (P : 𝟚 → Set κ) → P ₀ → P ₁ → (c : 𝟚) → P c
  two-elim P l r ₀ = l
  two-elim P l r ₁ = r

------------------------------------------------------------------------
-- Cases

module _ {ℓ : Level} {A : Set ℓ} where

  𝟚-cases : A → A → 𝟚 → A
  𝟚-cases x y ₀ = x
  𝟚-cases x y ₁ = y
