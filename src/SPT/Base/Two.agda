{-# OPTIONS --safe --without-K #-}

module SPT.Base.Two where

-- The two-point type `𝟚` has the points `₀` and `₁`, which are distinct
-- (`₀-is-not-₁`), and its equality is decidable. It is the type of
-- `Agda.Builtin.Bool`, under SPT's names given in the renaming: `₀` is
-- `false` and `₁` is `true`.

open import Agda.Builtin.Bool public
  renaming (Bool to 𝟚; false to ₀; true to ₁)

open import SPT.Base.Identity using (_＝_; refl; _≠_)
open import SPT.Base.Sum using (inl; inr)
open import SPT.Base.Decidable using (has-decidable-equality)

------------------------------------------------------------------------
-- Properties

₀-is-not-₁ : ₀ ≠ ₁
₀-is-not-₁ ()

𝟚-has-decidable-equality : has-decidable-equality 𝟚
𝟚-has-decidable-equality ₀ ₀ = inl refl
𝟚-has-decidable-equality ₀ ₁ = inr ₀-is-not-₁
𝟚-has-decidable-equality ₁ ₀ = inr (λ ())
𝟚-has-decidable-equality ₁ ₁ = inl refl
