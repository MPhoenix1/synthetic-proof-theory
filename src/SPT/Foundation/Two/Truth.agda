{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Two.Truth where

-- The truth family of the two-point type: `is-₁ b` is the unit type at `₁`
-- and the empty type at `₀`, by computation, so a Boolean datum b : 𝟚 holds
-- or fails as a type with at most one point (`is-₁-is-proposition`). A
-- Boolean relation `less : ℕ → ℕ → 𝟚` is read as the type-valued relation
-- `λ i j → is-₁ (less i j)`.

open import SPT.Base
open import SPT.Foundation.Propositions using (is-proposition)

is-₁ : 𝟚 → Set
is-₁ ₀ = 𝟘
is-₁ ₁ = 𝟙

is-₁-is-proposition : (b : 𝟚) → is-proposition (is-₁ b)
is-₁-is-proposition ₁ s t = refl
