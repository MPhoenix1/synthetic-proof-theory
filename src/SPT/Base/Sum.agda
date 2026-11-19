{-# OPTIONS --safe --without-K #-}

module SPT.Base.Sum where

-- The disjoint sum `A ⊎ B` has the points `inl a` for `a` in `A` and `inr b`
-- for `b` in `B`, and no others. A map out of it is given by cases on the two
-- sides. Its two injections never meet (`inl-is-not-inr`) and are injective.
-- SPT writes the sum `⊎`, keeping `+` for addition of numbers and of ordinals.

open import SPT.Base.Universes
open import SPT.Base.Identity using (_＝_; refl; _≠_)

infixr 10 _⊎_

data _⊎_ {ℓ κ : Level} (A : Set ℓ) (B : Set κ) : Set (ℓ ⊔ κ) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

module _ {ℓ κ μ : Level} {A : Set ℓ} {B : Set κ} {C : Set μ} where

  cases : (A → C) → (B → C) → A ⊎ B → C
  cases f g (inl a) = f a
  cases f g (inr b) = g b

------------------------------------------------------------------------
-- Properties

-- An injection alone does not show the other summand, so the injectivity laws
-- name the sum they live in.

module _ {ℓ κ : Level} {A : Set ℓ} {B : Set κ} where

  inl-is-not-inr : {a : A} {b : B} → inl a ≠ inr b
  inl-is-not-inr ()

  inl-is-injective : {a a′ : A} → _＝_ {A = A ⊎ B} (inl a) (inl a′) →
    a ＝ a′
  inl-is-injective refl = refl

  inr-is-injective : {b b′ : B} → _＝_ {A = A ⊎ B} (inr b) (inr b′) →
    b ＝ b′
  inr-is-injective refl = refl
