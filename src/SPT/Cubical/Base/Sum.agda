{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Base.Sum where

-- The disjoint sum `A ⊎ B` has the points `inl a` for `a` in `A` and `inr b`
-- for `b` in `B`, and no others. A map out of it is given by cases on the two
-- sides (`cases`), and a section of a family over it by one on each summand
-- (`⊎-induction`), computing by `refl` on both. Its two injections never meet
-- (`inl-is-not-inr`) and are injective. A map on each summand gives a map of
-- sums that keeps the side (`⊎-map`):
--
--   ⊎-map f g (inl a) = inl (f a),   ⊎-map f g (inr b) = inr (g b).
--
-- SPT writes the sum `⊎`, keeping `+` for addition of numbers and of ordinals.

open import SPT.Cubical.Base.Universes
open import SPT.Cubical.Base.Identity using (_＝_; refl; _≠_)

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

------------------------------------------------------------------------
-- Maps and induction

module _ {ℓ κ μ ν : Level} {A : Set ℓ} {B : Set κ} {C : Set μ} {D : Set ν}
  where

  ⊎-map : (A → C) → (B → D) → A ⊎ B → C ⊎ D
  ⊎-map f g (inl a) = inl (f a)
  ⊎-map f g (inr b) = inr (g b)

module _ {ℓ κ μ : Level} {A : Set ℓ} {B : Set κ} {P : A ⊎ B → Set μ} where

  ⊎-induction : ((a : A) → P (inl a)) → ((b : B) → P (inr b)) →
    (s : A ⊎ B) → P s
  ⊎-induction f g (inl a) = f a
  ⊎-induction f g (inr b) = g b
