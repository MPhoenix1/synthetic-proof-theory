{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.WellFounded.Subrelation where

-- A relation `R` is a subrelation of `S`, written `R ⊆ S`, when every witness
-- of `R x y` gives one of `S x y`. Both relations are type-valued, so the
-- inclusion is a map of witnesses, not a mere implication. A subrelation of a
-- well-founded relation is well-founded: an `S`-accessible point is
-- `R`-accessible, since each `R`-predecessor is an `S`-predecessor
-- (`accessible-in-subrelation`).

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Accessibility using
  (is-accessible; acc; is-well-founded)

module _ {ℓ κ μ : Level} {A : Set ℓ} where

  infix 5 _⊆_

  _⊆_ : (A → A → Set κ) → (A → A → Set μ) → Set (ℓ ⊔ κ ⊔ μ)
  R ⊆ S = {x y : A} → R x y → S x y

------------------------------------------------------------------------
-- Properties

module _ {ℓ κ μ : Level} {A : Set ℓ} {R : A → A → Set κ}
  {S : A → A → Set μ} where

  accessible-in-subrelation : R ⊆ S → (x : A) → is-accessible S x →
    is-accessible R x
  accessible-in-subrelation inclusion x (acc smaller) =
    acc (λ y y<x →
      accessible-in-subrelation inclusion y (smaller y (inclusion y<x)))

  subrelations-are-well-founded : R ⊆ S → is-well-founded S →
    is-well-founded R
  subrelations-are-well-founded inclusion well-founded x =
    accessible-in-subrelation inclusion x (well-founded x)
