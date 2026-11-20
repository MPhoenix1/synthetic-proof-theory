{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Base.Predicate where

-- Inclusion and equivalence of type-valued predicates on one type. A
-- predicate X is included in Y when every witness of X a gives one of Y a
-- (`_⊆ᵖ_`); two predicates are equivalent when each is included in the other
-- (`_≈ᵖ_`), symmetrically (`≈ᵖ-sym`):
--
--   X ⊆ᵖ Y = Π (a : A). X a → Y a,     X ≈ᵖ Y = (X ⊆ᵖ Y) × (Y ⊆ᵖ X).
--
-- Inclusion is a map of witnesses, not a mere implication, and equivalence
-- asks no inverse law. Foundation.WellFounded.Subrelation has the inclusion
-- of binary relations.

open import SPT.Cubical.Base.Universes
open import SPT.Cubical.Base.Sigma using (_,_; _×_)

module _ {α κ ν : Level} {A : Set α} where

  infix 5 _⊆ᵖ_

  -- Mathematical shape: Π (a : A). X a → Y a.
  _⊆ᵖ_ : (A → Set κ) → (A → Set ν) → Set (α ⊔ κ ⊔ ν)
  X ⊆ᵖ Y = (a : A) → X a → Y a

module _ {α κ : Level} {A : Set α} where

  infix 6 _≈ᵖ_

  -- Mathematical shape: (X ⊆ᵖ Y) × (Y ⊆ᵖ X).
  _≈ᵖ_ : (A → Set κ) → (A → Set κ) → Set (α ⊔ κ)
  X ≈ᵖ Y = (X ⊆ᵖ Y) × (Y ⊆ᵖ X)

  ≈ᵖ-sym : {X Y : A → Set κ} → X ≈ᵖ Y → Y ≈ᵖ X
  ≈ᵖ-sym (forth , back) = back , forth
