{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Base.Decidable where

-- A type is decidable when a point of it, or a refutation of it, is given. A
-- type has decidable equality when any two of its points are decided to be
-- identified or not. Both are data: the decision is a point of a disjoint sum,
-- retained, not a mere statement that one side holds.

open import SPT.Cubical.Base.Universes
open import SPT.Cubical.Base.Empty using (¬_)
open import SPT.Cubical.Base.Identity using (_＝_)
open import SPT.Cubical.Base.Sum using (_⊎_)

is-decidable : {ℓ : Level} → Set ℓ → Set ℓ
is-decidable A = A ⊎ ¬ A

has-decidable-equality : {ℓ : Level} → Set ℓ → Set ℓ
has-decidable-equality A = (x y : A) → is-decidable (x ＝ y)
