{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Base.Empty where

-- The empty type `𝟘` has no points, so a point of it gives a point of any type
-- (`𝟘-elim`). The negation `¬ A` of a type is the type of maps from `A` into
-- `𝟘`. Since `A → 𝟘` lives in the universe of `A`, `𝟘` needs only the lowest
-- universe.

open import SPT.Cubical.Base.Universes

------------------------------------------------------------------------
-- The empty type

data 𝟘 : Set where

𝟘-elim : {ℓ : Level} {A : Set ℓ} → 𝟘 → A
𝟘-elim ()

------------------------------------------------------------------------
-- Negation

infix 25 ¬_

¬_ : {ℓ : Level} → Set ℓ → Set ℓ
¬ A = A → 𝟘
