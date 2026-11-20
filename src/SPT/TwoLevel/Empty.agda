{-# OPTIONS --safe --without-K --two-level #-}

module SPT.TwoLevel.Empty where

-- The fibrant empty type eliminates into every outer type.
-- 𝟘-elimˢ is defined by the empty pattern.

open import Agda.Primitive using (SSet)
open import SPT.Base using (Level; 𝟘)

------------------------------------------------------------------------
-- Empty elimination into outer types

module _ {ℓ : Level} {X : SSet ℓ} where

  𝟘-elimˢ : 𝟘 → X
  𝟘-elimˢ ()
