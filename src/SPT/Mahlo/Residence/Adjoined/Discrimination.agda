{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Residence.Adjoined.Discrimination where

-- A lifted lower name differs from the generated empty name.
-- is-lifted distinguishes their formation constructors;
-- lifted-is-not-empty applies that distinction to an identification.

open import SPT.Base
open import SPT.Mahlo.Residence.Adjoined using
  (Name; liftedᶠ; empty; lifted)

module _ {ℓ : Level} (L : Set ℓ) (D : L → Set ℓ) (I : Set (lsuc ℓ))
  (E : I → Set ℓ) where

  is-lifted : Name L D I E → Set
  is-lifted (_ , liftedᶠ l) = 𝟙
  is-lifted _ = 𝟘

  lifted-is-not-empty : (l : L) →
    lifted {D = D} {I = I} {E = E} l ＝ empty → 𝟘
  lifted-is-not-empty l e = transport is-lifted e ⋆
