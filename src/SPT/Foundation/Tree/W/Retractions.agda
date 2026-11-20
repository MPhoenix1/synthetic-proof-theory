{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Tree.W.Retractions where

-- A tree node is unchanged when its branches are read through a
-- fiberwise retraction along an identification of labels (sup-forth).
-- The round trip and function extensionality are explicit hypotheses.

open import SPT.Base
open import SPT.Foundation.Sets.Uniqueness using
  (Extensionality; pointwise)
open import SPT.Foundation.Tree.W using (W; sup)

module _ {ℓ μ ν ρ : Level} {X : Set ℓ} {Y : Set μ}
  (o : X → Y) (Q : Y → Set ν) (R : X → Set ρ)
  (enter : (y : X) → Q (o y) → R y) (leave : (y : X) → R y → Q (o y))
  (round : (y : X) (r : R y) → enter y (leave y r) ＝ r) where

  sup-forth : Extensionality → {y₀ y : X} (e : y₀ ＝ y)
    (f : R y → W X R) →
    sup y₀ (λ r → f (enter y (transport Q (ap o e) (leave y₀ r))))
      ＝ sup y f
  sup-forth ext {y₀} refl f =
    ap (sup y₀) (pointwise ext (λ r → ap f (round y₀ r)))
