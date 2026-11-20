{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Happly.Pointwise where

-- Adjusted extensionality at every level, kept opaque (pointwise).
-- pointwise-at reads its path at each argument; pointwise-equation
-- identifies it with the adjusted funext construction.

open import SPT.Base
open import SPT.Foundation.Happly using (happly; funext; happly-funext)
open import SPT.Foundation.Sets.Uniqueness using (Extensionality; extensional)

module _ (ext : Extensionality) where

  opaque
    pointwise : {ν μ : Level} {X : Set ν} {Y : X → Set μ}
      {f g : (x : X) → Y x} → ((x : X) → f x ＝ g x) → f ＝ g
    pointwise {ν} {μ} {X} {Y} {f} {g} h =
      funext (extensional ext) f g h

    pointwise-equation : {ν μ : Level} {X : Set ν} {Y : X → Set μ}
      {f g : (x : X) → Y x} (h : (x : X) → f x ＝ g x) →
      pointwise h ＝ funext (extensional ext) f g h
    pointwise-equation h = refl

    pointwise-at : {ν μ : Level} {X : Set ν} {Y : X → Set μ}
      {f g : (x : X) → Y x} (h : (x : X) → f x ＝ g x)
      (x : X) → happly (pointwise h) x ＝ h x
    pointwise-at {ν} {μ} {X} {Y} {f} {g} h x =
      happly
        (happly-funext (extensional ext) (λ k → extensional ext) f g h)
        x
