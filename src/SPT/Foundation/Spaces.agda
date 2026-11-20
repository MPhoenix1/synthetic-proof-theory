{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Spaces where

-- Displayed spaces: a base type with a family of fibers over its points,
-- and the total space of such a family. The base is the determining datum;
-- a fiber's type depends on the exact base point it lies over.
--
--   Total X = Σ (Base X) (Fiber X).
--
-- Main definitions: the record `DΣ` (fields `Base`, `Fiber`) and `Total`,
-- and the one-point space, one point over one point (`unit-space`). The
-- Foundation's trees and signatures state their extensions as displayed
-- spaces.

open import SPT.Base

record DΣ (ℓb ℓf : Level) : Set (lsuc (ℓb ⊔ ℓf)) where
  field
    Base : Set ℓb
    Fiber : Base → Set ℓf

open DΣ public

Total : {ℓb ℓf : Level} → DΣ ℓb ℓf → Set (ℓb ⊔ ℓf)
Total X = Σ (Base X) (Fiber X)

-- The one-point displayed space, at every level.

unit-space : (ℓ : Level) → DΣ ℓ ℓ
unit-space ℓ = record
  { Base = Lift ℓ 𝟙
  ; Fiber = λ point → Lift ℓ 𝟙
  }
