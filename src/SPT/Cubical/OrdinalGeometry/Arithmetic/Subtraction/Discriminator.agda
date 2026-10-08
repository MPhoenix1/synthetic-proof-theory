{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Subtraction.Discriminator where

-- Subtraction without its datum. Suppose every initial map P → Q had a
-- remainder R with P + R ≃ Q, even one that does not agree with the map.
-- Then an arbitrary Boolean stream s is decided: possible s, which has a
-- point exactly when s hits true, includes into one, and the point of one
-- comes back from the left summand exactly when s hits (remainder). So the
-- decided image that Subtraction asks for cannot be dropped: the
-- remainders of arbitrary initial maps give LPO.

open import Agda.Primitive using (lzero)
open import Data.Bool using (Bool; false)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
import Data.Unit.Polymorphic as Polymorphic
open import Relation.Binary.PropositionalEquality using (_≡_)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
open import SPT.Cubical.OrdinalGeometry.Presentation.Sum using (_+_)
import SPT.Cubical.OrdinalGeometry.Presentation.Limit.Discriminator as Stream

-- Mathematical shape: Σ R. P + R ≃ Q.
Remainder : 𝒫 lzero → 𝒫 lzero → Set₁
Remainder P Q = Σ (𝒫 lzero) (λ R → (P + R) Presented.≃𝒫 Q)

private
  -- The point of one comes from the left summand exactly when s hits: a
  -- right point lies above every left point, and one has a single point.
  decide : (s : ℕ → Bool) → Remainder (Stream.possible s) Stream.one
    → Stream.Hit s ⊎ ((n : ℕ) → s n ≡ false)
  decide s (R , e) with Presented._≃𝒫_.from e tt
  ... | inj₁ h = inj₁ h
  ... | inj₂ r = inj₂ (Stream.absent s λ h →
    Presented._≃𝒫_.to-< e {x = inj₁ h} {y = inj₂ r} Polymorphic.tt)

-- Mathematical shape: (Π P Q. P ≤ Q → Σ R. P + R ≃ Q) → LPO.
remainder : ((P Q : 𝒫 lzero) → Maps.Initial P Q → Remainder P Q)
  → Stream.LPO
remainder subtract s =
  decide s (subtract (Stream.possible s) Stream.one (Stream.inclusion s))
