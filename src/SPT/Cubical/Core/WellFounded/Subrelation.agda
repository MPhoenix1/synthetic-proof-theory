{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.WellFounded.Subrelation where

-- Inclusion of type-valued relations, and well-foundedness of a relation
-- contained in a well-founded one.

open import Agda.Primitive using (Level; _⊔_)

open import SPT.Cubical.Core.WellFounded

------------------------------------------------------------------------
-- Subrelations

-- SubRel R S = Π {x y}. R x y → S x y.  Both relations are type-valued, so
-- an inhabitant maps each R-witness to an S-witness.

SubRel :
  {ℓ ℓr ℓs : Level}
  {A : Set ℓ} →
  (A → A → Set ℓr) →
  (A → A → Set ℓs) →
  Set (ℓ ⊔ ℓr ⊔ ℓs)
SubRel R S = ∀ {x y} → R x y → S x y

-- A subrelation of a well-founded relation is well founded: an S-accessible
-- point is R-accessible, since every R-predecessor is an S-predecessor.

subrel-wf :
  {ℓ ℓr ℓs : Level}
  {A : Set ℓ}
  {R : A → A → Set ℓr}
  {S : A → A → Set ℓs} →
  SubRel R S →
  WellFounded S →
  WellFounded R
subrel-wf {R = R} {S = S} R⊆S wfS x = go x (wfS x)
  where
    go : ∀ x → Acc S x → Acc R x
    go x (acc smallerS) =
      acc λ y yRx →
        go y (smallerS y (R⊆S yRx))
