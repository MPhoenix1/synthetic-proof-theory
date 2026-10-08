{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.WellFounded.Termination where

-- Strong normalization of a rewrite system as accessibility of the
-- reversed step relation, and termination as a section of the total space
-- of strongly normalizing states.

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_; fst)

open import SPT.Cubical.Core.WellFounded
open import SPT.Cubical.Core.WellFounded.Rewrite

------------------------------------------------------------------------
-- Strong normalization as accessibility

module Termination {ℓ ℓr : Level} (R : Rewrite ℓ ℓr) where

  open Rewrite R

  infix 30 _≺_

  _≺_ : State → State → Set ℓr
  y ≺ x = x ↝ y

  SN : State → Set (ℓ ⊔ ℓr)
  SN x = Acc _≺_ x

  Term : Set (ℓ ⊔ ℓr)
  Term = ∀ x → SN x

  ----------------------------------------------------------------------
  -- The total space of terminating states as a fibration over states

  AccFib : Set (ℓ ⊔ ℓr)
  AccFib = Σ State SN

  root : AccFib → State
  root = fst

  Fiber : State → Set (ℓ ⊔ ℓr)
  Fiber x = Σ AccFib (λ t → root t ≡ x)

  term→fiber : Term → ∀ x → Fiber x
  term→fiber t x = (x , t x) , refl

  fiber→term : (∀ x → Fiber x) → Term
  fiber→term sec x with sec x
  ... | ((y , sn) , refl) = sn
