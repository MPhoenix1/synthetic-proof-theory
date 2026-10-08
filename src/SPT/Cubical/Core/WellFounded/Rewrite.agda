{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.WellFounded.Rewrite where

-- Abstract rewrite systems: a type of states with a type-valued step
-- relation, and the rewrite system that runs a relation backwards.

open import Agda.Primitive using (Level; lsuc; _⊔_)

------------------------------------------------------------------------
-- Rewrite systems

record Rewrite (ℓ ℓr : Level) : Set (lsuc (ℓ ⊔ ℓr)) where
  infix 40 _↝_
  field
    State : Set ℓ
    _↝_   : State → State → Set ℓr

------------------------------------------------------------------------
-- Rewrite system induced by a predecessor relation

-- A witness of `relation child parent` is a step `parent ↝ child`.

reverseRelationRewrite :
    ∀ {ℓ ℓr : Level}
      {A : Set ℓ}
  → (A → A → Set ℓr)
  → Rewrite ℓ ℓr
reverseRelationRewrite {A = A} relation = record
  { State = A
  ; _↝_ = λ parent child → relation child parent
  }
