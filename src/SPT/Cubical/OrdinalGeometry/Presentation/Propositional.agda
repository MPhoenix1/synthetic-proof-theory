{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Presentation.Propositional where

-- Propositional presentations: between any two points, sameness and the
-- strict order each have at most one witness. The presentation of a
-- Boolean order is propositional (boolean-propositional). Its sameness is
-- equality of points, each an index with a proof of a Boolean, so it has
-- decidable equality and unique identity proofs (Hedberg); its order is a
-- Boolean condition on indices. Every presentation is equivalent to the
-- presentation of its Boolean order (Normalization.Boolean), so every
-- presentation is equivalent to a propositional one.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Hedberg using
  (decidable-equality-gives-set)
open import SPT.Cubical.Foundation.Two.Truth using (is-₁-is-proposition)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization.Presentation
  as Normalized
open import SPT.Cubical.OrdinalGeometry.ExactOrder.Boolean using
  (BooleanOrder; Points; order; point-≡)

private
  variable
    ℓ : Level

-- Mathematical shape: Π x y. isProp (x ≈ y) × isProp (x < y).
record Propositional (P : 𝒫 ℓ) : Set ℓ where
  field
    ≈-unique : ∀ {x y} (p q : 𝒫._≈_ P x y) → p ＝ q
    <-unique : ∀ {x y} (p q : 𝒫._<_ P x y) → p ＝ q

-- The presentation of a Boolean order.
boolean : BooleanOrder → 𝒫 ℓ
boolean O = Normalized.presentation (order O)

private
  -- Points of a Boolean order are equal exactly when their indices are.
  decide : (O : BooleanOrder) (a b : Points O) → is-decidable (a ＝ b)
  decide O (i , s) (j , t) with ℕ-has-decidable-equality i j
  ... | inl e = inl (point-≡ O e)
  ... | inr n = inr λ e → n (ap pr₁ e)

-- The presentation of a Boolean order is propositional.
boolean-propositional : (O : BooleanOrder) → Propositional (boolean {ℓ} O)
boolean-propositional O = record
  { ≈-unique = λ {x} {y} p q →
      ap lift
        (decidable-equality-gives-set (decide O) (lower x) (lower y)
          (lower p) (lower q))
  ; <-unique = λ {x} {y} p q →
      ap lift
        (is-₁-is-proposition
          (BooleanOrder.less O (pr₁ (lower x)) (pr₁ (lower y)))
          (lower p) (lower q))
  }
