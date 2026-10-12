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

open import Agda.Primitive using (Level)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Data.Bool.Properties using (T-irrelevant)
open import Data.Nat.Properties using () renaming (_≟_ to _≟ℕ_)
open import Data.Product using (_,_; proj₁)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; cong)
open import Relation.Nullary using (Dec; yes; no)

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
    ≈-unique : ∀ {x y} (p q : 𝒫._≈_ P x y) → p ≡ q
    <-unique : ∀ {x y} (p q : 𝒫._<_ P x y) → p ≡ q

-- The presentation of a Boolean order.
boolean : BooleanOrder → 𝒫 ℓ
boolean O = Normalized.presentation (order O)

private
  -- Points of a Boolean order are equal exactly when their indices are.
  decide : (O : BooleanOrder) (a b : Points O) → Dec (a ≡ b)
  decide O (i , s) (j , t) with i ≟ℕ j
  ... | yes e = yes (point-≡ O e)
  ... | no n = no λ e → n (cong proj₁ e)

-- The presentation of a Boolean order is propositional.
boolean-propositional : (O : BooleanOrder) → Propositional (boolean {ℓ} O)
boolean-propositional O = record
  { ≈-unique = λ p q →
      cong lift (Decidable⇒UIP.≡-irrelevant (decide O) (lower p) (lower q))
  ; <-unique = λ p q → cong lift (T-irrelevant (lower p) (lower q))
  }
