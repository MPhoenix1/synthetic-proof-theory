{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Truncations where

-- Propositional truncation at one universe level, as a hypothesis: a record
-- `Truncation ℓ` of a proposition `∥ X ∥` for each type `X` of that level,
-- the map `∣_∣` into it, and its recursion into the propositions of that
-- level,
--
--   ∥∥-rec : is-proposition P → (X → P) → ∥ X ∥ → P.
--
-- SPT never assumes a truncation; a theorem that needs one takes the record
-- as an explicit argument. Truncation is functorial (`∥∥-map`), and a
-- truncated point gives a truncated point of anything it maps to truncatedly
-- (`∥∥-bind`).

open import SPT.Base
open import SPT.Foundation.Propositions using (is-proposition)

------------------------------------------------------------------------
-- Truncations

record Truncation (ℓ : Level) : Set (lsuc ℓ) where
  field
    ∥_∥ : Set ℓ → Set ℓ
    ∥∥-is-proposition : (X : Set ℓ) → is-proposition ∥ X ∥
    ∣_∣ : {X : Set ℓ} → X → ∥ X ∥
    ∥∥-rec : {X P : Set ℓ} → is-proposition P → (X → P) → ∥ X ∥ → P

------------------------------------------------------------------------
-- Functoriality and binding

module _ {ℓ : Level} (t : Truncation ℓ) where

  open Truncation t

  -- Truncation is functorial.
  ∥∥-map : {X Y : Set ℓ} → (X → Y) → ∥ X ∥ → ∥ Y ∥
  ∥∥-map {X} {Y} f = ∥∥-rec (∥∥-is-proposition Y) (λ x → ∣ f x ∣)

  -- A truncated point gives a truncated point of anything it maps to
  -- truncatedly.
  ∥∥-bind : {X Y : Set ℓ} → ∥ X ∥ → (X → ∥ Y ∥) → ∥ Y ∥
  ∥∥-bind {X} {Y} x f = ∥∥-rec (∥∥-is-proposition Y) f x
