{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Presentation.Enumeration where

-- Partial ℕ-enumerations up to equality, and the successful entries of a
-- partial sequence, which are themselves enumerated up to equality.

open import Agda.Primitive using (Level)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

------------------------------------------------------------------------
-- Enumerations and successful entries

-- An enumeration of A up to equality:
--
--   Exactℕ𝒫(A) = Σ(e : ℕ → Maybe A). Π a. Σ n. e(n) ≡ just(a).

record Exactℕ𝒫 {ℓ : Level} (A : Set ℓ) : Set ℓ where
  field
    enum : ℕ → Maybe A
    covers :
      (x : A) → Σ ℕ λ n → enum n ≡ just x

-- `Entry.T e` has one constructor, exactly when e is `just`, so an
-- occurrence (an index with an entry) records its value without an
-- equality proof.

module Entry where

  data T {ℓ : Level} {A : Set ℓ} : Maybe A → Set ℓ where
    present : ∀ {x} → T (just x)

  value :
      ∀ {ℓ} {A : Set ℓ} {entry : Maybe A}
    → T entry
    → A
  value {entry = just x} present = x

  selects :
      ∀ {ℓ} {A : Set ℓ} {entry : Maybe A}
    → (selected : T entry)
    → entry ≡ just (value selected)
  selects present = refl

  maybe :
      ∀ {ℓ} {A : Set ℓ}
    → (entry : Maybe A)
    → Maybe (T entry)
  maybe nothing = nothing
  maybe (just x) = just present

  maybe-covers :
      ∀ {ℓ} {A : Set ℓ} {entry : Maybe A}
    → (selected : T entry)
    → maybe entry ≡ just selected
  maybe-covers present = refl

  -- Conversely to `selects`, an equation entry ≡ just x gives an entry,
  -- whose value is x.

  fromSelection :
      ∀ {ℓ} {A : Set ℓ} {entry : Maybe A} {x : A}
    → entry ≡ just x
    → T entry
  fromSelection refl = present

  value-fromSelection :
      ∀ {ℓ} {A : Set ℓ} {entry : Maybe A} {x : A}
    → (selected : entry ≡ just x)
    → value (fromSelection selected) ≡ x
  value-fromSelection refl = refl

module Occurrence where

  T :
      ∀ {ℓ} {A : Set ℓ}
    → (ℕ → Maybe A)
    → Set ℓ
  T sequence =
    Σ ℕ λ n → Entry.T (sequence n)

  fromEntry :
      ∀ {ℓ} {A : Set ℓ}
        {sequence : ℕ → Maybe A}
    → (n : ℕ)
    → Maybe (Entry.T (sequence n))
    → Maybe (T sequence)
  fromEntry n nothing = nothing
  fromEntry n (just selected) = just (n , selected)

  value :
      ∀ {ℓ} {A : Set ℓ} {sequence : ℕ → Maybe A}
    → T sequence
    → A
  value (n , selected) = Entry.value selected

  selects :
      ∀ {ℓ} {A : Set ℓ} {sequence : ℕ → Maybe A}
    → (occurrence : T sequence)
    → sequence (proj₁ occurrence) ≡ just (value occurrence)
  selects (n , selected) = Entry.selects selected

  enum :
      ∀ {ℓ} {A : Set ℓ}
    → (sequence : ℕ → Maybe A)
    → ℕ → Maybe (T sequence)
  enum sequence n =
    fromEntry n (Entry.maybe (sequence n))

  covers :
      ∀ {ℓ} {A : Set ℓ}
        (sequence : ℕ → Maybe A)
        (occurrence : T sequence)
    → Σ ℕ λ n → enum sequence n ≡ just occurrence
  covers sequence (n , selected) =
    n
    , cong (fromEntry n)
        (Entry.maybe-covers selected)

  𝒫 :
      ∀ {ℓ} {A : Set ℓ}
    → (sequence : ℕ → Maybe A)
    → Exactℕ𝒫 (T sequence)
  𝒫 sequence = record
    { enum = enum sequence
    ; covers = covers sequence
    }
