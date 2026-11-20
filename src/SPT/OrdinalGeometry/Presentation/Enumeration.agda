{-# OPTIONS --safe --without-K #-}

module SPT.OrdinalGeometry.Presentation.Enumeration where

-- Exact partial ℕ-enumerations and their successful occurrences. An exact
-- enumeration of a type lists every point by literal identification
-- (`Exact-Enumeration`):
--
--   Exact-Enumeration A = Σ e : ℕ → Maybe A. Π a : A. Σ n : ℕ. e n ＝ just a.
--
-- No quotient or presentation equivalence is used: this is the
-- countability datum that enumerates every exact operation child of a
-- signature-generated node. An entry of a partial sequence is present only
-- at `just` (`Entry`), so an occurrence in the sequence (`Occurrence`)
-- keeps the index and the selected value with no stored identification,
-- and the occurrences of a sequence are themselves exactly enumerated
-- (`occurrence-enumeration`).

open import SPT.Base

------------------------------------------------------------------------
-- Exact partial enumerations

record Exact-Enumeration {ℓ : Level} (A : Set ℓ) : Set ℓ where
  field
    enum : ℕ → Maybe A
    covers : (x : A) → Σ ℕ (λ n → enum n ＝ just x)

------------------------------------------------------------------------
-- Present entries

-- At a `just` entry the family has exactly the constructor below, and at
-- `nothing` it has none, so a present entry keeps the selected value with
-- no identification as a further coordinate.

data Entry {ℓ : Level} {A : Set ℓ} : Maybe A → Set ℓ where
  present : {x : A} → Entry (just x)

module _ {ℓ : Level} {A : Set ℓ} where

  entry-value : {entry : Maybe A} → Entry entry → A
  entry-value (present {x}) = x

  entry-selects : {entry : Maybe A} (selected : Entry entry) →
    entry ＝ just (entry-value selected)
  entry-selects present = refl

  maybe-entry : (entry : Maybe A) → Maybe (Entry entry)
  maybe-entry nothing = nothing
  maybe-entry (just x) = just present

  maybe-entry-covers : {entry : Maybe A} (selected : Entry entry) →
    maybe-entry entry ＝ just selected
  maybe-entry-covers present = refl

------------------------------------------------------------------------
-- Occurrences in a partial sequence

module _ {ℓ : Level} {A : Set ℓ} where

  Occurrence : (ℕ → Maybe A) → Set ℓ
  Occurrence sequence = Σ ℕ (λ n → Entry (sequence n))

  occurrence-from-entry : (sequence : ℕ → Maybe A) (n : ℕ) →
    Maybe (Entry (sequence n)) → Maybe (Occurrence sequence)
  occurrence-from-entry sequence n nothing = nothing
  occurrence-from-entry sequence n (just selected) = just (n , selected)

  occurrence-value : (sequence : ℕ → Maybe A) → Occurrence sequence → A
  occurrence-value sequence (n , selected) = entry-value selected

  occurrence-selects : (sequence : ℕ → Maybe A)
    (occurrence : Occurrence sequence) →
    sequence (pr₁ occurrence) ＝ just (occurrence-value sequence occurrence)
  occurrence-selects sequence (n , selected) = entry-selects selected

  enumerate-occurrences : (sequence : ℕ → Maybe A) →
    ℕ → Maybe (Occurrence sequence)
  enumerate-occurrences sequence n =
    occurrence-from-entry sequence n (maybe-entry (sequence n))

  occurrences-are-covered : (sequence : ℕ → Maybe A)
    (occurrence : Occurrence sequence) →
    Σ ℕ (λ n → enumerate-occurrences sequence n ＝ just occurrence)
  occurrences-are-covered sequence (n , selected) =
    n , ap (occurrence-from-entry sequence n) (maybe-entry-covers selected)

  occurrence-enumeration : (sequence : ℕ → Maybe A) →
    Exact-Enumeration (Occurrence sequence)
  occurrence-enumeration sequence = record
    { enum = enumerate-occurrences sequence
    ; covers = occurrences-are-covered sequence
    }
