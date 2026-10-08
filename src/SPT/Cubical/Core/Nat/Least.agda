{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.Nat.Least where

-- Least witnesses of a decidable predicate on ℕ, found by bounded search
-- below a given witness.  Minimality is stated with the computational order
-- `_<ℕᶜ_` of Nat.Order.

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

open import SPT.Cubical.Core.Nat.Order using
  (_<ℕᶜ_; cmpℕ<zero-impossible; <ℕᶜ-suc; <ℕᶜ-suc-split)

record LeastWitness (P : ℕ → Set) : Set where
  constructor least-witness
  field
    value : ℕ
    witness : P value
    minimal : (candidate : ℕ) → candidate <ℕᶜ value → ¬ P candidate

open LeastWitness public

data SearchBelow (P : ℕ → Set) (bound : ℕ) : Set where
  found : LeastWitness P → SearchBelow P bound
  absent :
      ((candidate : ℕ) → candidate <ℕᶜ bound → ¬ P candidate)
    → SearchBelow P bound

searchBelow :
    (P : ℕ → Set)
  → ((candidate : ℕ) → Dec (P candidate))
  → (bound : ℕ)
  → SearchBelow P bound
searchBelow P decide zero =
  absent (λ candidate candidate<zero →
    ⊥-elim (cmpℕ<zero-impossible candidate candidate<zero))
searchBelow P decide (suc bound) with searchBelow P decide bound
... | found least = found least
... | absent none-below with decide bound
...   | yes proof =
  found (least-witness bound proof none-below)
...   | no refutation =
  absent λ candidate candidate<suc-bound →
    case-split (<ℕᶜ-suc-split candidate bound candidate<suc-bound)
  where
    case-split :
        ∀ {candidate}
      → (candidate <ℕᶜ bound) ⊎ (candidate ≡ bound)
      → ¬ P candidate
    case-split (inj₁ candidate<bound) =
      none-below _ candidate<bound
    case-split (inj₂ candidate≡bound) =
      subst (λ n → ¬ P n) (sym candidate≡bound)
        refutation

leastUpTo :
    (P : ℕ → Set)
  → ((candidate : ℕ) → Dec (P candidate))
  → (bound : ℕ)
  → P bound
  → LeastWitness P
leastUpTo P decide bound bound-witness
    with searchBelow P decide (suc bound)
... | found least = least
... | absent none =
  ⊥-elim (none bound (<ℕᶜ-suc bound) bound-witness)
