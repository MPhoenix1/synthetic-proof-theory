{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Nat.Least where

-- A least witness of a predicate `P` on ℕ is a number with a proof of `P` and a
-- refutation of `P` at every smaller number, in the computational order `<ℕᶜ`.
-- For a decidable predicate, bounded search below a bound either finds a least
-- witness or refutes `P` below the bound (`searchBelow`). Searching below `suc
-- b` from a witness at `b` therefore always finds a least witness
-- (`leastUpTo`).

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Nat.Order using
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
  absent : ((candidate : ℕ) → candidate <ℕᶜ bound → ¬ P candidate) →
    SearchBelow P bound

------------------------------------------------------------------------
-- Properties

-- The search below `suc b` keeps the result below `b`, and decides `P b` only
-- when nothing was found below it (`extend-search`). A search below `suc b`
-- that found nothing would refute a witness at `b`, so with such a witness it
-- ends in a least witness (`least-from-search`).

module _ {P : ℕ → Set} where

  extend-search : (bound : ℕ) → SearchBelow P bound →
    is-decidable (P bound) → SearchBelow P (suc bound)
  extend-search bound (found least) _ = found least
  extend-search bound (absent none-below) (inl proof) =
    found (least-witness bound proof none-below)
  extend-search bound (absent none-below) (inr refutation) =
    absent (λ candidate candidate<suc-bound →
      cases
        (λ candidate<bound → none-below candidate candidate<bound)
        (λ candidate≡bound →
          transport (λ n → ¬ P n) (candidate≡bound ⁻¹) refutation)
        (<ℕᶜ-suc-split candidate bound candidate<suc-bound))

  least-from-search : (bound : ℕ) → P bound →
    SearchBelow P (suc bound) → LeastWitness P
  least-from-search bound bound-witness (found least) = least
  least-from-search bound bound-witness (absent none) =
    𝟘-elim (none bound (<ℕᶜ-suc bound) bound-witness)

module _ (P : ℕ → Set)
  (decide : (candidate : ℕ) → is-decidable (P candidate)) where

  searchBelow : (bound : ℕ) → SearchBelow P bound
  searchBelow zero =
    absent (λ candidate candidate<zero →
      𝟘-elim (cmpℕ<zero-impossible candidate candidate<zero))
  searchBelow (suc bound) =
    extend-search bound (searchBelow bound) (decide bound)

  leastUpTo : (bound : ℕ) → P bound → LeastWitness P
  leastUpTo bound bound-witness =
    least-from-search bound bound-witness (searchBelow (suc bound))
