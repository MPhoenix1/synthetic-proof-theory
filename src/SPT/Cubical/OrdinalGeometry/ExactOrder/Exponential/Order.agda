{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.Order where

-- The exact countable order of ω^P on finite strictly decreasing supports
-- over an exact countable order P. The enumeration decodes a support length
-- and an index into exponent–coefficient pairs, admits exactly the valid
-- supports, and covers every support.

open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_; length)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order
import SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.WellFounded
  as HistoryOrder

module Power {A : Set} (P : Order.Order A) where

  module Histories = HistoryOrder.Power P
  module Supports = Histories.Supports

  private
    abstract
      indices : Order.Order (ℕ × ℕ)
      indices = Order.Sum.order Order.natural (λ _ → Order.natural)

    module I = Order.Order indices
    module Pair = Order.Order Supports.Pair.order

    -- Decoding is by structural recursion on a separately given length;
    -- the pair enumeration of Base combines the indices.
    run : ℕ → ℕ → Maybe Supports.Raw
    run zero _ = just []
    run (suc k) n with I.enum n
    ... | nothing = nothing
    ... | just (i , j) with Pair.enum i | run k j
    ...   | just x | just xs = just (x ∷ xs)
    ...   | nothing | _ = nothing
    ...   | just _ | nothing = nothing

    hit : (k n i j : ℕ) (x : A × ℕ) (xs : Supports.Raw)
      → I.enum n ≡ just (i , j) → Pair.enum i ≡ just x → run k j ≡ just xs
      → run (suc k) n ≡ just (x ∷ xs)
    hit k n i j x xs p q r rewrite p | q | r = refl

    runs : (xs : Supports.Raw) → Σ ℕ (λ n → run (length xs) n ≡ just xs)
    runs [] = zero , refl
    runs (x ∷ xs) with Pair.covers x | runs xs
    ... | i , p | j , q with I.covers (i , j)
    ...   | n , r = n , hit (length xs) n i j x xs r p q

  raw-enum : ℕ → Maybe Supports.Raw
  raw-enum n with I.enum n
  ... | nothing = nothing
  ... | just (k , c) = run k c

  raw-covers : (xs : Supports.Raw) → Σ ℕ (λ n → raw-enum n ≡ just xs)
  raw-covers xs with runs xs
  ... | c , q with I.covers (length xs , c)
  ...   | n , p = n , found
    where
    found : raw-enum n ≡ just xs
    found rewrite p = q

  private
    admit : (xs : Supports.Raw) → Maybe Supports.Term
    admit xs with Supports.check xs
    ... | yes q = just (xs , q)
    ... | no _ = nothing

    admitted : (x : Supports.Term) → admit (Supports.raw x) ≡ just x
    admitted (xs , p) with Supports.check xs
    ... | yes q = cong just (Supports.equal refl)
    ... | no q = ⊥-elim (q p)

  enum : ℕ → Maybe Supports.Term
  enum n with raw-enum n
  ... | nothing = nothing
  ... | just xs = admit xs

  covers : (x : Supports.Term) → Σ ℕ (λ n → enum n ≡ just x)
  covers x with raw-covers (Supports.raw x)
  ... | n , p = n , found
    where
    found : enum n ≡ just x
    found rewrite p = admitted x

  order : Order.Order Supports.Term
  order = record
    { _<_ = Supports._<_
    ; trans = Supports.trans
    ; wf = Histories.well-founded
    ; compare = Supports.compare
    ; enum = enum
    ; covers = covers
    }
