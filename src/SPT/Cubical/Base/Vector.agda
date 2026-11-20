{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Base.Vector where

-- Vectors are lists of a given length: `Vec A n` has `[]` at length zero
-- and `x ∷ xs` at length `suc n` for `xs` of length `n`. The constructors
-- share the names and fixity of the list constructors, and Agda tells them
-- apart by type. The entry of a vector at a position `i : Fin n` is
-- `vector-lookup xs i`.

open import SPT.Cubical.Base.Universes
open import SPT.Cubical.Base.Natural using (suc; zero; ℕ)
open import SPT.Cubical.Base.Fin using (Fin; fsuc; fzero)

infixr 10 _∷_

data Vec {ℓ : Level} (A : Set ℓ) : ℕ → Set ℓ where
  [] : Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

module _ {ℓ : Level} {A : Set ℓ} where

  vector-lookup : {n : ℕ} → Vec A n → Fin n → A
  vector-lookup (x ∷ xs) fzero = x
  vector-lookup (x ∷ xs) (fsuc i) = vector-lookup xs i
