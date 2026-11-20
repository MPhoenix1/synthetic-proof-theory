{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Nat.Identifications where

-- Any two identifications of the same natural numbers agree
-- (`ℕ-identifications-agree`), since ℕ is a set (Hedberg's `ℕ-is-set`):
--
--   p q : m ＝ n   gives   p ＝ q.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Hedberg using (ℕ-is-set)

ℕ-identifications-agree : {m n : ℕ} (p q : m ＝ n) → p ＝ q
ℕ-identifications-agree {m} {n} = ℕ-is-set m n
