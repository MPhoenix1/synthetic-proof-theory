{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Nat.Identifications where

-- Any two identifications of the same natural numbers agree
-- (`ℕ-identifications-agree`), since ℕ is a set (Hedberg's `ℕ-is-set`):
--
--   p q : m ＝ n   gives   p ＝ q.

open import SPT.Base
open import SPT.Foundation.Hedberg using (ℕ-is-set)

ℕ-identifications-agree : {m n : ℕ} (p q : m ＝ n) → p ＝ q
ℕ-identifications-agree {m} {n} = ℕ-is-set m n
