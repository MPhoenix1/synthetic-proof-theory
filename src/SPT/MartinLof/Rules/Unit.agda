{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Rules.Unit where

-- The rules of the unit type, as a signature over the judgments of
-- the core theory (`Rule`, `premises`, `rules`): 1 is a type at level 0
-- (formation) with the point ⋆ (introduction), and every element of 1 is
-- ⋆ (uniqueness), so its eliminator is definable.

open import SPT.Base
import SPT.Foundation.Signature.Sum as Sig
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Formers using (unit; star)
open import SPT.MartinLof.Judgment using
  (Context; Judgment; context; term; term-equal; type; rule-signature)

data Rule (C : Set) : Judgment C → Set where
  formation : {n : ℕ} (Γ : Context C n) → Rule C (type Γ 0 unit)
  introduction : {n : ℕ} (Γ : Context C n) → Rule C (term Γ 0 star unit)
  uniqueness :
    {n : ℕ} (Γ : Context C n) (t : Raw.Expression C n)
    → Rule C (term-equal Γ 0 t star unit)

premises : {C : Set} {j : Judgment C} → Rule C j → List (Judgment C)
premises (formation Γ) = context Γ ∷ []
premises (introduction Γ) = context Γ ∷ []
premises (uniqueness Γ t) = term Γ 0 t unit ∷ []

rules : (C : Set) → Sig.Signature-Over (Judgment C) lzero lzero
rules C = rule-signature (Rule C) premises
