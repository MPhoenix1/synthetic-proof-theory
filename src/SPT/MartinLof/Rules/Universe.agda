{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Rules.Universe where

-- The rule of the universes, as a signature over the judgments of the
-- core theory (`Rule`, `premises`, `rules`): the universe at level l is a
-- type at level l + 1. Its elements are the types at level l (Judgment's
-- `type`), so the universes are closed under a former exactly when that
-- former's formation rule concludes in them.

open import SPT.Base
import SPT.Foundation.Signature.Sum as Sig
open import SPT.MartinLof.Formers using (universe)
open import SPT.MartinLof.Judgment using
  (Context; Judgment; context; type; rule-signature)

data Rule (C : Set) : Judgment C → Set where
  formation :
    {n : ℕ} (Γ : Context C n) (l : ℕ)
    → Rule C (type Γ (suc l) (universe l))

premises : {C : Set} {j : Judgment C} → Rule C j → List (Judgment C)
premises (formation Γ l) = context Γ ∷ []

rules : (C : Set) → Sig.Signature-Over (Judgment C) lzero lzero
rules C = rule-signature (Rule C) premises
