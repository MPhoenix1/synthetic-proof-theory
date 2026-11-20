{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Rules.Constant where

-- The rule of the constants, as a signature over the judgments of the
-- core theory (`Axioms`, `Rule`, `premises`, `rules`). The axioms assign
-- each constant c a closed type, its statement, at a level; in every
-- well-formed context c has its statement as type, once the statement is
-- a closed type at that level. Univalence at each level and the ambient
-- Mahlo rule enter the theory this way.

open import SPT.Base
import SPT.Foundation.Signature.Sum as Sig
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Formers using (constant; closed)
open import SPT.MartinLof.Judgment using
  (Context; ∅; Judgment; context; term; type; rule-signature)

-- The closed type of each constant, and its level.
record Axioms (C : Set) : Set where
  field
    level : C → ℕ
    statement : C → Raw.Expression C 0

data Rule (C : Set) (axioms : Axioms C) : Judgment C → Set where
  axiom :
    {n : ℕ} (Γ : Context C n) (c : C)
    → Rule C axioms
        (term Γ (Axioms.level axioms c) (constant c)
          (closed n (Axioms.statement axioms c)))

premises :
  {C : Set} {axioms : Axioms C} {j : Judgment C} → Rule C axioms j
  → List (Judgment C)
premises {C} {axioms} (axiom Γ c) =
  context Γ ∷ type ∅ (Axioms.level axioms c) (Axioms.statement axioms c)
  ∷ []

rules : (C : Set) → Axioms C → Sig.Signature-Over (Judgment C) lzero lzero
rules C axioms = rule-signature (Rule C axioms) premises
