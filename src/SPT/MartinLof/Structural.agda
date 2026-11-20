{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Structural where

-- The structural rules of the core theory, as a signature over its
-- judgments (`Rule`, `premises`, `rules`): the empty and extended
-- contexts, the assumption of a variable, conversion of terms and of equal
-- terms along equal types, reflexivity, symmetry and transitivity of
-- equal terms (for types: of equal terms of a universe), and the
-- extensional rule: a judgment holds when an extensionally equal one does
-- (Judgment's `JudgmentRel`). Each rule lists its premises; the signature
-- is Judgment's `rule-signature`.

open import SPT.Base
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Signature.Sum as Sig
import SPT.Foundation.Tree as Tree
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Judgment using
  (Context; ∅; _▸[_]_; level; lookup; Judgment; context; term; term-equal; type
  ; type-equal; Judgment-Rel; rule-signature)

data Rule (C : Set) : Judgment C → Set where
  empty : Rule C (context ∅)
  extend :
    {n : ℕ} (Γ : Context C n) (l : ℕ) (A : Raw.Expression C n)
    → Rule C (context (Γ ▸[ l ] A))
  assumption :
    {n : ℕ} (Γ : Context C n) (i : Fin n)
    → Rule C (term Γ (level Γ i) (Tree.hole i) (lookup Γ i))
  conversion :
    {n : ℕ} (Γ : Context C n) (l : ℕ) (t A B : Raw.Expression C n)
    → Rule C (term Γ l t B)
  equal-conversion :
    {n : ℕ} (Γ : Context C n) (l : ℕ) (t u A B : Raw.Expression C n)
    → Rule C (term-equal Γ l t u B)
  reflexive :
    {n : ℕ} (Γ : Context C n) (l : ℕ) (t A : Raw.Expression C n)
    → Rule C (term-equal Γ l t t A)
  symmetric :
    {n : ℕ} (Γ : Context C n) (l : ℕ) (t u A : Raw.Expression C n)
    → Rule C (term-equal Γ l u t A)
  transitive :
    {n : ℕ} (Γ : Context C n) (l : ℕ) (t u v A : Raw.Expression C n)
    → Rule C (term-equal Γ l t v A)
  extensional :
    (j : Judgment C) {j′ : Judgment C} → Judgment-Rel j j′ → Rule C j′

premises : {C : Set} {j : Judgment C} → Rule C j → List (Judgment C)
premises empty = []
premises (extend Γ l A) = type Γ l A ∷ []
premises (assumption Γ i) = context Γ ∷ []
premises (conversion Γ l t A B) = term Γ l t A ∷ type-equal Γ l A B ∷ []
premises (equal-conversion Γ l t u A B) =
  term-equal Γ l t u A ∷ type-equal Γ l A B ∷ []
premises (reflexive Γ l t A) = term Γ l t A ∷ []
premises (symmetric Γ l t u A) = term-equal Γ l t u A ∷ []
premises (transitive Γ l t u v A) =
  term-equal Γ l t u A ∷ term-equal Γ l u v A ∷ []
premises (extensional j r) = j ∷ []

rules : (C : Set) → Sig.Signature-Over (Judgment C) lzero lzero
rules C = rule-signature (Rule C) premises
