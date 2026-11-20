{-# OPTIONS --safe --without-K #-}

module SPT.Base where

-- The base is the vocabulary every SPT module is written in: universes and
-- lifting, functions, the empty type and negation, identity types with
-- transport, path induction and their groupoid laws, the unit type,
-- dependent pairs and products, disjoint sums, trichotomy, decidability, the
-- two-point type, the natural numbers with their order, pairing and
-- elimination, finite types and environments, lists, vectors, partial
-- values, inclusion of predicates, and induction on the arguments of an
-- introduction. Each type former is given once, in its own module, with one
-- notation. The identity type, Σ, the unit type, the two-point type, ℕ,
-- lists and Maybe are the types of Agda's own `Agda.Builtin` modules under
-- SPT's names, so the standard library shares them; SPT imports no module of
-- the standard library, and binds no builtin of its own.
--
-- SPT.Base is the one module that is opened whole. Every other import names
-- what it uses.
--
-- Precedence. Every operator of SPT takes its fixity from this table, in
-- the manner of agda-unimath's MIXFIX-OPERATORS.md. Lower levels bind more
-- loosely. The rows marked reserved fix the classes of the operators of
-- proof theory and ordinal analysis before their modules exist, so that
-- Γ ▻ A ∧ B ⊢ C reads as (Γ ▻ (A ∧ B)) ⊢ C, and A ∧ B ＝ C as an
-- identification of formulas.
--
--   level   class: operators
--   −1      binders (reserved; Σ is written prefix, `Σ A (λ x → B)`)
--   0, 1    chains: `_＝⟨_⟩_` (right), `_∎`
--   3       pairing: `_,_` (right)
--   4       judgements (reserved): `Γ ⊢ A`, `Γ ⊢⟨ α ⟩ A`
--   5       cedents, maps of types (reserved): `Γ ▻ A` (left), `A ≅ B`,
--             `A ↪ B`; inclusion of predicates: `_⊆ᵖ_`
--   6       identification: `_＝_`, `_≠_`; equivalence of predicates:
--             `_≈ᵖ_`; membership in a list: `_∈ˡ_`
--   10      sums, lists: `_⊎_`, `_∷_`, `_++_` (right)
--   15      products, composition: `_×_` (right), `_∘_` (right),
--             `_∙_` (left)
--   25      unary type operators: `¬_`, `_⁻¹`
--   30      order of numbers and ordinals: `_≤ℕˢ_`, `_<ℕˢ_`, `_≤ℕ′_`,
--             `_<ℕᶜ_`, `_≤ℕᶜ_`; reserved: `x ≺⟨ P ⟩ y`, `⊴`, `⊲`
--   32      embeddings of finite types: `_↑ˡ_` (left), `_↑ʳ_` (right)
--   35      addition, maximum: `_+_`, `_⊔ℕ_` (left); reserved: ordinal sum
--   36      subtraction: `_∸_` (left)
--   40      multiplication: `_*_` (left); reserved: ordinal product
--   45      exponentiation (reserved): `ω^_`, `_^_` (right)
--   46      successors: `1+_`
--   50–59   connectives of formulas (reserved): `⇒` below `∨` below `∧`
--             below `¬`
--   60      atoms of formulas (reserved): membership and equality of terms
--   70      numerals of finite types: `#_`
--
-- A structure-dependent operator is a top-level function with the
-- structure in brackets, declared by syntax (x ≺⟨ P ⟩ y), at the level of
-- its row.

open import SPT.Base.Universes public
open import SPT.Base.Functions public
open import SPT.Base.Empty public
open import SPT.Base.Identity public
open import SPT.Base.Unit public
open import SPT.Base.Sigma public
open import SPT.Base.Sum public
open import SPT.Base.Trichotomy public
open import SPT.Base.Decidable public
open import SPT.Base.Two public
open import SPT.Base.Natural public
open import SPT.Base.Fin public
open import SPT.Base.List public
open import SPT.Base.Maybe public
open import SPT.Base.Vector public
open import SPT.Base.Predicate public
open import SPT.Base.Induction public
