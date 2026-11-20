{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Judgment where

-- The judgments of the core theory, and its derivations as histories of a
-- signature generation. Raw contexts list types with their levels, each
-- type in the scope of the earlier ones (`Context`); a variable's level is
-- its entry's (`level`), its type the entry weakened to the whole context
-- (`lookup`). There are three judgment forms: well-formed contexts, terms
-- and equal terms, each term judgment with the level of its type
-- (`Judgment`). A type at level l is a term of the universe at l, and
-- equal types are equal terms there (`type`, `type-equal`). Judgments are
-- extensionally equal when their contexts and expressions are related by
-- TreeRel _＝_ (`Context-Rel`, `Judgment-Rel`, `context-refl`); an
-- expression and its substituted instances agree only up to this
-- relation, since children are functions. Rules given by their
-- conclusions and lists of premises form a signature over the judgments
-- (`rule-signature`). For any rules, typing is a signature generation
-- (Incidence.Boundary.Generation) whose boundary is the judgment to derive
-- and whose filler is trivial (`requests`, `typing`, by Boundary.Base's
-- `present-split`); the derivations of a judgment are the closed histories
-- of the rules at it (`Derivation`), which are the histories its filled
-- cell generates (`derivation-is-generated`).

open import SPT.Base
open import SPT.Foundation.Spaces using (DΣ)
open import SPT.Foundation.Spaces.Vertical using (family-displayed-space)
open import SPT.Incidence.Boundary.Base using (∂-Space; present-split; realize)
import SPT.Foundation.Signature.Sum as Sig
import SPT.Foundation.Tree as Tree
import SPT.Foundation.Tree.Relation as Relation
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Formers using (universe; weaken)

------------------------------------------------------------------------
-- Contexts

-- Γ ▸[ l ] A extends Γ by a variable of type A at level l.
data Context (C : Set) : ℕ → Set where
  ∅ : Context C 0
  _▸[_]_ :
    {n : ℕ} → Context C n → ℕ → Raw.Expression C n
    → Context C (suc n)

infixl 5 _▸[_]_

-- The level of a variable's type.
level : {C : Set} {n : ℕ} → Context C n → Fin n → ℕ
level ∅ ()
level (Γ ▸[ l ] A) fzero = l
level (Γ ▸[ l ] A) (fsuc i) = level Γ i

-- The type of a variable, weakened to the whole context.
lookup : {C : Set} {n : ℕ} → Context C n → Fin n → Raw.Expression C n
lookup ∅ ()
lookup (Γ ▸[ l ] A) fzero = weaken A
lookup (Γ ▸[ l ] A) (fsuc i) = weaken (lookup Γ i)

------------------------------------------------------------------------
-- Judgments

-- term Γ l t A: t has type A, a type at level l. term-equal Γ l t u A:
-- t and u are equal of type A.
data Judgment (C : Set) : Set where
  context : {n : ℕ} → Context C n → Judgment C
  term :
    {n : ℕ} → Context C n → ℕ → Raw.Expression C n → Raw.Expression C n
    → Judgment C
  term-equal :
    {n : ℕ} → Context C n → ℕ → Raw.Expression C n → Raw.Expression C n
    → Raw.Expression C n → Judgment C

-- A type at level l: a term of the universe at l.
type : {C : Set} {n : ℕ} → Context C n → ℕ → Raw.Expression C n → Judgment C
type Γ l A = term Γ (suc l) A (universe l)

-- Equal types at level l: equal terms of the universe at l.
type-equal :
  {C : Set} {n : ℕ} → Context C n → ℕ → Raw.Expression C n
  → Raw.Expression C n → Judgment C
type-equal Γ l A B = term-equal Γ (suc l) A B (universe l)

------------------------------------------------------------------------
-- Extensional equality of judgments

data Context-Rel {C : Set} : {n : ℕ} → Context C n → Context C n → Set where
  empty-rel : Context-Rel ∅ ∅
  extend-rel :
    {n l : ℕ} {Γ Δ : Context C n} {A B : Raw.Expression C n}
    → Context-Rel Γ Δ → Relation.TreeRel _＝_ A B
    → Context-Rel (Γ ▸[ l ] A) (Δ ▸[ l ] B)

data Judgment-Rel {C : Set} : Judgment C → Judgment C → Set where
  context-rel :
    {n : ℕ} {Γ Δ : Context C n} → Context-Rel Γ Δ
    → Judgment-Rel (context Γ) (context Δ)
  term-rel :
    {n l : ℕ} {Γ Δ : Context C n} {t t′ A A′ : Raw.Expression C n}
    → Context-Rel Γ Δ → Relation.TreeRel _＝_ t t′
    → Relation.TreeRel _＝_ A A′
    → Judgment-Rel (term Γ l t A) (term Δ l t′ A′)
  term-equal-rel :
    {n l : ℕ} {Γ Δ : Context C n} {t t′ u u′ A A′ : Raw.Expression C n}
    → Context-Rel Γ Δ → Relation.TreeRel _＝_ t t′
    → Relation.TreeRel _＝_ u u′ → Relation.TreeRel _＝_ A A′
    → Judgment-Rel (term-equal Γ l t u A) (term-equal Δ l t′ u′ A′)

-- Every context is extensionally equal to itself.
context-refl : {C : Set} {n : ℕ} (Γ : Context C n) → Context-Rel Γ Γ
context-refl ∅ = empty-rel
context-refl (Γ ▸[ l ] A) =
  extend-rel (context-refl Γ) (Relation.rel-refl (λ x → refl) A)

------------------------------------------------------------------------
-- Rules

-- Rules by their conclusions and lists of premises, as a signature.
rule-signature :
  {C : Set} (Rule : Judgment C → Set)
  → ({j : Judgment C} → Rule j → List (Judgment C))
  → Sig.Signature-Over (Judgment C) lzero lzero
rule-signature Rule premises = record
  { Operation = Rule
  ; Position = λ r → Fin (length (premises r))
  ; position-boundary = λ r p → list-lookup (premises r) p
  }

------------------------------------------------------------------------
-- Derivations, as generated histories

module _ {ℓo ℓp : Level} (C : Set)
  (rules : Sig.Signature-Over (Judgment C) ℓo ℓp)
  where

  -- The boundary is the judgment to derive; the filler is trivial.
  requests : DΣ lzero lzero
  requests = family-displayed-space (Judgment C) (λ j → 𝟙)

  typing :
    ∂-Space
      (family-displayed-space (Judgment C)
        (λ root → Sig.Signature-Over (Judgment C) ℓo ℓp))
      lzero lzero
  typing =
    present-split requests
      (record { on-base = λ j → j ; on-fiber = λ j u → rules })

  Derivation : Judgment C → Set (ℓo ⊔ ℓp)
  Derivation j = Tree.History (Sig.to-signature rules) j

  -- The derivations of a judgment are the closed histories that its filled
  -- cell of the typing generation realizes.
  derivation-is-generated : (j : Judgment C) →
    Tree.History (Sig.to-signature (pr₂ (realize typing (j , ⋆))))
      (pr₁ (realize typing (j , ⋆)))
    ＝ Derivation j
  derivation-is-generated j = refl
