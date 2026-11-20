{-# OPTIONS --safe --without-K #-}

module SPT.IR.Indexed.General.Reducibility.Kripke.Discriminator where

-- Kripke reducibility on one stage with two edges, ₀ and ₁, over the toy
-- syntax of Reducibility/Discriminator at that stage (`stages`,
-- `syntaxes`). The base predicate reads an element at the edge ₀, and the
-- plus predicate reads the decoding of its recursive input at the
-- current stage (`predicates`). Both are stored at every arrow, so they
-- ask their element along every arrow: the constant element ₀ is
-- reducible at the base and at the plus code (`base-reducible`,
-- `plus-reducible`), the element returning its edge is at neither (the
-- arrow constant at ₁ reads ₁: `base-not-reducible`,
-- `plus-not-reducible`), and after restriction along the arrow constant
-- at ₀ it is at both (`base-restricted-reducible`,
-- `plus-restricted-reducible`). The plus element stores the restrictions
-- of the base element at every arrow (`plus`), and the eliminator counts
-- its constructors through them by refl (`depth`, `depth-plus`).

open import SPT.Base

open import SPT.Foundation.Kripke using
  (Stages; Stage; Arrow; arrow; identity; restrict)
open import SPT.IR.Indexed.General.Reducibility using (Syntax)
open import SPT.IR.Indexed.General.Reducibility.Discriminator using
  (syntax′)
open import SPT.IR.Indexed.General.Reducibility.Kripke using
  (Ma♯; U0♯; El♯; El0'♯; Fam♯; U+♯; El+'♯; Predicates; Map; Elp; El0'p;
   El+'p; restricted; MapElim)

stages : Stages lzero
stages = record { Stage = 𝟙 ; Edge = λ e c → 𝟚 }

syntaxes : Stage stages → Syntax lzero
syntaxes e = syntax′

predicates : Predicates stages syntaxes
predicates = record
  { U0p₀ = λ d u → 𝟙
  ; El0p₀ = λ d u up t → t ⋆ ₀ ＝ ₀
  ; U+p₀ = λ d A Ap B Bp C → 𝟙
  ; El+p₀ = λ d A Ap B Bp C Cp t → Ap d (identity stages) t
  }

constant₀ constant₁ : Arrow stages ⋆ ⋆
constant₀ = arrow (λ e g → ₀)
constant₁ = arrow (λ e g → ₁)

------------------------------------------------------------------------
-- The base element

point : U0♯ stages syntaxes ⋆
point = λ e g → ⋆

base : Map stages syntaxes predicates ⋆ (El0'♯ stages syntaxes ⋆ point)
base = El0'p stages syntaxes predicates ⋆ point (λ d φ → ⋆)

zero-element edge-element :
  El♯ stages syntaxes ⋆ (El0'♯ stages syntaxes ⋆ point)
zero-element = λ e g → ₀
edge-element = λ e g → g

base-reducible :
  Elp stages syntaxes predicates ⋆ (El0'♯ stages syntaxes ⋆ point) base
    zero-element
base-reducible = λ d φ → refl

base-not-reducible :
  Elp stages syntaxes predicates ⋆ (El0'♯ stages syntaxes ⋆ point) base
    edge-element
  → 𝟘
base-not-reducible w with w ⋆ constant₁
... | ()

base-restricted-reducible :
  Elp stages syntaxes predicates ⋆
    (El0'♯ stages syntaxes ⋆ point ·⟨ stages ⟩ constant₀)
    (restricted stages syntaxes predicates ⋆
      (El0'♯ stages syntaxes ⋆ point) base ⋆ constant₀)
    (edge-element ·⟨ stages ⟩ constant₀)
base-restricted-reducible = λ d φ → refl

------------------------------------------------------------------------
-- The plus element over it

family : Fam♯ stages syntaxes ⋆ (El0'♯ stages syntaxes ⋆ point)
family = λ e g → ⋆

operation :
  U+♯ stages syntaxes ⋆ (El0'♯ stages syntaxes ⋆ point) family
operation = λ e g → ⋆

plus :
  Map stages syntaxes predicates ⋆
    (El+'♯ stages syntaxes ⋆ (El0'♯ stages syntaxes ⋆ point) family
      operation)
plus =
  El+'p stages syntaxes predicates ⋆ (El0'♯ stages syntaxes ⋆ point)
    (restricted stages syntaxes predicates ⋆
      (El0'♯ stages syntaxes ⋆ point) base)
    family
    (λ d φ a ap →
      restricted stages syntaxes predicates ⋆
        (El0'♯ stages syntaxes ⋆ point) base d φ)
    operation (λ d φ → ⋆)

plus-reducible :
  Elp stages syntaxes predicates ⋆
    (El+'♯ stages syntaxes ⋆ (El0'♯ stages syntaxes ⋆ point) family
      operation)
    plus (λ e g → ₀)
plus-reducible = λ d φ d′ φ′ → refl

plus-not-reducible :
  Elp stages syntaxes predicates ⋆
    (El+'♯ stages syntaxes ⋆ (El0'♯ stages syntaxes ⋆ point) family
      operation)
    plus (λ e g → g)
  → 𝟘
plus-not-reducible w with w ⋆ constant₁ ⋆ (identity stages)
... | ()

plus-restricted-reducible :
  Elp stages syntaxes predicates ⋆
    (El+'♯ stages syntaxes ⋆ (El0'♯ stages syntaxes ⋆ point) family
      operation ·⟨ stages ⟩ constant₀)
    (restricted stages syntaxes predicates ⋆
      (El+'♯ stages syntaxes ⋆ (El0'♯ stages syntaxes ⋆ point) family
        operation)
      plus ⋆ constant₀)
    ((λ e g → g) ·⟨ stages ⟩ constant₀)
plus-restricted-reducible = λ d φ d′ φ′ → refl

------------------------------------------------------------------------
-- Counting constructors

depth :
  (c : Stage stages) (m : Ma♯ stages syntaxes c)
  → Map stages syntaxes predicates c m → ℕ
depth =
  MapElim stages syntaxes predicates (λ c m mp → ℕ) (λ c u up → 0)
    (λ c A Ap h B Bp k C Cp → suc (h c (identity stages)))

depth-plus :
  depth ⋆
    (El+'♯ stages syntaxes ⋆ (El0'♯ stages syntaxes ⋆ point) family
      operation)
    plus
  ＝ 1
depth-plus = refl
