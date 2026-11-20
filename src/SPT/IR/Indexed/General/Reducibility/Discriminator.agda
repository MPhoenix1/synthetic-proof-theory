{-# OPTIONS --safe --without-K #-}

module SPT.IR.Indexed.General.Reducibility.Discriminator where

-- A toy syntax and predicates for Reducibility (`syntax′`, `predicates`):
-- codes are numbers, every code has the two closed terms of 𝟚, El0'
-- returns 0 and El+' A B C returns suc A. A base term is reducible when
-- it is ₀, and a term of El+' A B C when it is reducible at A, so the
-- plus predicate reads the decoding of a recursive input. The base
-- element decodes to that predicate (`base-reducible`,
-- `base-not-reducible`); the plus element over it reads it back through
-- its child (`plus-reducible`, `plus-not-reducible`); MapElim counts the
-- constructors by refl (`depth`, `depth-plus`). So both parameter records
-- are inhabited and Map, Elp and MapElim compute.

open import SPT.Base

open import SPT.IR.Indexed.General.Reducibility using
  (Syntax; Predicates; Map; Elp; El0'p; El+'p; MapElim)

syntax′ : Syntax lzero
syntax′ = record
  { Ma = ℕ
  ; El = λ m → 𝟚
  ; U0 = 𝟙
  ; El0' = λ u → 0
  ; Fam = λ A → 𝟙
  ; _$$_ = λ B a → 0
  ; U+ = λ A B → 𝟙
  ; El+' = λ A B C → suc A
  }

predicates : Predicates syntax′
predicates = record
  { U0p = λ u → 𝟙
  ; El0p = λ u up t → t ＝ ₀
  ; U+p = λ A Ap B Bp C → 𝟙
  ; El+p = λ A Ap B Bp C Cp t → Ap t
  }

base-element : Map syntax′ predicates 0
base-element = El0'p syntax′ predicates ⋆ ⋆

plus-element : Map syntax′ predicates 1
plus-element =
  El+'p syntax′ predicates 0 base-element ⋆ (λ a ap → base-element) ⋆ ⋆

base-reducible : Elp syntax′ predicates 0 base-element ₀
base-reducible = refl

base-not-reducible : Elp syntax′ predicates 0 base-element ₁ → 𝟘
base-not-reducible ()

plus-reducible : Elp syntax′ predicates 1 plus-element ₀
plus-reducible = refl

plus-not-reducible : Elp syntax′ predicates 1 plus-element ₁ → 𝟘
plus-not-reducible ()

depth : (m : ℕ) → Map syntax′ predicates m → ℕ
depth =
  MapElim syntax′ predicates (λ m mp → ℕ) (λ u up → 0)
    (λ A Ap h B Bp k C Cp → suc h)

depth-plus : depth 1 plus-element ＝ 1
depth-plus = refl
