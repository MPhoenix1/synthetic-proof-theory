{-# OPTIONS --safe --without-K --no-projection-like #-}

module SPT.MartinLof.Model.Russell where

-- The base of a model of the core theory: a natural model whose types are
-- the terms of a tower of Russell universes (`Russell`).
--
-- Contexts and substitutions form a category with a terminal context.
-- Terms over a context are contravariant in it, and each term has the
-- term coding its type (`type-of`), naturally. The universe at level l is
-- a closed term whose type is the universe at l + 1. A type at level l is
-- a term of type that universe (`Code`), as in the core theory. A context
-- extends by any term (`_▸_`), with its projection and its variable. A
-- substitution extends by a term of the right type (`extend`), and two
-- substitutions into an extension agree when their projections and
-- variables do. Replacing the last variable by a term along a
-- substitution is total (`_[_⨾_]`), and agrees with extending where the
-- term has the right type.
--
-- Operations are total, and their laws hold where the arguments have the
-- types the core theory gives them; a model may give any value elsewhere.
-- Only `extend` takes a proof, since a substitution into an extension
-- need not exist otherwise.
--
-- In the simplicial model (Kapulkin–Lumsdaine) a term at level l is a map
-- into the total space of the universe at l, and its type is its
-- composite with the projection, read in the universe above. Values off
-- the typed arguments are chosen classically.
--
-- Derived (`module _`): `Code` and its stability (`code-[]`, `closed-code`),
-- the section of a term (`section`), and a substitution taken under a
-- binder (`under`, with its typing proof `under-type`).

open import SPT.Base hiding (_∘_; id)

record Russell (ℓ : Level) : Set (lsuc ℓ) where
  infixr 15 _∘_
  infixl 25 _[_] _[_⨾_]
  infixl 5 _▸_

  ----------------------------------------------------------------------
  -- Contexts and substitutions

  field
    Ob : Set ℓ
    Hom : Ob → Ob → Set ℓ
    id : {Γ : Ob} → Hom Γ Γ
    _∘_ : {Γ Δ Θ : Ob} → Hom Δ Θ → Hom Γ Δ → Hom Γ Θ
    id-left : {Γ Δ : Ob} (σ : Hom Γ Δ) → id ∘ σ ＝ σ
    id-right : {Γ Δ : Ob} (σ : Hom Γ Δ) → σ ∘ id ＝ σ
    associative :
      {Γ Δ Θ Ξ : Ob} (σ : Hom Θ Ξ) (δ : Hom Δ Θ) (ν : Hom Γ Δ)
      → (σ ∘ δ) ∘ ν ＝ σ ∘ (δ ∘ ν)
    ◇ : Ob
    ε : (Γ : Ob) → Hom Γ ◇
    ε-unique : {Γ : Ob} (σ : Hom Γ ◇) → σ ＝ ε Γ

  ----------------------------------------------------------------------
  -- Terms, their types, and the universes

  field
    Tm : Ob → Set ℓ
    _[_] : {Γ Δ : Ob} → Tm Δ → Hom Γ Δ → Tm Γ
    [id] : {Γ : Ob} (t : Tm Γ) → t [ id ] ＝ t
    [∘] :
      {Γ Δ Θ : Ob} (t : Tm Θ) (σ : Hom Δ Θ) (δ : Hom Γ Δ)
      → t [ σ ∘ δ ] ＝ t [ σ ] [ δ ]
    type-of : {Γ : Ob} → Tm Γ → Tm Γ
    type-of-[] :
      {Γ Δ : Ob} (t : Tm Δ) (σ : Hom Γ Δ)
      → type-of (t [ σ ]) ＝ type-of t [ σ ]
    universe : ℕ → Tm ◇
    universe-type : (l : ℕ) → type-of (universe l) ＝ universe (suc l)

  ----------------------------------------------------------------------
  -- Context extension

  field
    _▸_ : (Γ : Ob) → Tm Γ → Ob
    p : {Γ : Ob} {a : Tm Γ} → Hom (Γ ▸ a) Γ
    q : {Γ : Ob} (a : Tm Γ) → Tm (Γ ▸ a)
    q-type :
      {Γ : Ob} (l : ℕ) (a : Tm Γ) → type-of a ＝ universe l [ ε Γ ]
      → type-of (q a) ＝ a [ p ]
    extend :
      {Γ Δ : Ob} (a : Tm Γ) (σ : Hom Δ Γ) (t : Tm Δ) → type-of t ＝ a [ σ ]
      → Hom Δ (Γ ▸ a)
    p-extend :
      {Γ Δ : Ob} (a : Tm Γ) (σ : Hom Δ Γ) (t : Tm Δ)
      (e : type-of t ＝ a [ σ ])
      → p ∘ extend a σ t e ＝ σ
    q-extend :
      {Γ Δ : Ob} (l : ℕ) (a : Tm Γ) (σ : Hom Δ Γ) (t : Tm Δ)
      (e : type-of t ＝ a [ σ ]) → type-of a ＝ universe l [ ε Γ ]
      → q a [ extend a σ t e ] ＝ t
    extend-unique :
      {Γ Δ : Ob} (a : Tm Γ) (τ τ′ : Hom Δ (Γ ▸ a)) → p ∘ τ ＝ p ∘ τ′
      → q a [ τ ] ＝ q a [ τ′ ] → τ ＝ τ′

  ----------------------------------------------------------------------
  -- Replacing the last variable

  field
    _[_⨾_] :
      {Γ Δ : Ob} {a : Tm Γ} → Tm (Γ ▸ a) → Hom Δ Γ → Tm Δ → Tm Δ
    [⨾] :
      {Γ Δ : Ob} (a : Tm Γ) (M : Tm (Γ ▸ a)) (σ : Hom Δ Γ) (t : Tm Δ)
      (e : type-of t ＝ a [ σ ])
      → M [ σ ⨾ t ] ＝ M [ extend a σ t e ]

------------------------------------------------------------------------
-- Derived notions

module _ {ℓ : Level} (R : Russell ℓ) where

  open Russell R

  -- a is a type at level l: a term of the universe at l.
  Code : {Γ : Ob} → ℕ → Tm Γ → Set ℓ
  Code {Γ} l a = type-of a ＝ universe l [ ε Γ ]

  -- Types at level l stay types at level l under substitution.
  code-[] :
    {Γ Δ : Ob} (l : ℕ) (a : Tm Γ) (σ : Hom Δ Γ) → Code l a
    → Code l (a [ σ ])
  code-[] {Γ} {Δ} l a σ ta =
    type-of-[] a σ ∙
      (ap (λ t → t [ σ ]) ta ∙
        ([∘] (universe l) (ε Γ) σ ⁻¹ ∙
          ap (λ τ → universe l [ τ ]) (ε-unique (ε Γ ∘ σ))))

  -- A closed type at level l, in any context.
  closed-code :
    {Γ : Ob} (l : ℕ) (a : Tm ◇) (σ : Hom Γ ◇)
    → type-of a ＝ universe l → Code l (a [ σ ])
  closed-code l a σ ta =
    type-of-[] a σ ∙
      (ap (λ t → t [ σ ]) ta ∙
        ap (λ τ → universe l [ τ ]) (ε-unique σ))

  -- The section of a term x of type a.
  section : {Γ : Ob} (a x : Tm Γ) → type-of x ＝ a → Hom Γ (Γ ▸ a)
  section a x tx = extend a id x (tx ∙ [id] a ⁻¹)

  -- The variable of a substituted type has the type taken along p.
  under-type :
    {Γ Δ : Ob} (l : ℕ) (a : Tm Γ) (σ : Hom Δ Γ) → Code l a
    → type-of (q (a [ σ ])) ＝ a [ σ ∘ p ]
  under-type l a σ ta =
    q-type l (a [ σ ]) (code-[] l a σ ta) ∙ [∘] a σ p ⁻¹

  -- σ taken under a binder of a type a at level l.
  under :
    {Γ Δ : Ob} (l : ℕ) (a : Tm Γ) (σ : Hom Δ Γ) → Code l a
    → Hom (Δ ▸ a [ σ ]) (Γ ▸ a)
  under l a σ ta = extend a (σ ∘ p) (q (a [ σ ])) (under-type l a σ ta)
