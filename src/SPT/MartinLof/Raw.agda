{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Raw where

-- The raw expressions of the core theory interpreted in the simplicial model
-- (Cubical/Mahlo/Simplicial.md): Martin-Löf type theory with universes
-- at closed levels, Lift, Π, Σ, identity types, W, 0, 1, +, ℕ, and named
-- constants for its axioms, as a binding signature (`Former`, `Premise`,
-- `depth`, `binding`). Terms and types share one syntax: a type at level l
-- is a term of the universe at l, as in Agda, where every type has a sort.
-- Introductions and eliminations carry the types they need as premises,
-- and every former records the levels of the types it carries, so that an
-- expression determines the types of its parts and their universes. A
-- premise records how many variables it binds: a codomain one, J's motive
-- two (the end point and the path), W's induction method three (shape,
-- children and hypotheses). Expressions are the trees of
-- Foundation.Tree.Binding (`Expression`).

open import SPT.Base hiding (lift; lower; zero)
import SPT.Foundation.Tree.Binding as Binding

------------------------------------------------------------------------
-- Formers

-- C names the constants (axioms) of the theory. The numbers are the levels
-- of the types a former carries: for Π, Σ, W and + those of the two
-- families, for J, W-induction, case and ℕ-induction also the motive's.
data Former (C : Set) : Set where
  universe : ℕ → Former C
  lifted lift lower : ℕ → ℕ → Former C
  pi lambda application : ℕ → ℕ → Former C
  sigma pair first second : ℕ → ℕ → Former C
  identity reflexivity : ℕ → Former C
  path-induction : ℕ → ℕ → Former C
  tree supremum : ℕ → ℕ → Former C
  tree-induction : ℕ → ℕ → ℕ → Former C
  empty : Former C
  absurd : ℕ → Former C
  unit star : Former C
  sum left right : ℕ → ℕ → Former C
  case : ℕ → ℕ → ℕ → Former C
  natural zero successor : Former C
  natural-induction : ℕ → Former C
  constant : C → Former C
  -- Kubánek's Mahlo subuniverses at level i (Canonicity of the Mahlo
  -- Universe, MSc thesis, Chalmers 2025, §3.3): for a base U0 with a
  -- decoding El0 and an operator U+ with a decoding El+, the subuniverse
  -- Ma, its codes El0' u and El+' A B C, the decoding El, and induction
  -- maElim into a motive at level j.
  subuniverse inclusion closure decoding : ℕ → Former C
  subuniverse-induction : ℕ → ℕ → Former C

------------------------------------------------------------------------
-- Premises

data Premise {C : Set} : Former C → Set where
  -- Lift k of a type A at level m, its introduction and elimination.
  lifted-type : {m k : ℕ} → Premise (lifted m k)
  lift-type lift-term : {m k : ℕ} → Premise (lift m k)
  lower-type lower-term : {m k : ℕ} → Premise (lower m k)
  -- Π A B, λ_{A,B} t, app_{A,B} f a.
  pi-domain pi-codomain : {m k : ℕ} → Premise (pi m k)
  lambda-domain lambda-codomain lambda-body :
    {m k : ℕ} → Premise (lambda m k)
  application-domain application-codomain :
    {m k : ℕ} → Premise (application m k)
  application-function application-argument :
    {m k : ℕ} → Premise (application m k)
  -- Σ A B, pair_{A,B} a b, fst_{A,B} p, snd_{A,B} p.
  sigma-first sigma-second : {m k : ℕ} → Premise (sigma m k)
  pair-first-type pair-second-type pair-first pair-second :
    {m k : ℕ} → Premise (pair m k)
  first-first-type first-second-type first-pair :
    {m k : ℕ} → Premise (first m k)
  second-first-type second-second-type second-pair :
    {m k : ℕ} → Premise (second m k)
  -- Id_A a b, refl_A a, J_{A,C} a d b p.
  identity-type identity-left identity-right :
    {m : ℕ} → Premise (identity m)
  reflexivity-type reflexivity-point : {m : ℕ} → Premise (reflexivity m)
  induction-type induction-motive : {m k : ℕ} → Premise (path-induction m k)
  induction-base induction-method : {m k : ℕ} → Premise (path-induction m k)
  induction-end induction-path : {m k : ℕ} → Premise (path-induction m k)
  -- W A B, sup_{A,B} a f, and W-induction with motive and method.
  tree-shape tree-position : {m k : ℕ} → Premise (tree m k)
  supremum-shape-type supremum-position-type :
    {m k : ℕ} → Premise (supremum m k)
  supremum-shape supremum-children : {m k : ℕ} → Premise (supremum m k)
  recursion-shape-type recursion-position-type :
    {m k l : ℕ} → Premise (tree-induction m k l)
  recursion-motive recursion-method recursion-tree :
    {m k l : ℕ} → Premise (tree-induction m k l)
  -- 0 and its elimination; 1 and its point.
  absurd-motive absurd-term : {k : ℕ} → Premise (absurd k)
  -- A + B, inl_{A,B} a, inr_{A,B} b, case.
  sum-left sum-right : {m k : ℕ} → Premise (sum m k)
  left-left-type left-right-type left-term : {m k : ℕ} → Premise (left m k)
  right-left-type right-right-type right-term :
    {m k : ℕ} → Premise (right m k)
  case-left-type case-right-type case-motive :
    {m k l : ℕ} → Premise (case m k l)
  case-left-method case-right-method case-term :
    {m k l : ℕ} → Premise (case m k l)
  -- ℕ: successor and induction.
  successor-term : Premise successor
  natural-motive natural-base natural-step natural-term :
    {l : ℕ} → Premise (natural-induction l)
  -- The subuniverse: its four parameters at each of its formers, then the
  -- point of El0' u, the code, family and point of El+' A B C, the code
  -- El decodes, and maElim's motive, its two methods and its code. Each
  -- is a term; the motive and the methods are functions.
  subuniverse-base subuniverse-base-decoding subuniverse-step :
    {i : ℕ} → Premise (subuniverse i)
  subuniverse-step-decoding :
    {i : ℕ} → Premise (subuniverse i)
  inclusion-base inclusion-base-decoding inclusion-step :
    {i : ℕ} → Premise (inclusion i)
  inclusion-step-decoding inclusion-point :
    {i : ℕ} → Premise (inclusion i)
  closure-base closure-base-decoding closure-step closure-step-decoding :
    {i : ℕ} → Premise (closure i)
  closure-code closure-family closure-point :
    {i : ℕ} → Premise (closure i)
  decoding-base decoding-base-decoding decoding-step decoding-step-decoding :
    {i : ℕ} → Premise (decoding i)
  decoding-code :
    {i : ℕ} → Premise (decoding i)
  subinduction-base subinduction-base-decoding subinduction-step :
    {i j : ℕ} → Premise (subuniverse-induction i j)
  subinduction-step-decoding subinduction-motive subinduction-inclusion :
    {i j : ℕ} → Premise (subuniverse-induction i j)
  subinduction-closure subinduction-code :
    {i j : ℕ} → Premise (subuniverse-induction i j)

------------------------------------------------------------------------
-- Binding depth of each premise

depth : {C : Set} (o : Former C) → Premise o → ℕ
depth _ lifted-type = 0
depth _ lift-type = 0
depth _ lift-term = 0
depth _ lower-type = 0
depth _ lower-term = 0
depth _ pi-domain = 0
depth _ pi-codomain = 1
depth _ lambda-domain = 0
depth _ lambda-codomain = 1
depth _ lambda-body = 1
depth _ application-domain = 0
depth _ application-codomain = 1
depth _ application-function = 0
depth _ application-argument = 0
depth _ sigma-first = 0
depth _ sigma-second = 1
depth _ pair-first-type = 0
depth _ pair-second-type = 1
depth _ pair-first = 0
depth _ pair-second = 0
depth _ first-first-type = 0
depth _ first-second-type = 1
depth _ first-pair = 0
depth _ second-first-type = 0
depth _ second-second-type = 1
depth _ second-pair = 0
depth _ identity-type = 0
depth _ identity-left = 0
depth _ identity-right = 0
depth _ reflexivity-type = 0
depth _ reflexivity-point = 0
depth _ induction-type = 0
depth _ induction-motive = 2
depth _ induction-base = 0
depth _ induction-method = 0
depth _ induction-end = 0
depth _ induction-path = 0
depth _ tree-shape = 0
depth _ tree-position = 1
depth _ supremum-shape-type = 0
depth _ supremum-position-type = 1
depth _ supremum-shape = 0
depth _ supremum-children = 0
depth _ recursion-shape-type = 0
depth _ recursion-position-type = 1
depth _ recursion-motive = 1
depth _ recursion-method = 3
depth _ recursion-tree = 0
depth _ absurd-motive = 1
depth _ absurd-term = 0
depth _ sum-left = 0
depth _ sum-right = 0
depth _ left-left-type = 0
depth _ left-right-type = 0
depth _ left-term = 0
depth _ right-left-type = 0
depth _ right-right-type = 0
depth _ right-term = 0
depth _ case-left-type = 0
depth _ case-right-type = 0
depth _ case-motive = 1
depth _ case-left-method = 1
depth _ case-right-method = 1
depth _ case-term = 0
depth _ successor-term = 0
depth _ natural-motive = 1
depth _ natural-base = 0
depth _ natural-step = 2
depth _ natural-term = 0
depth _ subuniverse-base = 0
depth _ subuniverse-base-decoding = 0
depth _ subuniverse-step = 0
depth _ subuniverse-step-decoding = 0
depth _ inclusion-base = 0
depth _ inclusion-base-decoding = 0
depth _ inclusion-step = 0
depth _ inclusion-step-decoding = 0
depth _ inclusion-point = 0
depth _ closure-base = 0
depth _ closure-base-decoding = 0
depth _ closure-step = 0
depth _ closure-step-decoding = 0
depth _ closure-code = 0
depth _ closure-family = 0
depth _ closure-point = 0
depth _ decoding-base = 0
depth _ decoding-base-decoding = 0
depth _ decoding-step = 0
depth _ decoding-step-decoding = 0
depth _ decoding-code = 0
depth _ subinduction-base = 0
depth _ subinduction-base-decoding = 0
depth _ subinduction-step = 0
depth _ subinduction-step-decoding = 0
depth _ subinduction-motive = 0
depth _ subinduction-inclusion = 0
depth _ subinduction-closure = 0
depth _ subinduction-code = 0

------------------------------------------------------------------------
-- The binding signature and its expressions

binding : (C : Set) → Binding.Binding lzero lzero
binding C = record
  { Operation = Former C
  ; Premise = Premise
  ; depth = depth
  }

Expression : (C : Set) → ℕ → Set
Expression C = Binding.Expression (binding C)
