{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Formers where

-- The formers of the core theory as operations on its raw expressions, and
-- the renamings and substitutions its rules use. Each former is a node of
-- the binding signature with a named family of children (`Children`, one
-- family per former); a premise binding d variables is an expression of
-- scope d + n read under the binders by Binding's `bound`. Weakening: by
-- one variable (`weaken`), by d variables under c bound ones
-- (`weaken-past`), of a closed expression (`closed`). Substitution: a
-- substitution extended by a last variable (`extended`), the variables of
-- a scope inside a larger one (`shifted`), and the last one, two or three
-- variables replaced (`instantiate`, `instantiate₂`, `instantiate₃`), also
-- under further variables (`instantiate-past`).

open import SPT.Base hiding (lift; lower; zero)
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Signature.Sum as Sig
import SPT.Foundation.Tree as Tree
import SPT.Foundation.Tree.Binding as Binding
import SPT.MartinLof.Raw as Raw

------------------------------------------------------------------------
-- Children

-- The children of a node of the former o in scope n: at each premise, a
-- tree at the depth of the variables the premise binds.
Children : (C : Set) → ℕ → Raw.Former C → Set
Children C n o =
  (p : Raw.Premise o)
  → Tree.Tree (Sig.to-signature (Binding.over (Raw.binding C)))
      (Binding.Variable n) (Raw.depth o p + 0)

------------------------------------------------------------------------
-- Universes and Lift

universe-children :
  {C : Set} {n : ℕ} (l : ℕ) → Children C n (Raw.universe l)
universe-children l ()

universe : {C : Set} {n : ℕ} → ℕ → Raw.Expression C n
universe l = Tree.node (Raw.universe l) (universe-children l)

lifted-children :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n
  → Children C n (Raw.lifted m k)
lifted-children m k A Raw.lifted-type = A

lifted :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n → Raw.Expression C n
lifted m k A = Tree.node (Raw.lifted m k) (lifted-children m k A)

lift-children :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n → Raw.Expression C n
  → Children C n (Raw.lift m k)
lift-children m k A a Raw.lift-type = A
lift-children m k A a Raw.lift-term = a

lift :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n → Raw.Expression C n
  → Raw.Expression C n
lift m k A a = Tree.node (Raw.lift m k) (lift-children m k A a)

lower-children :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n → Raw.Expression C n
  → Children C n (Raw.lower m k)
lower-children m k A x Raw.lower-type = A
lower-children m k A x Raw.lower-term = x

lower :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n → Raw.Expression C n
  → Raw.Expression C n
lower m k A x = Tree.node (Raw.lower m k) (lower-children m k A x)

------------------------------------------------------------------------
-- Π

pi-children :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc n) → Children C n (Raw.pi m k)
pi-children m k A B Raw.pi-domain = A
pi-children {C} {n} m k A B Raw.pi-codomain =
  Binding.bound (Raw.binding C) n 1 B

pi :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc n) → Raw.Expression C n
pi m k A B = Tree.node (Raw.pi m k) (pi-children m k A B)

lambda-children :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc n) → Raw.Expression C (suc n)
  → Children C n (Raw.lambda m k)
lambda-children m k A B t Raw.lambda-domain = A
lambda-children {C} {n} m k A B t Raw.lambda-codomain =
  Binding.bound (Raw.binding C) n 1 B
lambda-children {C} {n} m k A B t Raw.lambda-body =
  Binding.bound (Raw.binding C) n 1 t

lambda :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc n) → Raw.Expression C (suc n)
  → Raw.Expression C n
lambda m k A B t = Tree.node (Raw.lambda m k) (lambda-children m k A B t)

application-children :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc n) → Raw.Expression C n → Raw.Expression C n
  → Children C n (Raw.application m k)
application-children m k A B f a Raw.application-domain = A
application-children {C} {n} m k A B f a Raw.application-codomain =
  Binding.bound (Raw.binding C) n 1 B
application-children m k A B f a Raw.application-function = f
application-children m k A B f a Raw.application-argument = a

application :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc n) → Raw.Expression C n → Raw.Expression C n
  → Raw.Expression C n
application m k A B f a =
  Tree.node (Raw.application m k) (application-children m k A B f a)

------------------------------------------------------------------------
-- Σ

sigma-children :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc n) → Children C n (Raw.sigma m k)
sigma-children m k A B Raw.sigma-first = A
sigma-children {C} {n} m k A B Raw.sigma-second =
  Binding.bound (Raw.binding C) n 1 B

sigma :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc n) → Raw.Expression C n
sigma m k A B = Tree.node (Raw.sigma m k) (sigma-children m k A B)

pair-children :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc n) → Raw.Expression C n → Raw.Expression C n
  → Children C n (Raw.pair m k)
pair-children m k A B a b Raw.pair-first-type = A
pair-children {C} {n} m k A B a b Raw.pair-second-type =
  Binding.bound (Raw.binding C) n 1 B
pair-children m k A B a b Raw.pair-first = a
pair-children m k A B a b Raw.pair-second = b

pair :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc n) → Raw.Expression C n → Raw.Expression C n
  → Raw.Expression C n
pair m k A B a b = Tree.node (Raw.pair m k) (pair-children m k A B a b)

first-children :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc n) → Raw.Expression C n
  → Children C n (Raw.first m k)
first-children m k A B p Raw.first-first-type = A
first-children {C} {n} m k A B p Raw.first-second-type =
  Binding.bound (Raw.binding C) n 1 B
first-children m k A B p Raw.first-pair = p

first :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc n) → Raw.Expression C n → Raw.Expression C n
first m k A B p = Tree.node (Raw.first m k) (first-children m k A B p)

second-children :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc n) → Raw.Expression C n
  → Children C n (Raw.second m k)
second-children m k A B p Raw.second-first-type = A
second-children {C} {n} m k A B p Raw.second-second-type =
  Binding.bound (Raw.binding C) n 1 B
second-children m k A B p Raw.second-pair = p

second :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc n) → Raw.Expression C n → Raw.Expression C n
second m k A B p = Tree.node (Raw.second m k) (second-children m k A B p)

------------------------------------------------------------------------
-- Identity types

identity-children :
  {C : Set} {n : ℕ} (m : ℕ) → Raw.Expression C n → Raw.Expression C n
  → Raw.Expression C n → Children C n (Raw.identity m)
identity-children m A a b Raw.identity-type = A
identity-children m A a b Raw.identity-left = a
identity-children m A a b Raw.identity-right = b

identity :
  {C : Set} {n : ℕ} (m : ℕ) → Raw.Expression C n → Raw.Expression C n
  → Raw.Expression C n → Raw.Expression C n
identity m A a b = Tree.node (Raw.identity m) (identity-children m A a b)

reflexivity-children :
  {C : Set} {n : ℕ} (m : ℕ) → Raw.Expression C n → Raw.Expression C n
  → Children C n (Raw.reflexivity m)
reflexivity-children m A a Raw.reflexivity-type = A
reflexivity-children m A a Raw.reflexivity-point = a

reflexivity :
  {C : Set} {n : ℕ} (m : ℕ) → Raw.Expression C n → Raw.Expression C n
  → Raw.Expression C n
reflexivity m A a = Tree.node (Raw.reflexivity m) (reflexivity-children m A a)

path-induction-children :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc (suc n)) → Raw.Expression C n
  → Raw.Expression C n → Raw.Expression C n → Raw.Expression C n
  → Children C n (Raw.path-induction m k)
path-induction-children m k A M a d b p Raw.induction-type = A
path-induction-children {C} {n} m k A M a d b p Raw.induction-motive =
  Binding.bound (Raw.binding C) n 2 M
path-induction-children m k A M a d b p Raw.induction-base = a
path-induction-children m k A M a d b p Raw.induction-method = d
path-induction-children m k A M a d b p Raw.induction-end = b
path-induction-children m k A M a d b p Raw.induction-path = p

path-induction :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc (suc n)) → Raw.Expression C n
  → Raw.Expression C n → Raw.Expression C n → Raw.Expression C n
  → Raw.Expression C n
path-induction m k A M a d b p =
  Tree.node (Raw.path-induction m k)
    (path-induction-children m k A M a d b p)

------------------------------------------------------------------------
-- W

tree-children :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc n) → Children C n (Raw.tree m k)
tree-children m k A B Raw.tree-shape = A
tree-children {C} {n} m k A B Raw.tree-position =
  Binding.bound (Raw.binding C) n 1 B

tree :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc n) → Raw.Expression C n
tree m k A B = Tree.node (Raw.tree m k) (tree-children m k A B)

supremum-children :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc n) → Raw.Expression C n → Raw.Expression C n
  → Children C n (Raw.supremum m k)
supremum-children m k A B a f Raw.supremum-shape-type = A
supremum-children {C} {n} m k A B a f Raw.supremum-position-type =
  Binding.bound (Raw.binding C) n 1 B
supremum-children m k A B a f Raw.supremum-shape = a
supremum-children m k A B a f Raw.supremum-children = f

supremum :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc n) → Raw.Expression C n → Raw.Expression C n
  → Raw.Expression C n
supremum m k A B a f =
  Tree.node (Raw.supremum m k) (supremum-children m k A B a f)

tree-induction-children :
  {C : Set} {n : ℕ} (m k l : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc n) → Raw.Expression C (suc n)
  → Raw.Expression C (suc (suc (suc n))) → Raw.Expression C n
  → Children C n (Raw.tree-induction m k l)
tree-induction-children m k l A B M c w Raw.recursion-shape-type = A
tree-induction-children {C} {n} m k l A B M c w
  Raw.recursion-position-type = Binding.bound (Raw.binding C) n 1 B
tree-induction-children {C} {n} m k l A B M c w Raw.recursion-motive =
  Binding.bound (Raw.binding C) n 1 M
tree-induction-children {C} {n} m k l A B M c w Raw.recursion-method =
  Binding.bound (Raw.binding C) n 3 c
tree-induction-children m k l A B M c w Raw.recursion-tree = w

tree-induction :
  {C : Set} {n : ℕ} (m k l : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc n) → Raw.Expression C (suc n)
  → Raw.Expression C (suc (suc (suc n))) → Raw.Expression C n
  → Raw.Expression C n
tree-induction m k l A B M c w =
  Tree.node (Raw.tree-induction m k l)
    (tree-induction-children m k l A B M c w)

------------------------------------------------------------------------
-- 0 and 1

empty-children : {C : Set} {n : ℕ} → Children C n Raw.empty
empty-children ()

empty : {C : Set} {n : ℕ} → Raw.Expression C n
empty = Tree.node Raw.empty empty-children

absurd-children :
  {C : Set} {n : ℕ} (k : ℕ) → Raw.Expression C (suc n)
  → Raw.Expression C n → Children C n (Raw.absurd k)
absurd-children {C} {n} k M t Raw.absurd-motive =
  Binding.bound (Raw.binding C) n 1 M
absurd-children k M t Raw.absurd-term = t

absurd :
  {C : Set} {n : ℕ} (k : ℕ) → Raw.Expression C (suc n)
  → Raw.Expression C n → Raw.Expression C n
absurd k M t = Tree.node (Raw.absurd k) (absurd-children k M t)

unit-children : {C : Set} {n : ℕ} → Children C n Raw.unit
unit-children ()

unit : {C : Set} {n : ℕ} → Raw.Expression C n
unit = Tree.node Raw.unit unit-children

star-children : {C : Set} {n : ℕ} → Children C n Raw.star
star-children ()

star : {C : Set} {n : ℕ} → Raw.Expression C n
star = Tree.node Raw.star star-children

------------------------------------------------------------------------
-- Sums

sum-children :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n → Raw.Expression C n
  → Children C n (Raw.sum m k)
sum-children m k A B Raw.sum-left = A
sum-children m k A B Raw.sum-right = B

sum :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n → Raw.Expression C n
  → Raw.Expression C n
sum m k A B = Tree.node (Raw.sum m k) (sum-children m k A B)

left-children :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n → Raw.Expression C n
  → Raw.Expression C n → Children C n (Raw.left m k)
left-children m k A B a Raw.left-left-type = A
left-children m k A B a Raw.left-right-type = B
left-children m k A B a Raw.left-term = a

left :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n → Raw.Expression C n
  → Raw.Expression C n → Raw.Expression C n
left m k A B a = Tree.node (Raw.left m k) (left-children m k A B a)

right-children :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n → Raw.Expression C n
  → Raw.Expression C n → Children C n (Raw.right m k)
right-children m k A B b Raw.right-left-type = A
right-children m k A B b Raw.right-right-type = B
right-children m k A B b Raw.right-term = b

right :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n → Raw.Expression C n
  → Raw.Expression C n → Raw.Expression C n
right m k A B b = Tree.node (Raw.right m k) (right-children m k A B b)

case-children :
  {C : Set} {n : ℕ} (m k l : ℕ) → Raw.Expression C n → Raw.Expression C n
  → Raw.Expression C (suc n) → Raw.Expression C (suc n)
  → Raw.Expression C (suc n) → Raw.Expression C n
  → Children C n (Raw.case m k l)
case-children m k l A B M c d s Raw.case-left-type = A
case-children m k l A B M c d s Raw.case-right-type = B
case-children {C} {n} m k l A B M c d s Raw.case-motive =
  Binding.bound (Raw.binding C) n 1 M
case-children {C} {n} m k l A B M c d s Raw.case-left-method =
  Binding.bound (Raw.binding C) n 1 c
case-children {C} {n} m k l A B M c d s Raw.case-right-method =
  Binding.bound (Raw.binding C) n 1 d
case-children m k l A B M c d s Raw.case-term = s

case :
  {C : Set} {n : ℕ} (m k l : ℕ) → Raw.Expression C n → Raw.Expression C n
  → Raw.Expression C (suc n) → Raw.Expression C (suc n)
  → Raw.Expression C (suc n) → Raw.Expression C n → Raw.Expression C n
case m k l A B M c d s =
  Tree.node (Raw.case m k l) (case-children m k l A B M c d s)

------------------------------------------------------------------------
-- ℕ

natural-children : {C : Set} {n : ℕ} → Children C n Raw.natural
natural-children ()

natural : {C : Set} {n : ℕ} → Raw.Expression C n
natural = Tree.node Raw.natural natural-children

zero-children : {C : Set} {n : ℕ} → Children C n Raw.zero
zero-children ()

zero : {C : Set} {n : ℕ} → Raw.Expression C n
zero = Tree.node Raw.zero zero-children

successor-children :
  {C : Set} {n : ℕ} → Raw.Expression C n → Children C n Raw.successor
successor-children t Raw.successor-term = t

successor : {C : Set} {n : ℕ} → Raw.Expression C n → Raw.Expression C n
successor t = Tree.node Raw.successor (successor-children t)

natural-induction-children :
  {C : Set} {n : ℕ} (l : ℕ) → Raw.Expression C (suc n)
  → Raw.Expression C n → Raw.Expression C (suc (suc n))
  → Raw.Expression C n → Children C n (Raw.natural-induction l)
natural-induction-children {C} {n} l M z s t Raw.natural-motive =
  Binding.bound (Raw.binding C) n 1 M
natural-induction-children l M z s t Raw.natural-base = z
natural-induction-children {C} {n} l M z s t Raw.natural-step =
  Binding.bound (Raw.binding C) n 2 s
natural-induction-children l M z s t Raw.natural-term = t

natural-induction :
  {C : Set} {n : ℕ} (l : ℕ) → Raw.Expression C (suc n)
  → Raw.Expression C n → Raw.Expression C (suc (suc n))
  → Raw.Expression C n → Raw.Expression C n
natural-induction l M z s t =
  Tree.node (Raw.natural-induction l) (natural-induction-children l M z s t)

------------------------------------------------------------------------
-- Kubánek's subuniverses

subuniverse-children :
  {C : Set} {n : ℕ} (i : ℕ) (U0 E0 U+ E+ : Raw.Expression C n)
  → Children C n (Raw.subuniverse i)
subuniverse-children i U0 E0 U+ E+ Raw.subuniverse-base = U0
subuniverse-children i U0 E0 U+ E+ Raw.subuniverse-base-decoding = E0
subuniverse-children i U0 E0 U+ E+ Raw.subuniverse-step = U+
subuniverse-children i U0 E0 U+ E+ Raw.subuniverse-step-decoding = E+

subuniverse :
  {C : Set} {n : ℕ} (i : ℕ) (U0 E0 U+ E+ : Raw.Expression C n)
  → Raw.Expression C n
subuniverse i U0 E0 U+ E+ =
  Tree.node (Raw.subuniverse i)
    (subuniverse-children i U0 E0 U+ E+)

inclusion-children :
  {C : Set} {n : ℕ} (i : ℕ) (U0 E0 U+ E+ u : Raw.Expression C n)
  → Children C n (Raw.inclusion i)
inclusion-children i U0 E0 U+ E+ u Raw.inclusion-base = U0
inclusion-children i U0 E0 U+ E+ u Raw.inclusion-base-decoding = E0
inclusion-children i U0 E0 U+ E+ u Raw.inclusion-step = U+
inclusion-children i U0 E0 U+ E+ u Raw.inclusion-step-decoding = E+
inclusion-children i U0 E0 U+ E+ u Raw.inclusion-point = u

inclusion :
  {C : Set} {n : ℕ} (i : ℕ) (U0 E0 U+ E+ u : Raw.Expression C n)
  → Raw.Expression C n
inclusion i U0 E0 U+ E+ u =
  Tree.node (Raw.inclusion i)
    (inclusion-children i U0 E0 U+ E+ u)

closure-children :
  {C : Set} {n : ℕ} (i : ℕ) (U0 E0 U+ E+ A B c : Raw.Expression C n)
  → Children C n (Raw.closure i)
closure-children i U0 E0 U+ E+ A B c Raw.closure-base = U0
closure-children i U0 E0 U+ E+ A B c Raw.closure-base-decoding = E0
closure-children i U0 E0 U+ E+ A B c Raw.closure-step = U+
closure-children i U0 E0 U+ E+ A B c Raw.closure-step-decoding = E+
closure-children i U0 E0 U+ E+ A B c Raw.closure-code = A
closure-children i U0 E0 U+ E+ A B c Raw.closure-family = B
closure-children i U0 E0 U+ E+ A B c Raw.closure-point = c

closure :
  {C : Set} {n : ℕ} (i : ℕ) (U0 E0 U+ E+ A B c : Raw.Expression C n)
  → Raw.Expression C n
closure i U0 E0 U+ E+ A B c =
  Tree.node (Raw.closure i)
    (closure-children i U0 E0 U+ E+ A B c)

decoding-children :
  {C : Set} {n : ℕ} (i : ℕ) (U0 E0 U+ E+ a : Raw.Expression C n)
  → Children C n (Raw.decoding i)
decoding-children i U0 E0 U+ E+ a Raw.decoding-base = U0
decoding-children i U0 E0 U+ E+ a Raw.decoding-base-decoding = E0
decoding-children i U0 E0 U+ E+ a Raw.decoding-step = U+
decoding-children i U0 E0 U+ E+ a Raw.decoding-step-decoding = E+
decoding-children i U0 E0 U+ E+ a Raw.decoding-code = a

decoding :
  {C : Set} {n : ℕ} (i : ℕ) (U0 E0 U+ E+ a : Raw.Expression C n)
  → Raw.Expression C n
decoding i U0 E0 U+ E+ a =
  Tree.node (Raw.decoding i)
    (decoding-children i U0 E0 U+ E+ a)

subuniverse-induction-children :
  {C : Set} {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M b s a : Raw.Expression C n)
  → Children C n (Raw.subuniverse-induction i j)
subuniverse-induction-children i j U0 E0 U+ E+ M b s a
  Raw.subinduction-base = U0
subuniverse-induction-children i j U0 E0 U+ E+ M b s a
  Raw.subinduction-base-decoding = E0
subuniverse-induction-children i j U0 E0 U+ E+ M b s a
  Raw.subinduction-step = U+
subuniverse-induction-children i j U0 E0 U+ E+ M b s a
  Raw.subinduction-step-decoding = E+
subuniverse-induction-children i j U0 E0 U+ E+ M b s a
  Raw.subinduction-motive = M
subuniverse-induction-children i j U0 E0 U+ E+ M b s a
  Raw.subinduction-inclusion = b
subuniverse-induction-children i j U0 E0 U+ E+ M b s a
  Raw.subinduction-closure = s
subuniverse-induction-children i j U0 E0 U+ E+ M b s a Raw.subinduction-code = a

subuniverse-induction :
  {C : Set} {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M b s a : Raw.Expression C n)
  → Raw.Expression C n
subuniverse-induction i j U0 E0 U+ E+ M b s a =
  Tree.node (Raw.subuniverse-induction i j)
    (subuniverse-induction-children i j U0 E0 U+ E+ M b s a)

------------------------------------------------------------------------
-- Constants

constant-children : {C : Set} {n : ℕ} (c : C) → Children C n (Raw.constant c)
constant-children c ()

constant : {C : Set} {n : ℕ} → C → Raw.Expression C n
constant c = Tree.node (Raw.constant c) (constant-children c)

------------------------------------------------------------------------
-- Weakening

-- Weakening by one variable, the new last one.
weaken :
  {C : Set} {n : ℕ} → Raw.Expression C n → Raw.Expression C (suc n)
weaken {C} e = Binding.rename (Raw.binding C) fsuc e

-- Weakening by d variables under c bound ones.
weaken-past :
  {C : Set} (n c d : ℕ) → Raw.Expression C (c + n)
  → Raw.Expression C (c + (d + n))
weaken-past {C} n c d e =
  Binding.rename (Raw.binding C)
    (Binding.lift (Raw.binding C) c (λ (y : Fin n) → d ↑ʳ y)) e

-- A closed expression in scope n.
closed : {C : Set} (n : ℕ) → Raw.Expression C 0 → Raw.Expression C n
closed {C} n e = Binding.rename (Raw.binding C) (λ (i : Fin 0) → i ↑ˡ n) e

------------------------------------------------------------------------
-- Substitution

-- σ extended by e for a new last variable.
extended :
  {C : Set} {k n : ℕ} → (Fin k → Raw.Expression C n) → Raw.Expression C n
  → Fin (suc k) → Raw.Expression C n
extended σ e fzero = e
extended σ e (fsuc i) = σ i

-- The variables of scope n, inside scope d + n.
shifted : {C : Set} (n d : ℕ) → Fin n → Raw.Expression C (d + n)
shifted n d i = Tree.hole (d ↑ʳ i)

-- The last variable of M replaced by e.
instantiate :
  {C : Set} {n : ℕ} → Raw.Expression C (suc n) → Raw.Expression C n
  → Raw.Expression C n
instantiate {C} {n} M e =
  Binding.substitute (Raw.binding C) n
    (extended (λ (i : Fin n) → Tree.hole i) e) M

-- The last variable of M replaced by e, d variables deeper (the rules use
-- d ≥ 1; d = 0 is `instantiate`).
instantiate-past :
  {C : Set} {n : ℕ} (d : ℕ) → Raw.Expression C (suc n)
  → Raw.Expression C (d + n) → Raw.Expression C (d + n)
instantiate-past {C} {n} d M e =
  Binding.substitute (Raw.binding C) (d + n) (extended (shifted n d) e) M

-- The last two variables of M replaced by a and b, b the last.
instantiate₂ :
  {C : Set} {n : ℕ} → Raw.Expression C (suc (suc n))
  → Raw.Expression C n → Raw.Expression C n → Raw.Expression C n
instantiate₂ {C} {n} M a b =
  Binding.substitute (Raw.binding C) n
    (extended (extended (λ (i : Fin n) → Tree.hole i) a) b) M

-- The last three variables of M replaced by a, b and c, c the last.
instantiate₃ :
  {C : Set} {n : ℕ} → Raw.Expression C (suc (suc (suc n)))
  → Raw.Expression C n → Raw.Expression C n → Raw.Expression C n
  → Raw.Expression C n
instantiate₃ {C} {n} M a b c =
  Binding.substitute (Raw.binding C) n
    (extended (extended (extended (λ (i : Fin n) → Tree.hole i) a) b) c) M
