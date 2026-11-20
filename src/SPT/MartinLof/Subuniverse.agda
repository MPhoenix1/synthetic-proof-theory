{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Subuniverse where

-- The types of Kubánek's subuniverse formers (Canonicity of the Mahlo
-- Universe, MSc thesis, Chalmers 2025, §3.3) as raw expressions, for the
-- rules of Rules/Subuniverse. At level i the parameters are a base U0 : U i
-- with a decoding E0 : U0 → U i (`family`), and an operator U+ :
-- Π (A : U i). (A → U i) → U i (`operator`, `operation`) with a decoding
-- E+ : Π (A : U i) (B : A → U i). U+ A B → U i (`operator-decoding`,
-- `plus-operation`, `plus-family`; `operated` is U+ applied to A and B).
-- Over them: El A → Ma (`family-of`), U+ (El A) B → U i (`decoded-plus`),
-- λ x. El (B x) (`decoded`), the type of the closure's point
-- (`point-type`), the motive's type Ma → U j and its application
-- (`motive-type`, `motive-at`), and the methods' types (`inclusion-method`;
-- `closure-method` through `closure-first`, `closure-second`,
-- `closure-third`, `closure-fourth` and `induction-hypotheses`, one Π
-- each). The right sides of the four computation equations are
-- `decoding-closure`, `induction-inclusion` and `induction-closure`, and
-- E0 u for decoding at an inclusion.
--
-- Each type is a function of the expressions it depends on, with the
-- variables a Π binds as holes, so the instance of one at a term is that
-- function applied to it, and its weakening the function at the weakened
-- arguments. A compound is never weakened whole: its parts are, as in
-- `applied` and `decoded-plus`, so a weakened expression is stable when
-- its parts are. Levels are written by value, as the formation rules give
-- them (`family-level` and the others).

open import SPT.Base
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Tree as Tree
open import SPT.MartinLof.Formers using
  (universe; pi; lambda; application; weaken; subuniverse; inclusion; closure
  ; decoding; subuniverse-induction)
import SPT.MartinLof.Raw as Raw

------------------------------------------------------------------------
-- Levels

-- a → U i; (a → U i) → U i; the operator; Π (B : A → U i). U+ A B → U i;
-- the operator's decoding.
family-level operation-level operator-level : ℕ → ℕ
family-level i = i ⊔ℕ suc i
operation-level i = family-level i ⊔ℕ suc i
operator-level i = suc i ⊔ℕ operation-level i

plus-level plus-decoding-level : ℕ → ℕ
plus-level i = family-level i ⊔ℕ family-level i
plus-decoding-level i = suc i ⊔ℕ plus-level i

-- Ma → U j; the inclusion method; the closure method, Π by Π from inside.
motive-level inclusion-method-level : ℕ → ℕ → ℕ
motive-level i j = i ⊔ℕ suc j
inclusion-method-level i j = i ⊔ℕ j

fourth-level third-level second-level first-level : ℕ → ℕ → ℕ
fourth-level i j = i ⊔ℕ j
third-level i j = fourth-level i j ⊔ℕ fourth-level i j
second-level i j = (i ⊔ℕ i) ⊔ℕ third-level i j
first-level i j = j ⊔ℕ second-level i j

closure-method-level : ℕ → ℕ → ℕ
closure-method-level i j = i ⊔ℕ first-level i j

------------------------------------------------------------------------
-- The parameters

-- a → U i.
family :
  {C : Set} {n : ℕ} (i : ℕ) → Raw.Expression C n → Raw.Expression C n
family i a = pi i (suc i) a (universe i)

-- (A → U i) → U i, for A the last variable.
operation : {C : Set} {n : ℕ} (i : ℕ) → Raw.Expression C (suc n)
operation i =
  pi (family-level i) (suc i) (family i (Tree.hole fzero)) (universe i)

-- Π (A : U i). (A → U i) → U i.
operator : {C : Set} {n : ℕ} (i : ℕ) → Raw.Expression C n
operator i = pi (suc i) (operation-level i) (universe i) (operation i)

-- f a b, for f an operator.
operated :
  {C : Set} {n : ℕ} (i : ℕ) (f a b : Raw.Expression C n)
  → Raw.Expression C n
operated i f a b =
  application (family-level i) (suc i) (family i a) (universe i)
    (application (suc i) (operation-level i) (universe i) (operation i) f a)
    b

-- f A B → U i, for A and B the last two variables.
plus-family :
  {C : Set} {n : ℕ} (i : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc (suc n))
plus-family i f =
  pi i (suc i)
    (operated i (weaken (weaken f)) (Tree.hole (fsuc fzero))
      (Tree.hole fzero))
    (universe i)

-- Π (B : A → U i). f A B → U i, for A the last variable.
plus-operation :
  {C : Set} {n : ℕ} (i : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc n)
plus-operation i f =
  pi (family-level i) (family-level i) (family i (Tree.hole fzero))
    (plus-family i f)

-- Π (A : U i) (B : A → U i). f A B → U i.
operator-decoding :
  {C : Set} {n : ℕ} (i : ℕ) → Raw.Expression C n → Raw.Expression C n
operator-decoding i f =
  pi (suc i) (plus-level i) (universe i) (plus-operation i f)

------------------------------------------------------------------------
-- Over the subuniverse

-- El A → Ma.
family-of :
  {C : Set} {n : ℕ} (i : ℕ) (U0 E0 U+ E+ A : Raw.Expression C n)
  → Raw.Expression C n
family-of i U0 E0 U+ E+ A =
  pi i i (decoding i U0 E0 U+ E+ A)
    (subuniverse i (weaken U0) (weaken E0) (weaken U+) (weaken E+))

-- B x, for x the last variable and B a family over El A.
applied :
  {C : Set} {n : ℕ} (i : ℕ) (U0 E0 U+ E+ A B : Raw.Expression C n)
  → Raw.Expression C (suc n)
applied i U0 E0 U+ E+ A B =
  application i i
    (decoding i (weaken U0) (weaken E0) (weaken U+) (weaken E+) (weaken A))
    (subuniverse i (weaken (weaken U0)) (weaken (weaken E0))
      (weaken (weaken U+)) (weaken (weaken E+)))
    (weaken B) (Tree.hole fzero)

-- λ x. El (B x).
decoded :
  {C : Set} {n : ℕ} (i : ℕ) (U0 E0 U+ E+ A B : Raw.Expression C n)
  → Raw.Expression C n
decoded i U0 E0 U+ E+ A B =
  lambda i (suc i) (decoding i U0 E0 U+ E+ A) (universe i)
    (decoding i (weaken U0) (weaken E0) (weaken U+) (weaken E+)
      (applied i U0 E0 U+ E+ A B))

-- U+ (El A) B → U i, for B the last variable.
decoded-plus :
  {C : Set} {n : ℕ} (i : ℕ) (U0 E0 U+ E+ A : Raw.Expression C n)
  → Raw.Expression C (suc n)
decoded-plus i U0 E0 U+ E+ A =
  pi i (suc i)
    (operated i (weaken U+)
      (decoding i (weaken U0) (weaken E0) (weaken U+) (weaken E+) (weaken A))
      (Tree.hole fzero))
    (universe i)

-- U+ (El A) (λ x. El (B x)), the type of the closure's point.
point-type :
  {C : Set} {n : ℕ} (i : ℕ) (U0 E0 U+ E+ A B : Raw.Expression C n)
  → Raw.Expression C n
point-type i U0 E0 U+ E+ A B =
  operated i U+ (decoding i U0 E0 U+ E+ A) (decoded i U0 E0 U+ E+ A B)

-- E+ (El A) (λ x. El (B x)) c, the decoding at a closure.
decoding-closure :
  {C : Set} {n : ℕ} (i : ℕ) (U0 E0 U+ E+ A B c : Raw.Expression C n)
  → Raw.Expression C n
decoding-closure i U0 E0 U+ E+ A B c =
  application i (suc i) (point-type i U0 E0 U+ E+ A B) (universe i)
    (application (family-level i) (family-level i)
      (family i (decoding i U0 E0 U+ E+ A))
      (decoded-plus i U0 E0 U+ E+ A)
      (application (suc i) (plus-level i) (universe i) (plus-operation i U+)
        E+ (decoding i U0 E0 U+ E+ A))
      (decoded i U0 E0 U+ E+ A B))
    c

------------------------------------------------------------------------
-- Induction

-- Ma → U j, and M a.
motive-type :
  {C : Set} {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ : Raw.Expression C n)
  → Raw.Expression C n
motive-type i j U0 E0 U+ E+ =
  pi i (suc j) (subuniverse i U0 E0 U+ E+) (universe j)

motive-at :
  {C : Set} {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M a : Raw.Expression C n)
  → Raw.Expression C n
motive-at i j U0 E0 U+ E+ M a =
  application i (suc j) (subuniverse i U0 E0 U+ E+) (universe j) M a

-- Π (u : U0). M (El0' u).
inclusion-method :
  {C : Set} {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M : Raw.Expression C n)
  → Raw.Expression C n
inclusion-method i j U0 E0 U+ E+ M =
  pi i j U0
    (motive-at i j (weaken U0) (weaken E0) (weaken U+) (weaken E+)
      (weaken M)
      (inclusion i (weaken U0) (weaken E0) (weaken U+) (weaken E+)
        (Tree.hole fzero)))

-- Π (c : U+ (El A) (λ x. El (B x))). M (El+' A B c).
closure-fourth :
  {C : Set} {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M A B : Raw.Expression C n)
  → Raw.Expression C n
closure-fourth i j U0 E0 U+ E+ M A B =
  pi i j (point-type i U0 E0 U+ E+ A B)
    (motive-at i j (weaken U0) (weaken E0) (weaken U+) (weaken E+)
      (weaken M)
      (closure i (weaken U0) (weaken E0) (weaken U+) (weaken E+) (weaken A)
        (weaken B) (Tree.hole fzero)))

-- Π (x : El A). M (B x).
induction-hypotheses :
  {C : Set} {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M A B : Raw.Expression C n)
  → Raw.Expression C n
induction-hypotheses i j U0 E0 U+ E+ M A B =
  pi i j (decoding i U0 E0 U+ E+ A)
    (motive-at i j (weaken U0) (weaken E0) (weaken U+) (weaken E+)
      (weaken M) (applied i U0 E0 U+ E+ A B))

-- Π (k : Π (x : El A). M (B x)). Π (c : …). M (El+' A B c).
closure-third :
  {C : Set} {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M A B : Raw.Expression C n)
  → Raw.Expression C n
closure-third i j U0 E0 U+ E+ M A B =
  pi (fourth-level i j) (fourth-level i j)
    (induction-hypotheses i j U0 E0 U+ E+ M A B)
    (closure-fourth i j (weaken U0) (weaken E0) (weaken U+) (weaken E+)
      (weaken M) (weaken A) (weaken B))

-- Π (B : El A → Ma). Π (k : …). Π (c : …). M (El+' A B c).
closure-second :
  {C : Set} {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M A : Raw.Expression C n)
  → Raw.Expression C n
closure-second i j U0 E0 U+ E+ M A =
  pi (i ⊔ℕ i) (third-level i j) (family-of i U0 E0 U+ E+ A)
    (closure-third i j (weaken U0) (weaken E0) (weaken U+) (weaken E+)
      (weaken M) (weaken A) (Tree.hole fzero))

-- Π (h : M A). Π (B : …). Π (k : …). Π (c : …). M (El+' A B c).
closure-first :
  {C : Set} {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M A : Raw.Expression C n)
  → Raw.Expression C n
closure-first i j U0 E0 U+ E+ M A =
  pi j (second-level i j) (motive-at i j U0 E0 U+ E+ M A)
    (closure-second i j (weaken U0) (weaken E0) (weaken U+) (weaken E+)
      (weaken M) (weaken A))

-- Π (A : Ma). Π (h : M A). Π (B : …). Π (k : …). Π (c : …). M (El+' A B c).
closure-method :
  {C : Set} {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M : Raw.Expression C n)
  → Raw.Expression C n
closure-method i j U0 E0 U+ E+ M =
  pi i (first-level i j) (subuniverse i U0 E0 U+ E+)
    (closure-first i j (weaken U0) (weaken E0) (weaken U+) (weaken E+)
      (weaken M) (Tree.hole fzero))

-- b u, induction at an inclusion.
induction-inclusion :
  {C : Set} {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M b u : Raw.Expression C n)
  → Raw.Expression C n
induction-inclusion i j U0 E0 U+ E+ M b u =
  application i j U0
    (motive-at i j (weaken U0) (weaken E0) (weaken U+) (weaken E+)
      (weaken M)
      (inclusion i (weaken U0) (weaken E0) (weaken U+) (weaken E+)
        (Tree.hole fzero)))
    b u

-- s A (ind A) B (λ x. ind (B x)) c, induction at a closure.
induction-closure :
  {C : Set} {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M b s A B c : Raw.Expression C n)
  → Raw.Expression C n
induction-closure i j U0 E0 U+ E+ M b s A B c =
  application i j (point-type i U0 E0 U+ E+ A B)
    (motive-at i j (weaken U0) (weaken E0) (weaken U+) (weaken E+)
      (weaken M)
      (closure i (weaken U0) (weaken E0) (weaken U+) (weaken E+) (weaken A)
        (weaken B) (Tree.hole fzero)))
    (application (fourth-level i j) (fourth-level i j)
      (induction-hypotheses i j U0 E0 U+ E+ M A B)
      (closure-fourth i j (weaken U0) (weaken E0) (weaken U+) (weaken E+)
        (weaken M) (weaken A) (weaken B))
      (application (i ⊔ℕ i) (third-level i j) (family-of i U0 E0 U+ E+ A)
        (closure-third i j (weaken U0) (weaken E0) (weaken U+) (weaken E+)
          (weaken M) (weaken A) (Tree.hole fzero))
        (application j (second-level i j) (motive-at i j U0 E0 U+ E+ M A)
          (closure-second i j (weaken U0) (weaken E0) (weaken U+)
            (weaken E+) (weaken M) (weaken A))
          (application i (first-level i j) (subuniverse i U0 E0 U+ E+)
            (closure-first i j (weaken U0) (weaken E0) (weaken U+)
              (weaken E+) (weaken M) (Tree.hole fzero))
            s A)
          (subuniverse-induction i j U0 E0 U+ E+ M b s A))
        B)
      (lambda i j (decoding i U0 E0 U+ E+ A)
        (motive-at i j (weaken U0) (weaken E0) (weaken U+) (weaken E+)
          (weaken M) (applied i U0 E0 U+ E+ A B))
        (subuniverse-induction i j (weaken U0) (weaken E0) (weaken U+)
          (weaken E+) (weaken M) (weaken b) (weaken s)
          (applied i U0 E0 U+ E+ A B))))
    c
