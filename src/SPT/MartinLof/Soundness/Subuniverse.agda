{-# OPTIONS --safe --without-K --no-projection-like #-}

module SPT.MartinLof.Soundness.Subuniverse where

-- Soundness of the rules of Kubánek's subuniverses (`sound`). The value of
-- each former is the model's operation at the values of its children. A Π,
-- λ or application has the model's at given values of its children
-- (`pi-rewrite`, `lambda-rewrite`, `application-rewrite`, from Pi's
-- `pi-value` and the others). So the types of the rules (Subuniverse) read
-- at an environment are the model's types (Model.Subuniverse) at the
-- values of what they depend on, a weakened expression read as its value
-- along p (`family-value` through `induction-closure-value`). A sealed
-- type is reached through its unfolding equation, its codomain at the
-- weakened arguments by the lemma of the next one (`fourth-weakened`,
-- `third-weakened`, `second-weakened`, `first-weakened`). These need only
-- the parameters' stability (`Stable-Parameters`, `weakened`).
--
-- The premises' typings (`Typed-Parameters`, `Typed-Arguments`,
-- `Typed-Methods`, at instances `parameters-[]` and the others) give the
-- model's `Parameters`, `Arguments` and `Methods` (`parameters-at`,
-- `arguments-at`, `methods-at`). Each former is stable by its stability
-- law and has its type by its typing law (`subuniverse-typed` through
-- `induction-typed`; M a is a type by Pi's application,
-- `motive-at-typed`). Each equation of the rules holds at every instance
-- of the environment: the decoding laws and β (`inclusion-decoding-value`
-- and the others), and the children's equations for the congruences
-- (Typing's `equal-[]`). So its right side has the typing of its left
-- (`equal-typed`).

open import SPT.Base hiding (Lift; _∘_; id; lift; lower; zero)
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Tree as Tree
import SPT.MartinLof.Formers as Formers
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Judgment using (Judgment)
import SPT.MartinLof.Rules.Subuniverse as Block
import SPT.MartinLof.Subuniverse as Types
open import SPT.MartinLof.Subuniverse using
  (family-level; operation-level; operator-level; plus-level
  ; plus-decoding-level; motive-level; inclusion-method-level
  ; closure-method-level; fourth-level; third-level; second-level; first-level)
open import SPT.MartinLof.Model.Empty using (Empty)
open import SPT.MartinLof.Model.Identity using (Identity)
open import SPT.MartinLof.Model.Lift using (Lift)
open import SPT.MartinLof.Model.Natural using (Natural)
import SPT.MartinLof.Model.Subuniverse as Model
open import SPT.MartinLof.Model.Subuniverse using
  (Operations; Subuniverse; Parameters; Arguments; Methods)
open import SPT.MartinLof.Model.Pi using (Pi)
open import SPT.MartinLof.Model.Russell using (Russell; closed-code)
open import SPT.MartinLof.Model.Sigma using (Sigma)
open import SPT.MartinLof.Model.Sum using (Sum)
open import SPT.MartinLof.Model.Unit using (Unit)
open import SPT.MartinLof.Model.WellFounded using (WellFounded)
import SPT.MartinLof.Soundness.Environment as Environment
import SPT.MartinLof.Soundness.Instances as Instances
import SPT.MartinLof.Soundness.Interpretation as Interpretation
import SPT.MartinLof.Soundness.Pi as Products
open import SPT.MartinLof.Soundness.Transport using
  (ap₄; ap₅; ap₆; ap₇; ap₈)
import SPT.MartinLof.Soundness.Typing as Typing

module _ {ℓ : Level} {C : Set}
  (R : Russell ℓ) (let open Russell R)
  (lifting : Lift R) (let open Lift lifting)
  (products : Pi R) (let open Pi products)
  (pairs : Sigma R) (let open Sigma pairs)
  (paths : Identity R) (let open Identity paths)
  (trees : WellFounded R products) (let open WellFounded trees)
  (nothing : Empty R) (let open Empty nothing)
  (one : Unit R) (let open Unit one)
  (sums : Sum R) (let open Sum sums)
  (numbers : Natural R) (let open Natural numbers)
  (operations : Operations R) (let open Operations operations)
  (subuniverses : Subuniverse R products operations)
  (let open Subuniverse subuniverses)
  (constant : C → Tm ◇)
  (let ext = Environment.ext R)
  (let _[_]ᵉ = Environment._[_]ᵉ R)
  (let Stable = Environment.Stable R)
  (let meaning = Interpretation.⟦_⟧ R lifting products pairs paths trees
                   nothing one sums numbers operations subuniverses constant)
  (let object = Interpretation.object R lifting products pairs paths trees
                  nothing one sums numbers operations subuniverses constant)
  (let values = Interpretation.values R lifting products pairs paths trees
                  nothing one sums numbers operations subuniverses constant)
  (let Typed = Interpretation.Typed R lifting products pairs paths trees
                 nothing one sums numbers operations subuniverses constant)
  (let Valid = Interpretation.Valid R lifting products pairs paths trees
                 nothing one sums numbers operations subuniverses constant)
  (let weaken-at = Instances.weaken-at R lifting products pairs paths trees
                     nothing one sums numbers operations subuniverses constant)
  (let weaken-stable = Instances.weaken-stable R lifting products pairs
                         paths trees nothing one sums numbers
                         operations subuniverses constant)
  (let instantiate-value = Instances.instantiate-value R lifting products
                             pairs paths trees nothing one sums numbers
                             operations subuniverses constant)
  (let pi-value = Products.pi-value R lifting products pairs paths trees
                    nothing one sums numbers operations subuniverses constant)
  (let lambda-value = Products.lambda-value R lifting products pairs paths
                        trees nothing one sums numbers operations subuniverses
                          constant)
  (let application-value = Products.application-value R lifting products
                             pairs paths trees nothing one sums numbers
                             operations subuniverses constant)
  (let application-typed = Products.application-typed R lifting products
                             pairs paths trees nothing one sums numbers
                             operations subuniverses constant)
  (let closed-stable = Typing.closed-stable R lifting products pairs paths
                         trees nothing one sums numbers operations subuniverses
                         constant)
  (let as-type = Typing.as-type R lifting products pairs paths trees nothing
                   one sums numbers operations subuniverses constant)
  (let typed-[] = Typing.typed-[] R lifting products pairs paths trees
                    nothing one sums numbers operations subuniverses constant)
  (let equal-[] = Typing.equal-[] R lifting products pairs paths trees
                    nothing one sums numbers operations subuniverses constant)
  (let type-stable = Interpretation.Typed.type-stable)
  (let type-code = Interpretation.Typed.type-code)
  (let term-stable = Interpretation.Typed.term-stable)
  (let term-type = Interpretation.Typed.term-type)
  where

  ----------------------------------------------------------------------
  -- Π, λ and application at given values of their children

  -- The domain's value a is explicit: the codomain is compared at the
  -- extension by a, and at an unsolved a that comparison unfolds the
  -- codomain's whole value.
  pi-rewrite :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (X : Ob) (env : Vec (Tm X) n) (a : Tm X)
    {b : Tm (X ▸ a)}
    → meaning A X env ＝ a → meaning B (X ▸ a) (ext a env) ＝ b
    → meaning (Formers.pi m k A B) X env ＝ pi m k a b
  pi-rewrite m k A B X env a refl refl = pi-value m k A B X env

  lambda-rewrite :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B t : Raw.Expression C (suc n)) (X : Ob) (env : Vec (Tm X) n)
    (a : Tm X) {b u : Tm (X ▸ a)}
    → meaning A X env ＝ a → meaning B (X ▸ a) (ext a env) ＝ b
    → meaning t (X ▸ a) (ext a env) ＝ u
    → meaning (Formers.lambda m k A B t) X env ＝ lambda m k a b u
  lambda-rewrite m k A B t X env a refl refl refl =
    lambda-value m k A B t X env

  application-rewrite :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (f x : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) (a : Tm X) {b : Tm (X ▸ a)} {g y : Tm X}
    → meaning A X env ＝ a → meaning B (X ▸ a) (ext a env) ＝ b
    → meaning f X env ＝ g → meaning x X env ＝ y
    → meaning (Formers.application m k A B f x) X env
      ＝ application m k a b g y
  application-rewrite m k A B f x X env a refl refl refl refl =
    application-value m k A B f x X env

  -- An expression weakened twice, at two extensions.
  weakened² :
    {n : ℕ} (e : Raw.Expression C n) (X : Ob) (a : Tm X) (b : Tm (X ▸ a))
    (env : Vec (Tm X) n) → Stable (meaning e) X env
    → meaning (Formers.weaken (Formers.weaken e)) (X ▸ a ▸ b)
        (ext b (ext a env))
      ＝ meaning e X env [ p ] [ p ]
  weakened² e X a b env s =
    weaken-at (Formers.weaken e) (X ▸ a) b (ext a env)
        (weaken-stable e X a env s) ∙
      ap (λ t → t [ p ]) (weaken-at e X a env s)

  ----------------------------------------------------------------------
  -- The parameters' types

  -- a → U i.
  family-value :
    {n : ℕ} (i : ℕ) (a : Raw.Expression C n) (X : Ob) (env : Vec (Tm X) n)
    → meaning (Types.family i a) X env
      ＝ Model.family-type R products i (meaning a X env)
  family-value i a X env = pi-value i (suc i) a (Formers.universe i) X env

  -- (A → U i) → U i, over A : U i.
  operation-value :
    {n : ℕ} (i : ℕ) (X : Ob) (env : Vec (Tm X) n)
    → meaning (Types.operation i) (X ▸ universe i [ ε X ])
        (ext (universe i [ ε X ]) env)
      ＝ Model.operation-type R products i
  operation-value i X env =
    pi-rewrite (family-level i) (suc i) (Types.family i (Tree.hole fzero))
      (Formers.universe i) (X ▸ universe i [ ε X ])
      (ext (universe i [ ε X ]) env)
      (Model.family-type R products i (q (universe i [ ε X ])))
      (family-value i (Tree.hole fzero) (X ▸ universe i [ ε X ])
        (ext (universe i [ ε X ]) env))
      refl

  -- Π (A : U i). (A → U i) → U i.
  operator-value :
    {n : ℕ} (i : ℕ) (X : Ob) (env : Vec (Tm X) n)
    → meaning (Types.operator i) X env ＝ Model.operator-type R products i
  operator-value i X env =
    pi-rewrite (suc i) (operation-level i) (Formers.universe i)
      (Types.operation i) X env (universe i [ ε X ]) refl
      (operation-value i X env)

  -- f a b, for f an operator.
  operated-value :
    {n : ℕ} (i : ℕ) (f a b : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) {g x y : Tm X}
    → meaning f X env ＝ g → meaning a X env ＝ x → meaning b X env ＝ y
    → meaning (Types.operated i f a b) X env
      ＝ Model.operated R products i g x y
  operated-value i f a b X env refl refl refl =
    application-rewrite (family-level i) (suc i) (Types.family i a)
      (Formers.universe i)
      (Formers.application (suc i) (operation-level i) (Formers.universe i)
        (Types.operation i) f a)
      b X env (Model.family-type R products i (meaning a X env))
      (family-value i a X env) refl
      (application-rewrite (suc i) (operation-level i) (Formers.universe i)
        (Types.operation i) f a X env (universe i [ ε X ]) refl
        (operation-value i X env) refl refl)
      refl

  -- f A B → U i, over A : U i and B : A → U i.
  plus-family-value :
    {n : ℕ} (i : ℕ) (f : Raw.Expression C n) (X : Ob) (env : Vec (Tm X) n)
    → Stable (meaning f) X env
    → let A = universe i [ ε X ]
          F = Model.family-type R products i (q A)
      in meaning (Types.plus-family i f) (X ▸ A ▸ F) (ext F (ext A env))
         ＝ Model.plus-family-type R products i (meaning f X env)
  plus-family-value i f X env s =
    let A = universe i [ ε X ]
        F = Model.family-type R products i (q A)
    in pi-rewrite i (suc i)
         (Types.operated i (Formers.weaken (Formers.weaken f))
           (Tree.hole (fsuc fzero)) (Tree.hole fzero))
         (Formers.universe i) (X ▸ A ▸ F) (ext F (ext A env))
         (Model.operated R products i (meaning f X env [ p ] [ p ])
           (q A [ p ]) (q F))
         (operated-value i (Formers.weaken (Formers.weaken f))
           (Tree.hole (fsuc fzero)) (Tree.hole fzero) (X ▸ A ▸ F)
           (ext F (ext A env)) (weakened² f X A F env s) refl refl)
         refl

  -- Π (B : A → U i). f A B → U i, over A : U i.
  plus-operation-value :
    {n : ℕ} (i : ℕ) (f : Raw.Expression C n) (X : Ob) (env : Vec (Tm X) n)
    → Stable (meaning f) X env
    → meaning (Types.plus-operation i f) (X ▸ universe i [ ε X ])
        (ext (universe i [ ε X ]) env)
      ＝ Model.plus-operation-type R products i (meaning f X env)
  plus-operation-value i f X env s =
    pi-rewrite (family-level i) (family-level i)
      (Types.family i (Tree.hole fzero)) (Types.plus-family i f)
      (X ▸ universe i [ ε X ]) (ext (universe i [ ε X ]) env)
      (Model.family-type R products i (q (universe i [ ε X ])))
      (family-value i (Tree.hole fzero) (X ▸ universe i [ ε X ])
        (ext (universe i [ ε X ]) env))
      (plus-family-value i f X env s)

  -- Π (A : U i) (B : A → U i). f A B → U i.
  operator-decoding-value :
    {n : ℕ} (i : ℕ) (f : Raw.Expression C n) (X : Ob) (env : Vec (Tm X) n)
    → Stable (meaning f) X env
    → meaning (Types.operator-decoding i f) X env
      ＝ Model.plus-decoding-type R products i (meaning f X env)
  operator-decoding-value i f X env s =
    pi-rewrite (suc i) (plus-level i) (Formers.universe i)
      (Types.plus-operation i f) X env (universe i [ ε X ]) refl
      (plus-operation-value i f X env s)

  -- The parameters' values are stable.
  record Stable-Parameters
    {n : ℕ} (U0 E0 U+ E+ : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) : Set ℓ where
    field
      base-stable : Stable (meaning U0) X env
      base-decoding-stable : Stable (meaning E0) X env
      step-stable : Stable (meaning U+) X env
      step-decoding-stable : Stable (meaning E+) X env

  -- So are their weakenings, at an extension by d.
  weakened :
    {n : ℕ} (U0 E0 U+ E+ : Raw.Expression C n) (X : Ob) (d : Tm X)
    (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Stable-Parameters (Formers.weaken U0) (Formers.weaken E0)
        (Formers.weaken U+) (Formers.weaken E+) (X ▸ d) (ext d env)
  weakened U0 E0 U+ E+ X d env S =
    let open Stable-Parameters S
    in record
      { base-stable = weaken-stable U0 X d env base-stable
      ; base-decoding-stable = weaken-stable E0 X d env base-decoding-stable
      ; step-stable = weaken-stable U+ X d env step-stable
      ; step-decoding-stable = weaken-stable E+ X d env step-decoding-stable
      }

  ----------------------------------------------------------------------
  -- Types over the subuniverse

  -- El A → Ma.
  family-of-value :
    {n : ℕ} (i : ℕ) (U0 E0 U+ E+ A : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → meaning (Types.family-of i U0 E0 U+ E+ A) X env
      ＝ Model.family-of-type R products operations i (meaning U0 X env)
          (meaning E0 X env) (meaning U+ X env) (meaning E+ X env)
          (meaning A X env)
  family-of-value i U0 E0 U+ E+ A X env S =
    let open Stable-Parameters S
        D = decoding i (meaning U0 X env) (meaning E0 X env)
              (meaning U+ X env) (meaning E+ X env) (meaning A X env)
    in pi-rewrite i i (Formers.decoding i U0 E0 U+ E+ A)
         (Formers.subuniverse i (Formers.weaken U0) (Formers.weaken E0)
           (Formers.weaken U+) (Formers.weaken E+))
         X env D refl
         (ap₄ (subuniverse i) (weaken-at U0 X D env base-stable)
           (weaken-at E0 X D env base-decoding-stable)
           (weaken-at U+ X D env step-stable)
           (weaken-at E+ X D env step-decoding-stable))

  -- B x, for x the variable of El A.
  applied-value :
    {n : ℕ} (i : ℕ) (U0 E0 U+ E+ A B : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Stable (meaning A) X env → Stable (meaning B) X env
    → let D = decoding i (meaning U0 X env) (meaning E0 X env)
                (meaning U+ X env) (meaning E+ X env) (meaning A X env)
      in meaning (Types.applied i U0 E0 U+ E+ A B) (X ▸ D) (ext D env)
         ＝ Model.applied-term R products operations i (meaning U0 X env)
             (meaning E0 X env) (meaning U+ X env) (meaning E+ X env)
             (meaning A X env) (meaning B X env)
  applied-value i U0 E0 U+ E+ A B X env S sA sB =
    let open Stable-Parameters S
        u0 = meaning U0 X env
        e0 = meaning E0 X env
        u+ = meaning U+ X env
        e+ = meaning E+ X env
        D = decoding i u0 e0 u+ e+ (meaning A X env)
        D′ = decoding i (u0 [ p ]) (e0 [ p ]) (u+ [ p ]) (e+ [ p ])
               (meaning A X env [ p ])
    in application-rewrite i i
         (Formers.decoding i (Formers.weaken U0) (Formers.weaken E0)
           (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken A))
         (Formers.subuniverse i (Formers.weaken (Formers.weaken U0))
           (Formers.weaken (Formers.weaken E0))
           (Formers.weaken (Formers.weaken U+))
           (Formers.weaken (Formers.weaken E+)))
         (Formers.weaken B) (Tree.hole fzero) (X ▸ D) (ext D env) D′
         (ap₅ (decoding i) (weaken-at U0 X D env base-stable)
           (weaken-at E0 X D env base-decoding-stable)
           (weaken-at U+ X D env step-stable)
           (weaken-at E+ X D env step-decoding-stable)
           (weaken-at A X D env sA))
         (ap₄ (subuniverse i) (weakened² U0 X D D′ env base-stable)
           (weakened² E0 X D D′ env base-decoding-stable)
           (weakened² U+ X D D′ env step-stable)
           (weakened² E+ X D D′ env step-decoding-stable))
         (weaken-at B X D env sB) refl

  -- λ x. El (B x).
  decoded-value :
    {n : ℕ} (i : ℕ) (U0 E0 U+ E+ A B : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Stable (meaning A) X env → Stable (meaning B) X env
    → meaning (Types.decoded i U0 E0 U+ E+ A B) X env
      ＝ Model.decoded-term R products operations i (meaning U0 X env)
          (meaning E0 X env) (meaning U+ X env) (meaning E+ X env)
          (meaning A X env) (meaning B X env)
  decoded-value i U0 E0 U+ E+ A B X env S sA sB =
    let open Stable-Parameters S
        D = decoding i (meaning U0 X env) (meaning E0 X env)
              (meaning U+ X env) (meaning E+ X env) (meaning A X env)
    in lambda-rewrite i (suc i) (Formers.decoding i U0 E0 U+ E+ A)
         (Formers.universe i)
         (Formers.decoding i (Formers.weaken U0) (Formers.weaken E0)
           (Formers.weaken U+) (Formers.weaken E+)
           (Types.applied i U0 E0 U+ E+ A B))
         X env D refl refl
         (ap₅ (decoding i) (weaken-at U0 X D env base-stable)
           (weaken-at E0 X D env base-decoding-stable)
           (weaken-at U+ X D env step-stable)
           (weaken-at E+ X D env step-decoding-stable)
           (applied-value i U0 E0 U+ E+ A B X env S sA sB))

  -- U+ (El A) (λ x. El (B x)).
  point-type-value :
    {n : ℕ} (i : ℕ) (U0 E0 U+ E+ A B : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Stable (meaning A) X env → Stable (meaning B) X env
    → meaning (Types.point-type i U0 E0 U+ E+ A B) X env
      ＝ Model.point-type R products operations i (meaning U0 X env)
          (meaning E0 X env) (meaning U+ X env) (meaning E+ X env)
          (meaning A X env) (meaning B X env)
  point-type-value i U0 E0 U+ E+ A B X env S sA sB =
    operated-value i U+ (Formers.decoding i U0 E0 U+ E+ A)
      (Types.decoded i U0 E0 U+ E+ A B) X env refl refl
      (decoded-value i U0 E0 U+ E+ A B X env S sA sB)

  -- U+ (El A) B → U i, over B : El A → U i.
  decoded-plus-value :
    {n : ℕ} (i : ℕ) (U0 E0 U+ E+ A : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Stable (meaning A) X env
    → let F = Model.family-type R products i
                (decoding i (meaning U0 X env) (meaning E0 X env)
                  (meaning U+ X env) (meaning E+ X env) (meaning A X env))
      in meaning (Types.decoded-plus i U0 E0 U+ E+ A) (X ▸ F) (ext F env)
         ＝ Model.decoded-plus-type R products operations i (meaning U0 X env)
             (meaning E0 X env) (meaning U+ X env) (meaning E+ X env)
             (meaning A X env)
  decoded-plus-value i U0 E0 U+ E+ A X env S sA =
    let open Stable-Parameters S
        u0 = meaning U0 X env
        e0 = meaning E0 X env
        u+ = meaning U+ X env
        e+ = meaning E+ X env
        α = meaning A X env
        F = Model.family-type R products i (decoding i u0 e0 u+ e+ α)
    in pi-rewrite i (suc i)
         (Types.operated i (Formers.weaken U+)
           (Formers.decoding i (Formers.weaken U0) (Formers.weaken E0)
             (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken A))
           (Tree.hole fzero))
         (Formers.universe i) (X ▸ F) (ext F env)
         (Model.operated R products i (u+ [ p ])
           (decoding i (u0 [ p ]) (e0 [ p ]) (u+ [ p ]) (e+ [ p ]) (α [ p ]))
           (q F))
         (operated-value i (Formers.weaken U+)
           (Formers.decoding i (Formers.weaken U0) (Formers.weaken E0)
             (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken A))
           (Tree.hole fzero) (X ▸ F) (ext F env)
           (weaken-at U+ X F env step-stable)
           (ap₅ (decoding i) (weaken-at U0 X F env base-stable)
             (weaken-at E0 X F env base-decoding-stable)
             (weaken-at U+ X F env step-stable)
             (weaken-at E+ X F env step-decoding-stable)
             (weaken-at A X F env sA))
           refl)
         refl

  -- E+ (El A) (λ x. El (B x)) c.
  decoding-closure-value :
    {n : ℕ} (i : ℕ) (U0 E0 U+ E+ A B c : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Stable (meaning A) X env → Stable (meaning B) X env
    → meaning (Types.decoding-closure i U0 E0 U+ E+ A B c) X env
      ＝ Model.decoding-closure R products operations i (meaning U0 X env)
          (meaning E0 X env) (meaning U+ X env) (meaning E+ X env)
          (meaning A X env) (meaning B X env) (meaning c X env)
  decoding-closure-value i U0 E0 U+ E+ A B c X env S sA sB =
    let open Stable-Parameters S
        u0 = meaning U0 X env
        e0 = meaning E0 X env
        u+ = meaning U+ X env
        e+ = meaning E+ X env
        α = meaning A X env
        dA = Formers.decoding i U0 E0 U+ E+ A
        k = Formers.application (suc i) (plus-level i) (Formers.universe i)
              (Types.plus-operation i U+) E+ dA
        h = Formers.application (family-level i) (family-level i)
              (Types.family i dA) (Types.decoded-plus i U0 E0 U+ E+ A) k
              (Types.decoded i U0 E0 U+ E+ A B)
    in application-rewrite i (suc i) (Types.point-type i U0 E0 U+ E+ A B)
           (Formers.universe i) h c X env
           (Model.point-type R products operations i u0 e0 u+ e+ α
             (meaning B X env))
           (point-type-value i U0 E0 U+ E+ A B X env S sA sB) refl
           (application-rewrite (family-level i) (family-level i)
             (Types.family i dA) (Types.decoded-plus i U0 E0 U+ E+ A) k
             (Types.decoded i U0 E0 U+ E+ A B) X env
             (Model.family-type R products i (decoding i u0 e0 u+ e+ α))
             (family-value i dA X env)
             (decoded-plus-value i U0 E0 U+ E+ A X env S sA)
             (application-rewrite (suc i) (plus-level i) (Formers.universe i)
               (Types.plus-operation i U+) E+ dA X env (universe i [ ε X ])
               refl (plus-operation-value i U+ X env step-stable) refl refl)
             (decoded-value i U0 E0 U+ E+ A B X env S sA sB))
           refl ∙
         Model.decoding-closure-unfold R products operations i
             (meaning U0 X env) (meaning E0 X env) (meaning U+ X env)
             (meaning E+ X env) (meaning A X env) (meaning B X env)
             (meaning c X env) ⁻¹

  ----------------------------------------------------------------------
  -- Types of induction

  -- Ma → U j, and M a.
  motive-type-value :
    {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → meaning (Types.motive-type i j U0 E0 U+ E+) X env
      ＝ Model.motive-type R products operations i j (meaning U0 X env)
          (meaning E0 X env) (meaning U+ X env) (meaning E+ X env)
  motive-type-value i j U0 E0 U+ E+ X env =
    pi-value i (suc j) (Formers.subuniverse i U0 E0 U+ E+)
      (Formers.universe j) X env

  motive-at-value :
    {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M a : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → meaning (Types.motive-at i j U0 E0 U+ E+ M a) X env
      ＝ Model.motive-at R products operations i j (meaning U0 X env)
          (meaning E0 X env) (meaning U+ X env) (meaning E+ X env)
          (meaning M X env) (meaning a X env)
  motive-at-value i j U0 E0 U+ E+ M a X env =
    application-value i (suc j) (Formers.subuniverse i U0 E0 U+ E+)
      (Formers.universe j) M a X env

  -- M (El0' u), for u the variable of an extension by d.
  inclusion-motive :
    {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M : Raw.Expression C n) (X : Ob)
    (d : Tm X) (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Stable (meaning M) X env
    → meaning
        (Types.motive-at i j (Formers.weaken U0) (Formers.weaken E0)
          (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken M)
          (Formers.inclusion i (Formers.weaken U0) (Formers.weaken E0)
            (Formers.weaken U+) (Formers.weaken E+) (Tree.hole fzero)))
        (X ▸ d) (ext d env)
      ＝ Model.motive-at R products operations i j (meaning U0 X env [ p ])
          (meaning E0 X env [ p ]) (meaning U+ X env [ p ])
          (meaning E+ X env [ p ]) (meaning M X env [ p ])
          (inclusion i (meaning U0 X env [ p ]) (meaning E0 X env [ p ])
            (meaning U+ X env [ p ]) (meaning E+ X env [ p ]) (q d))
  inclusion-motive i j U0 E0 U+ E+ M X d env S sM =
    let open Stable-Parameters S
    in motive-at-value i j (Formers.weaken U0) (Formers.weaken E0)
           (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken M)
           (Formers.inclusion i (Formers.weaken U0) (Formers.weaken E0)
             (Formers.weaken U+) (Formers.weaken E+) (Tree.hole fzero))
           (X ▸ d) (ext d env) ∙
         ap₅
           (λ u e v w h →
              Model.motive-at R products operations i j u e v w h
                (inclusion i u e v w (q d)))
           (weaken-at U0 X d env base-stable)
           (weaken-at E0 X d env base-decoding-stable)
           (weaken-at U+ X d env step-stable)
           (weaken-at E+ X d env step-decoding-stable)
           (weaken-at M X d env sM)

  -- Π (u : U0). M (El0' u).
  inclusion-method-value :
    {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Stable (meaning M) X env
    → meaning (Types.inclusion-method i j U0 E0 U+ E+ M) X env
      ＝ Model.inclusion-method-type R products operations i j
          (meaning U0 X env) (meaning E0 X env) (meaning U+ X env)
          (meaning E+ X env) (meaning M X env)
  inclusion-method-value i j U0 E0 U+ E+ M X env S sM =
    pi-rewrite i j U0
      (Types.motive-at i j (Formers.weaken U0) (Formers.weaken E0)
        (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken M)
        (Formers.inclusion i (Formers.weaken U0) (Formers.weaken E0)
          (Formers.weaken U+) (Formers.weaken E+) (Tree.hole fzero)))
      X env (meaning U0 X env) refl
      (inclusion-motive i j U0 E0 U+ E+ M X (meaning U0 X env) env S sM)

  -- b u, induction at an inclusion.
  induction-inclusion-value :
    {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M b u : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Stable (meaning M) X env
    → meaning (Types.induction-inclusion i j U0 E0 U+ E+ M b u) X env
      ＝ Model.induction-inclusion R products operations i j
          (meaning U0 X env) (meaning E0 X env) (meaning U+ X env)
          (meaning E+ X env) (meaning M X env) (meaning b X env)
          (meaning u X env)
  induction-inclusion-value i j U0 E0 U+ E+ M b u X env S sM =
    application-rewrite i j U0
      (Types.motive-at i j (Formers.weaken U0) (Formers.weaken E0)
        (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken M)
        (Formers.inclusion i (Formers.weaken U0) (Formers.weaken E0)
          (Formers.weaken U+) (Formers.weaken E+) (Tree.hole fzero)))
      b u X env (meaning U0 X env) refl
      (inclusion-motive i j U0 E0 U+ E+ M X (meaning U0 X env) env S sM)
      refl refl

  -- M (El+' A B c), for c the variable of an extension by d.
  closure-motive :
    {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M A B : Raw.Expression C n) (X : Ob)
    (d : Tm X) (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Stable (meaning M) X env → Stable (meaning A) X env
    → Stable (meaning B) X env
    → meaning
        (Types.motive-at i j (Formers.weaken U0) (Formers.weaken E0)
          (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken M)
          (Formers.closure i (Formers.weaken U0) (Formers.weaken E0)
            (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken A)
            (Formers.weaken B) (Tree.hole fzero)))
        (X ▸ d) (ext d env)
      ＝ Model.motive-at R products operations i j (meaning U0 X env [ p ])
          (meaning E0 X env [ p ]) (meaning U+ X env [ p ])
          (meaning E+ X env [ p ]) (meaning M X env [ p ])
          (closure i (meaning U0 X env [ p ]) (meaning E0 X env [ p ])
            (meaning U+ X env [ p ]) (meaning E+ X env [ p ])
            (meaning A X env [ p ]) (meaning B X env [ p ]) (q d))
  closure-motive i j U0 E0 U+ E+ M A B X d env S sM sA sB =
    let open Stable-Parameters S
    in motive-at-value i j (Formers.weaken U0) (Formers.weaken E0)
           (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken M)
           (Formers.closure i (Formers.weaken U0) (Formers.weaken E0)
             (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken A)
             (Formers.weaken B) (Tree.hole fzero))
           (X ▸ d) (ext d env) ∙
         ap₇
           (λ u e v w h a b →
              Model.motive-at R products operations i j u e v w h
                (closure i u e v w a b (q d)))
           (weaken-at U0 X d env base-stable)
           (weaken-at E0 X d env base-decoding-stable)
           (weaken-at U+ X d env step-stable)
           (weaken-at E+ X d env step-decoding-stable)
           (weaken-at M X d env sM) (weaken-at A X d env sA)
           (weaken-at B X d env sB)

  -- The closure method's type, Π by Π from inside: Π (c : U+ (El A) …).
  -- M (El+' A B c).
  closure-fourth-value :
    {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M A B : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Stable (meaning M) X env → Stable (meaning A) X env
    → Stable (meaning B) X env
    → meaning (Types.closure-fourth i j U0 E0 U+ E+ M A B) X env
      ＝ Model.closure-fourth-type R products operations i j
          (meaning U0 X env) (meaning E0 X env) (meaning U+ X env)
          (meaning E+ X env) (meaning M X env) (meaning A X env)
          (meaning B X env)
  closure-fourth-value i j U0 E0 U+ E+ M A B X env S sM sA sB =
    let P = Model.point-type R products operations i (meaning U0 X env)
              (meaning E0 X env) (meaning U+ X env) (meaning E+ X env)
              (meaning A X env) (meaning B X env)
    in pi-rewrite i j (Types.point-type i U0 E0 U+ E+ A B)
           (Types.motive-at i j (Formers.weaken U0) (Formers.weaken E0)
             (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken M)
             (Formers.closure i (Formers.weaken U0) (Formers.weaken E0)
               (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken A)
               (Formers.weaken B) (Tree.hole fzero)))
           X env P (point-type-value i U0 E0 U+ E+ A B X env S sA sB)
           (closure-motive i j U0 E0 U+ E+ M A B X P env S sM sA sB) ∙
      Model.closure-fourth-type-unfold R products operations i j
          (meaning U0 X env) (meaning E0 X env) (meaning U+ X env)
          (meaning E+ X env) (meaning M X env) (meaning A X env)
          (meaning B X env) ⁻¹

  -- The fourth type at the weakened arguments, at an extension by d.
  fourth-weakened :
    {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M A B : Raw.Expression C n) (X : Ob)
    (d : Tm X) (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Stable (meaning M) X env → Stable (meaning A) X env
    → Stable (meaning B) X env
    → meaning
        (Types.closure-fourth i j (Formers.weaken U0) (Formers.weaken E0)
          (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken M)
          (Formers.weaken A) (Formers.weaken B))
        (X ▸ d) (ext d env)
      ＝ Model.closure-fourth-type R products operations i j
          (meaning U0 X env [ p ]) (meaning E0 X env [ p ])
          (meaning U+ X env [ p ]) (meaning E+ X env [ p ])
          (meaning M X env [ p ]) (meaning A X env [ p ])
          (meaning B X env [ p ])
  fourth-weakened i j U0 E0 U+ E+ M A B X d env S sM sA sB =
    let open Stable-Parameters S
    in closure-fourth-value i j (Formers.weaken U0) (Formers.weaken E0)
           (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken M)
           (Formers.weaken A) (Formers.weaken B) (X ▸ d) (ext d env)
           (weakened U0 E0 U+ E+ X d env S) (weaken-stable M X d env sM)
           (weaken-stable A X d env sA) (weaken-stable B X d env sB) ∙
         ap₇ (Model.closure-fourth-type R products operations i j)
           (weaken-at U0 X d env base-stable)
           (weaken-at E0 X d env base-decoding-stable)
           (weaken-at U+ X d env step-stable)
           (weaken-at E+ X d env step-decoding-stable)
           (weaken-at M X d env sM) (weaken-at A X d env sA)
           (weaken-at B X d env sB)

  -- M (B x), for x the variable of El A.
  hypothesis-motive :
    {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M A B : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Stable (meaning M) X env → Stable (meaning A) X env
    → Stable (meaning B) X env
    → let D = decoding i (meaning U0 X env) (meaning E0 X env)
                (meaning U+ X env) (meaning E+ X env) (meaning A X env)
      in meaning
           (Types.motive-at i j (Formers.weaken U0) (Formers.weaken E0)
             (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken M)
             (Types.applied i U0 E0 U+ E+ A B))
           (X ▸ D) (ext D env)
         ＝ Model.motive-at R products operations i j (meaning U0 X env [ p ])
             (meaning E0 X env [ p ]) (meaning U+ X env [ p ])
             (meaning E+ X env [ p ]) (meaning M X env [ p ])
             (Model.applied-term R products operations i (meaning U0 X env)
               (meaning E0 X env) (meaning U+ X env) (meaning E+ X env)
               (meaning A X env) (meaning B X env))
  hypothesis-motive i j U0 E0 U+ E+ M A B X env S sM sA sB =
    let open Stable-Parameters S
        D = decoding i (meaning U0 X env) (meaning E0 X env)
              (meaning U+ X env) (meaning E+ X env) (meaning A X env)
    in motive-at-value i j (Formers.weaken U0) (Formers.weaken E0)
           (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken M)
           (Types.applied i U0 E0 U+ E+ A B) (X ▸ D) (ext D env) ∙
         ap₆ (Model.motive-at R products operations i j)
           (weaken-at U0 X D env base-stable)
           (weaken-at E0 X D env base-decoding-stable)
           (weaken-at U+ X D env step-stable)
           (weaken-at E+ X D env step-decoding-stable)
           (weaken-at M X D env sM)
           (applied-value i U0 E0 U+ E+ A B X env S sA sB)

  -- Π (x : El A). M (B x).
  hypotheses-value :
    {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M A B : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Stable (meaning M) X env → Stable (meaning A) X env
    → Stable (meaning B) X env
    → meaning (Types.induction-hypotheses i j U0 E0 U+ E+ M A B) X env
      ＝ Model.hypotheses-type R products operations i j (meaning U0 X env)
          (meaning E0 X env) (meaning U+ X env) (meaning E+ X env)
          (meaning M X env) (meaning A X env) (meaning B X env)
  hypotheses-value i j U0 E0 U+ E+ M A B X env S sM sA sB =
    pi-rewrite i j (Formers.decoding i U0 E0 U+ E+ A)
        (Types.motive-at i j (Formers.weaken U0) (Formers.weaken E0)
          (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken M)
          (Types.applied i U0 E0 U+ E+ A B))
        X env
        (decoding i (meaning U0 X env) (meaning E0 X env) (meaning U+ X env)
          (meaning E+ X env) (meaning A X env))
        refl (hypothesis-motive i j U0 E0 U+ E+ M A B X env S sM sA sB) ∙
      Model.hypotheses-type-unfold R products operations i j
          (meaning U0 X env) (meaning E0 X env) (meaning U+ X env)
          (meaning E+ X env) (meaning M X env) (meaning A X env)
          (meaning B X env) ⁻¹

  -- Π (k : Π (x : El A). M (B x)). Π (c : …). M (El+' A B c).
  closure-third-value :
    {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M A B : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Stable (meaning M) X env → Stable (meaning A) X env
    → Stable (meaning B) X env
    → meaning (Types.closure-third i j U0 E0 U+ E+ M A B) X env
      ＝ Model.closure-third-type R products operations i j
          (meaning U0 X env) (meaning E0 X env) (meaning U+ X env)
          (meaning E+ X env) (meaning M X env) (meaning A X env)
          (meaning B X env)
  closure-third-value i j U0 E0 U+ E+ M A B X env S sM sA sB =
    let H = Model.hypotheses-type R products operations i j
              (meaning U0 X env) (meaning E0 X env) (meaning U+ X env)
              (meaning E+ X env) (meaning M X env) (meaning A X env)
              (meaning B X env)
    in pi-rewrite (fourth-level i j) (fourth-level i j)
           (Types.induction-hypotheses i j U0 E0 U+ E+ M A B)
           (Types.closure-fourth i j (Formers.weaken U0) (Formers.weaken E0)
             (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken M)
             (Formers.weaken A) (Formers.weaken B))
           X env H (hypotheses-value i j U0 E0 U+ E+ M A B X env S sM sA sB)
           (fourth-weakened i j U0 E0 U+ E+ M A B X H env S sM sA sB) ∙
      Model.closure-third-type-unfold R products operations i j
          (meaning U0 X env) (meaning E0 X env) (meaning U+ X env)
          (meaning E+ X env) (meaning M X env) (meaning A X env)
          (meaning B X env) ⁻¹

  -- The third type at the weakened arguments, B the variable of an
  -- extension by d.
  third-weakened :
    {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M A : Raw.Expression C n) (X : Ob)
    (d : Tm X) (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Stable (meaning M) X env → Stable (meaning A) X env
    → meaning
        (Types.closure-third i j (Formers.weaken U0) (Formers.weaken E0)
          (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken M)
          (Formers.weaken A) (Tree.hole fzero))
        (X ▸ d) (ext d env)
      ＝ Model.closure-third-type R products operations i j
          (meaning U0 X env [ p ]) (meaning E0 X env [ p ])
          (meaning U+ X env [ p ]) (meaning E+ X env [ p ])
          (meaning M X env [ p ]) (meaning A X env [ p ]) (q d)
  third-weakened i j U0 E0 U+ E+ M A X d env S sM sA =
    let open Stable-Parameters S
    in closure-third-value i j (Formers.weaken U0) (Formers.weaken E0)
           (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken M)
           (Formers.weaken A) (Tree.hole fzero) (X ▸ d) (ext d env)
           (weakened U0 E0 U+ E+ X d env S) (weaken-stable M X d env sM)
           (weaken-stable A X d env sA)
           (Environment.stable-lookup R fzero (X ▸ d) (ext d env)) ∙
         ap₇ (Model.closure-third-type R products operations i j)
           (weaken-at U0 X d env base-stable)
           (weaken-at E0 X d env base-decoding-stable)
           (weaken-at U+ X d env step-stable)
           (weaken-at E+ X d env step-decoding-stable)
           (weaken-at M X d env sM) (weaken-at A X d env sA) refl

  -- Π (B : El A → Ma). Π (k : …). Π (c : …). M (El+' A B c).
  closure-second-value :
    {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M A : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Stable (meaning M) X env → Stable (meaning A) X env
    → meaning (Types.closure-second i j U0 E0 U+ E+ M A) X env
      ＝ Model.closure-second-type R products operations i j
          (meaning U0 X env) (meaning E0 X env) (meaning U+ X env)
          (meaning E+ X env) (meaning M X env) (meaning A X env)
  closure-second-value i j U0 E0 U+ E+ M A X env S sM sA =
    let F = Model.family-of-type R products operations i (meaning U0 X env)
              (meaning E0 X env) (meaning U+ X env) (meaning E+ X env)
              (meaning A X env)
    in pi-rewrite (i ⊔ℕ i) (third-level i j)
           (Types.family-of i U0 E0 U+ E+ A)
           (Types.closure-third i j (Formers.weaken U0) (Formers.weaken E0)
             (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken M)
             (Formers.weaken A) (Tree.hole fzero))
           X env F (family-of-value i U0 E0 U+ E+ A X env S)
           (third-weakened i j U0 E0 U+ E+ M A X F env S sM sA) ∙
      Model.closure-second-type-unfold R products operations i j
          (meaning U0 X env) (meaning E0 X env) (meaning U+ X env)
          (meaning E+ X env) (meaning M X env) (meaning A X env) ⁻¹

  -- The second type at the weakened arguments, at an extension by d.
  second-weakened :
    {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M A : Raw.Expression C n) (X : Ob)
    (d : Tm X) (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Stable (meaning M) X env → Stable (meaning A) X env
    → meaning
        (Types.closure-second i j (Formers.weaken U0) (Formers.weaken E0)
          (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken M)
          (Formers.weaken A))
        (X ▸ d) (ext d env)
      ＝ Model.closure-second-type R products operations i j
          (meaning U0 X env [ p ]) (meaning E0 X env [ p ])
          (meaning U+ X env [ p ]) (meaning E+ X env [ p ])
          (meaning M X env [ p ]) (meaning A X env [ p ])
  second-weakened i j U0 E0 U+ E+ M A X d env S sM sA =
    let open Stable-Parameters S
    in closure-second-value i j (Formers.weaken U0) (Formers.weaken E0)
           (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken M)
           (Formers.weaken A) (X ▸ d) (ext d env)
           (weakened U0 E0 U+ E+ X d env S) (weaken-stable M X d env sM)
           (weaken-stable A X d env sA) ∙
         ap₆ (Model.closure-second-type R products operations i j)
           (weaken-at U0 X d env base-stable)
           (weaken-at E0 X d env base-decoding-stable)
           (weaken-at U+ X d env step-stable)
           (weaken-at E+ X d env step-decoding-stable)
           (weaken-at M X d env sM) (weaken-at A X d env sA)

  -- Π (h : M A). Π (B : …). Π (k : …). Π (c : …). M (El+' A B c).
  closure-first-value :
    {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M A : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Stable (meaning M) X env → Stable (meaning A) X env
    → meaning (Types.closure-first i j U0 E0 U+ E+ M A) X env
      ＝ Model.closure-first-type R products operations i j
          (meaning U0 X env) (meaning E0 X env) (meaning U+ X env)
          (meaning E+ X env) (meaning M X env) (meaning A X env)
  closure-first-value i j U0 E0 U+ E+ M A X env S sM sA =
    let N = Model.motive-at R products operations i j (meaning U0 X env)
              (meaning E0 X env) (meaning U+ X env) (meaning E+ X env)
              (meaning M X env) (meaning A X env)
    in pi-rewrite j (second-level i j)
           (Types.motive-at i j U0 E0 U+ E+ M A)
           (Types.closure-second i j (Formers.weaken U0) (Formers.weaken E0)
             (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken M)
             (Formers.weaken A))
           X env N (motive-at-value i j U0 E0 U+ E+ M A X env)
           (second-weakened i j U0 E0 U+ E+ M A X N env S sM sA) ∙
      Model.closure-first-type-unfold R products operations i j
          (meaning U0 X env) (meaning E0 X env) (meaning U+ X env)
          (meaning E+ X env) (meaning M X env) (meaning A X env) ⁻¹

  -- The first type at the weakened arguments, A the variable of an
  -- extension by d.
  first-weakened :
    {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M : Raw.Expression C n) (X : Ob)
    (d : Tm X) (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Stable (meaning M) X env
    → meaning
        (Types.closure-first i j (Formers.weaken U0) (Formers.weaken E0)
          (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken M)
          (Tree.hole fzero))
        (X ▸ d) (ext d env)
      ＝ Model.closure-first-type R products operations i j
          (meaning U0 X env [ p ]) (meaning E0 X env [ p ])
          (meaning U+ X env [ p ]) (meaning E+ X env [ p ])
          (meaning M X env [ p ]) (q d)
  first-weakened i j U0 E0 U+ E+ M X d env S sM =
    let open Stable-Parameters S
    in closure-first-value i j (Formers.weaken U0) (Formers.weaken E0)
           (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken M)
           (Tree.hole fzero) (X ▸ d) (ext d env)
           (weakened U0 E0 U+ E+ X d env S) (weaken-stable M X d env sM)
           (Environment.stable-lookup R fzero (X ▸ d) (ext d env)) ∙
         ap₆ (Model.closure-first-type R products operations i j)
           (weaken-at U0 X d env base-stable)
           (weaken-at E0 X d env base-decoding-stable)
           (weaken-at U+ X d env step-stable)
           (weaken-at E+ X d env step-decoding-stable)
           (weaken-at M X d env sM) refl

  -- Π (A : Ma). Π (h : M A). Π (B : …). Π (k : …). Π (c : …).
  -- M (El+' A B c).
  closure-method-value :
    {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Stable (meaning M) X env
    → meaning (Types.closure-method i j U0 E0 U+ E+ M) X env
      ＝ Model.closure-method-type R products operations i j
          (meaning U0 X env) (meaning E0 X env) (meaning U+ X env)
          (meaning E+ X env) (meaning M X env)
  closure-method-value i j U0 E0 U+ E+ M X env S sM =
    let Ma = subuniverse i (meaning U0 X env) (meaning E0 X env)
               (meaning U+ X env) (meaning E+ X env)
    in pi-rewrite i (first-level i j) (Formers.subuniverse i U0 E0 U+ E+)
           (Types.closure-first i j (Formers.weaken U0) (Formers.weaken E0)
             (Formers.weaken U+) (Formers.weaken E+) (Formers.weaken M)
             (Tree.hole fzero))
           X env Ma refl (first-weakened i j U0 E0 U+ E+ M X Ma env S sM) ∙
      Model.closure-method-type-unfold R products operations i j
          (meaning U0 X env) (meaning E0 X env) (meaning U+ X env)
          (meaning E+ X env) (meaning M X env) ⁻¹

  -- s A (ind A) B (λ x. ind (B x)) c, induction at a closure.
  induction-closure-value :
    {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M b s A B c : Raw.Expression C n)
    (X : Ob) (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Stable (meaning M) X env → Stable (meaning b) X env
    → Stable (meaning s) X env → Stable (meaning A) X env
    → Stable (meaning B) X env
    → meaning (Types.induction-closure i j U0 E0 U+ E+ M b s A B c) X env
      ＝ Model.induction-closure R products operations i j
          (meaning U0 X env) (meaning E0 X env) (meaning U+ X env)
          (meaning E+ X env) (meaning M X env) (meaning b X env)
          (meaning s X env) (meaning A X env) (meaning B X env)
          (meaning c X env)
  induction-closure-value
    i j U0 E0 U+ E+ M b s A B c X env S sM sb ss sA sB =
    let open Stable-Parameters S
        u0 = meaning U0 X env
        e0 = meaning E0 X env
        u+ = meaning U+ X env
        e+ = meaning E+ X env
        m = meaning M X env
        α = meaning A X env
        β = meaning B X env
        D = decoding i u0 e0 u+ e+ α
        Ma = subuniverse i u0 e0 u+ e+
        Mα = Model.motive-at R products operations i j u0 e0 u+ e+ m α
        F = Model.family-of-type R products operations i u0 e0 u+ e+ α
        H = Model.hypotheses-type R products operations i j u0 e0 u+ e+ m α β
        P = Model.point-type R products operations i u0 e0 u+ e+ α β
        V0 = Formers.weaken U0
        W0 = Formers.weaken E0
        V+ = Formers.weaken U+
        W+ = Formers.weaken E+
        N = Formers.weaken M
        Bx = Types.applied i U0 E0 U+ E+ A B
        s₁ = Formers.application i (first-level i j)
               (Formers.subuniverse i U0 E0 U+ E+)
               (Types.closure-first i j V0 W0 V+ W+ N (Tree.hole fzero))
               s A
        s₂ = Formers.application j (second-level i j)
               (Types.motive-at i j U0 E0 U+ E+ M A)
               (Types.closure-second i j V0 W0 V+ W+ N (Formers.weaken A))
               s₁ (Formers.subuniverse-induction i j U0 E0 U+ E+ M b s A)
        s₃ = Formers.application (i ⊔ℕ i) (third-level i j)
               (Types.family-of i U0 E0 U+ E+ A)
               (Types.closure-third i j V0 W0 V+ W+ N (Formers.weaken A)
                 (Tree.hole fzero))
               s₂ B
        κ = Formers.lambda i j (Formers.decoding i U0 E0 U+ E+ A)
              (Types.motive-at i j V0 W0 V+ W+ N Bx)
              (Formers.subuniverse-induction i j V0 W0 V+ W+ N
                (Formers.weaken b) (Formers.weaken s) Bx)
        s₄ = Formers.application (fourth-level i j) (fourth-level i j)
               (Types.induction-hypotheses i j U0 E0 U+ E+ M A B)
               (Types.closure-fourth i j V0 W0 V+ W+ N (Formers.weaken A)
                 (Formers.weaken B))
               s₃ κ
    in application-rewrite i j (Types.point-type i U0 E0 U+ E+ A B)
           (Types.motive-at i j V0 W0 V+ W+ N
             (Formers.closure i V0 W0 V+ W+ (Formers.weaken A)
               (Formers.weaken B) (Tree.hole fzero)))
           s₄ c X env P (point-type-value i U0 E0 U+ E+ A B X env S sA sB)
           (closure-motive i j U0 E0 U+ E+ M A B X P env S sM sA sB)
           (application-rewrite (fourth-level i j) (fourth-level i j)
             (Types.induction-hypotheses i j U0 E0 U+ E+ M A B)
             (Types.closure-fourth i j V0 W0 V+ W+ N (Formers.weaken A)
               (Formers.weaken B))
             s₃ κ X env H
             (hypotheses-value i j U0 E0 U+ E+ M A B X env S sM sA sB)
             (fourth-weakened i j U0 E0 U+ E+ M A B X H env S sM sA sB)
             (application-rewrite (i ⊔ℕ i) (third-level i j)
               (Types.family-of i U0 E0 U+ E+ A)
               (Types.closure-third i j V0 W0 V+ W+ N (Formers.weaken A)
                 (Tree.hole fzero))
               s₂ B X env F (family-of-value i U0 E0 U+ E+ A X env S)
               (third-weakened i j U0 E0 U+ E+ M A X F env S sM sA)
               (application-rewrite j (second-level i j)
                 (Types.motive-at i j U0 E0 U+ E+ M A)
                 (Types.closure-second i j V0 W0 V+ W+ N (Formers.weaken A))
                 s₁ (Formers.subuniverse-induction i j U0 E0 U+ E+ M b s A)
                 X env Mα (motive-at-value i j U0 E0 U+ E+ M A X env)
                 (second-weakened i j U0 E0 U+ E+ M A X Mα env S sM sA)
                 (application-rewrite i (first-level i j)
                   (Formers.subuniverse i U0 E0 U+ E+)
                   (Types.closure-first i j V0 W0 V+ W+ N
                     (Tree.hole fzero))
                   s A X env Ma refl
                   (first-weakened i j U0 E0 U+ E+ M X Ma env S sM) refl
                   refl)
                 refl)
               refl)
             (lambda-rewrite i j (Formers.decoding i U0 E0 U+ E+ A)
               (Types.motive-at i j V0 W0 V+ W+ N Bx)
               (Formers.subuniverse-induction i j V0 W0 V+ W+ N
                 (Formers.weaken b) (Formers.weaken s) Bx)
               X env D refl
               (hypothesis-motive i j U0 E0 U+ E+ M A B X env S sM sA sB)
               (ap₈ (induction i j) (weaken-at U0 X D env base-stable)
                 (weaken-at E0 X D env base-decoding-stable)
                 (weaken-at U+ X D env step-stable)
                 (weaken-at E+ X D env step-decoding-stable)
                 (weaken-at M X D env sM) (weaken-at b X D env sb)
                 (weaken-at s X D env ss)
                 (applied-value i U0 E0 U+ E+ A B X env S sA sB))))
           refl ∙
         Model.induction-closure-unfold R products operations i j u0 e0
             u+ e+ m (meaning b X env) (meaning s X env) α β
             (meaning c X env) ⁻¹

  ----------------------------------------------------------------------
  -- The premises

  -- The parameters with their types (Block.parameters), a closure's
  -- arguments (Block.arguments), and the motive and the methods
  -- (Block.methods).
  record Typed-Parameters
    {n : ℕ} (i : ℕ) (U0 E0 U+ E+ : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) : Set ℓ where
    constructor typed-parameters
    field
      base-typed : Typed X env (suc i) U0 (Formers.universe i)
      base-decoding-typed : Typed X env (family-level i) E0 (Types.family i U0)
      step-typed : Typed X env (operator-level i) U+ (Types.operator i)
      step-decoding-typed :
        Typed X env (plus-decoding-level i) E+ (Types.operator-decoding i U+)

  record Typed-Arguments
    {n : ℕ} (i : ℕ) (U0 E0 U+ E+ A B c : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) : Set ℓ where
    constructor typed-arguments
    field
      code-typed : Typed X env i A (Formers.subuniverse i U0 E0 U+ E+)
      family-typed : Typed X env (i ⊔ℕ i) B (Types.family-of i U0 E0 U+ E+ A)
      point-typed : Typed X env i c (Types.point-type i U0 E0 U+ E+ A B)

  record Typed-Methods
    {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M b s : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) : Set ℓ where
    constructor typed-methods
    field
      motive-typed :
        Typed X env (motive-level i j) M (Types.motive-type i j U0 E0 U+ E+)
      inclusion-method-typed :
        Typed X env (inclusion-method-level i j) b
          (Types.inclusion-method i j U0 E0 U+ E+ M)
      closure-method-typed :
        Typed X env (closure-method-level i j) s
          (Types.closure-method i j U0 E0 U+ E+ M)

  -- Typed's fields at given indices. Projected directly, a field's type is
  -- compared with the expected one before its record argument fixes the
  -- indices, and at a compound type that unfolds the type's whole value.
  stable-at :
    {n : ℕ} (X : Ob) (env : Vec (Tm X) n) (l : ℕ) (t A : Raw.Expression C n)
    → Typed X env l t A → Stable (meaning t) X env
  stable-at X env l t A T = term-stable T

  type-at :
    {n : ℕ} (X : Ob) (env : Vec (Tm X) n) (l : ℕ) (t A : Raw.Expression C n)
    → Typed X env l t A → type-of (meaning t X env) ＝ meaning A X env
  type-at X env l t A T = term-type T

  -- Their values: the parameters stable, with the model's typings.
  stable-parameters :
    {n : ℕ} (i : ℕ) (U0 E0 U+ E+ : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Typed-Parameters i U0 E0 U+ E+ X env
    → Stable-Parameters U0 E0 U+ E+ X env
  stable-parameters i U0 E0 U+ E+ X env T =
    let open Typed-Parameters T
    in record
      { base-stable = term-stable base-typed
      ; base-decoding-stable = term-stable base-decoding-typed
      ; step-stable = term-stable step-typed
      ; step-decoding-stable = term-stable step-decoding-typed
      }

  parameters-at :
    {n : ℕ} (i : ℕ) (U0 E0 U+ E+ : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Typed-Parameters i U0 E0 U+ E+ X env
    → Parameters R products i (meaning U0 X env) (meaning E0 X env)
        (meaning U+ X env) (meaning E+ X env)
  parameters-at i U0 E0 U+ E+ X env T =
    let open Typed-Parameters T
    in record
      { base-code = type-at X env (suc i) U0 (Formers.universe i) base-typed
      ; base-decoding-type =
          type-at X env (family-level i) E0 (Types.family i U0)
              base-decoding-typed ∙
            family-value i U0 X env
      ; step-type =
          type-at X env (operator-level i) U+ (Types.operator i)
              step-typed ∙
            operator-value i X env
      ; step-decoding-type =
          type-at X env (plus-decoding-level i) E+
              (Types.operator-decoding i U+) step-decoding-typed ∙
            operator-decoding-value i U+ X env
              (stable-at X env (operator-level i) U+ (Types.operator i)
                step-typed)
      }

  arguments-at :
    {n : ℕ} (i : ℕ) (U0 E0 U+ E+ A B c : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Typed-Arguments i U0 E0 U+ E+ A B c X env
    → Arguments R products operations i (meaning U0 X env)
        (meaning E0 X env) (meaning U+ X env) (meaning E+ X env)
        (meaning A X env) (meaning B X env) (meaning c X env)
  arguments-at i U0 E0 U+ E+ A B c X env S T =
    let open Typed-Arguments T
    in record
      { code-type =
          type-at X env i A (Formers.subuniverse i U0 E0 U+ E+) code-typed
      ; family-type′ =
          type-at X env (i ⊔ℕ i) B (Types.family-of i U0 E0 U+ E+ A)
              family-typed ∙
            family-of-value i U0 E0 U+ E+ A X env S
      ; point-type′ =
          type-at X env i c (Types.point-type i U0 E0 U+ E+ A B)
              point-typed ∙
            point-type-value i U0 E0 U+ E+ A B X env S
              (stable-at X env i A (Formers.subuniverse i U0 E0 U+ E+)
                code-typed)
              (stable-at X env (i ⊔ℕ i) B (Types.family-of i U0 E0 U+ E+ A)
                family-typed)
      }

  methods-at :
    {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M b s : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Typed-Methods i j U0 E0 U+ E+ M b s X env
    → Methods R products operations i j (meaning U0 X env)
        (meaning E0 X env) (meaning U+ X env) (meaning E+ X env)
        (meaning M X env) (meaning b X env) (meaning s X env)
  methods-at i j U0 E0 U+ E+ M b s X env S T =
    let open Typed-Methods T
        sM = stable-at X env (motive-level i j) M
               (Types.motive-type i j U0 E0 U+ E+) motive-typed
    in record
      { motive-type′ =
          type-at X env (motive-level i j) M
              (Types.motive-type i j U0 E0 U+ E+) motive-typed ∙
            motive-type-value i j U0 E0 U+ E+ X env
      ; inclusion-method-type′ =
          type-at X env (inclusion-method-level i j) b
              (Types.inclusion-method i j U0 E0 U+ E+ M)
              inclusion-method-typed ∙
            inclusion-method-value i j U0 E0 U+ E+ M X env S sM
      ; closure-method-type′ =
          type-at X env (closure-method-level i j) s
              (Types.closure-method i j U0 E0 U+ E+ M) closure-method-typed ∙
            closure-method-value i j U0 E0 U+ E+ M X env S sM
      }

  -- The premises at an instance of the environment.
  parameters-[] :
    {n : ℕ} (i : ℕ) (U0 E0 U+ E+ : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Typed-Parameters i U0 E0 U+ E+ X env
    → {Y : Ob} (τ : Hom Y X) → Typed-Parameters i U0 E0 U+ E+ Y (env [ τ ]ᵉ)
  parameters-[] i U0 E0 U+ E+ X env T τ =
    let open Typed-Parameters T
    in typed-parameters
         (typed-[] X env (suc i) U0 (Formers.universe i) base-typed τ)
         (typed-[] X env (family-level i) E0 (Types.family i U0)
           base-decoding-typed τ)
         (typed-[] X env (operator-level i) U+ (Types.operator i) step-typed
           τ)
         (typed-[] X env (plus-decoding-level i) E+
           (Types.operator-decoding i U+) step-decoding-typed τ)

  arguments-[] :
    {n : ℕ} (i : ℕ) (U0 E0 U+ E+ A B c : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Typed-Arguments i U0 E0 U+ E+ A B c X env
    → {Y : Ob} (τ : Hom Y X)
    → Typed-Arguments i U0 E0 U+ E+ A B c Y (env [ τ ]ᵉ)
  arguments-[] i U0 E0 U+ E+ A B c X env T τ =
    let open Typed-Arguments T
    in typed-arguments
         (typed-[] X env i A (Formers.subuniverse i U0 E0 U+ E+) code-typed
           τ)
         (typed-[] X env (i ⊔ℕ i) B (Types.family-of i U0 E0 U+ E+ A)
           family-typed τ)
         (typed-[] X env i c (Types.point-type i U0 E0 U+ E+ A B)
           point-typed τ)

  methods-[] :
    {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M b s : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Typed-Methods i j U0 E0 U+ E+ M b s X env
    → {Y : Ob} (τ : Hom Y X)
    → Typed-Methods i j U0 E0 U+ E+ M b s Y (env [ τ ]ᵉ)
  methods-[] i j U0 E0 U+ E+ M b s X env T τ =
    let open Typed-Methods T
    in typed-methods
         (typed-[] X env (motive-level i j) M
           (Types.motive-type i j U0 E0 U+ E+) motive-typed τ)
         (typed-[] X env (inclusion-method-level i j) b
           (Types.inclusion-method i j U0 E0 U+ E+ M) inclusion-method-typed
           τ)
         (typed-[] X env (closure-method-level i j) s
           (Types.closure-method i j U0 E0 U+ E+ M) closure-method-typed τ)

  ----------------------------------------------------------------------
  -- The formers

  subuniverse-typed :
    {n : ℕ} (i : ℕ) (U0 E0 U+ E+ : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Parameters R products i (meaning U0 X env) (meaning E0 X env)
        (meaning U+ X env) (meaning E+ X env)
    → Typed X env (suc i) (Formers.subuniverse i U0 E0 U+ E+)
        (Formers.universe i)
  subuniverse-typed i U0 E0 U+ E+ X env S P =
    let open Stable-Parameters S
    in as-type X env i (Formers.subuniverse i U0 E0 U+ E+)
         (λ Y τ →
            ap₄ (subuniverse i) (base-stable Y τ)
                (base-decoding-stable Y τ) (step-stable Y τ)
                (step-decoding-stable Y τ) ∙
              subuniverse-[] i (meaning U0 X env) (meaning E0 X env)
                  (meaning U+ X env) (meaning E+ X env) τ P ⁻¹)
         (subuniverse-code i (meaning U0 X env) (meaning E0 X env)
           (meaning U+ X env) (meaning E+ X env) P)

  inclusion-typed :
    {n : ℕ} (i : ℕ) (U0 E0 U+ E+ u : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Parameters R products i (meaning U0 X env) (meaning E0 X env)
        (meaning U+ X env) (meaning E+ X env)
    → Typed X env i u U0
    → Typed X env i (Formers.inclusion i U0 E0 U+ E+ u)
        (Formers.subuniverse i U0 E0 U+ E+)
  inclusion-typed i U0 E0 U+ E+ u X env S P Tu =
    let open Stable-Parameters S
        T = subuniverse-typed i U0 E0 U+ E+ X env S P
    in record
      { type-stable =
          stable-at X env (suc i) (Formers.subuniverse i U0 E0 U+ E+)
            (Formers.universe i) T
      ; type-code =
          type-at X env (suc i) (Formers.subuniverse i U0 E0 U+ E+)
            (Formers.universe i) T
      ; term-stable = λ Y τ →
          ap₅ (inclusion i) (base-stable Y τ) (base-decoding-stable Y τ)
              (step-stable Y τ) (step-decoding-stable Y τ)
              (term-stable Tu Y τ) ∙
            inclusion-[] i (meaning U0 X env) (meaning E0 X env)
                (meaning U+ X env) (meaning E+ X env) (meaning u X env) τ P
                (term-type Tu) ⁻¹
      ; term-type =
          inclusion-type i (meaning U0 X env) (meaning E0 X env)
            (meaning U+ X env) (meaning E+ X env) (meaning u X env) P
            (term-type Tu)
      }

  closure-typed :
    {n : ℕ} (i : ℕ) (U0 E0 U+ E+ A B c : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Parameters R products i (meaning U0 X env) (meaning E0 X env)
        (meaning U+ X env) (meaning E+ X env)
    → Typed-Arguments i U0 E0 U+ E+ A B c X env
    → Typed X env i (Formers.closure i U0 E0 U+ E+ A B c)
        (Formers.subuniverse i U0 E0 U+ E+)
  closure-typed i U0 E0 U+ E+ A B c X env S P TA =
    let open Stable-Parameters S
        open Typed-Arguments TA
        T = subuniverse-typed i U0 E0 U+ E+ X env S P
        Q = arguments-at i U0 E0 U+ E+ A B c X env S TA
    in record
      { type-stable =
          stable-at X env (suc i) (Formers.subuniverse i U0 E0 U+ E+)
            (Formers.universe i) T
      ; type-code =
          type-at X env (suc i) (Formers.subuniverse i U0 E0 U+ E+)
            (Formers.universe i) T
      ; term-stable = λ Y τ →
          ap₇ (closure i) (base-stable Y τ) (base-decoding-stable Y τ)
              (step-stable Y τ) (step-decoding-stable Y τ)
              (term-stable code-typed Y τ) (term-stable family-typed Y τ)
              (term-stable point-typed Y τ) ∙
            closure-[] i (meaning U0 X env) (meaning E0 X env)
                (meaning U+ X env) (meaning E+ X env) (meaning A X env)
                (meaning B X env) (meaning c X env) τ P Q ⁻¹
      ; term-type =
          closure-type i (meaning U0 X env) (meaning E0 X env)
            (meaning U+ X env) (meaning E+ X env) (meaning A X env)
            (meaning B X env) (meaning c X env) P Q
      }

  decoding-typed :
    {n : ℕ} (i : ℕ) (U0 E0 U+ E+ a : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Parameters R products i (meaning U0 X env) (meaning E0 X env)
        (meaning U+ X env) (meaning E+ X env)
    → Typed X env i a (Formers.subuniverse i U0 E0 U+ E+)
    → Typed X env (suc i) (Formers.decoding i U0 E0 U+ E+ a)
        (Formers.universe i)
  decoding-typed i U0 E0 U+ E+ a X env S P Ta =
    let open Stable-Parameters S
    in as-type X env i (Formers.decoding i U0 E0 U+ E+ a)
         (λ Y τ →
            ap₅ (decoding i) (base-stable Y τ)
                (base-decoding-stable Y τ) (step-stable Y τ)
                (step-decoding-stable Y τ) (term-stable Ta Y τ) ∙
              decoding-[] i (meaning U0 X env) (meaning E0 X env)
                  (meaning U+ X env) (meaning E+ X env) (meaning a X env) τ
                  P (term-type Ta) ⁻¹)
         (decoding-code i (meaning U0 X env) (meaning E0 X env)
           (meaning U+ X env) (meaning E+ X env) (meaning a X env) P
           (term-type Ta))

  -- M a, a type at level j: Pi's application at the universe.
  motive-at-typed :
    {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M a : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Typed X env (suc i) (Formers.subuniverse i U0 E0 U+ E+)
        (Formers.universe i)
    → Typed X env (motive-level i j) M (Types.motive-type i j U0 E0 U+ E+)
    → Typed X env i a (Formers.subuniverse i U0 E0 U+ E+)
    → Typed X env (suc j) (Types.motive-at i j U0 E0 U+ E+ M a)
        (Formers.universe j)
  motive-at-typed i j U0 E0 U+ E+ M a X env TMa TM Ta =
    let Ma = meaning (Formers.subuniverse i U0 E0 U+ E+) X env
        T = application-typed i (suc j) (Formers.subuniverse i U0 E0 U+ E+)
              (Formers.universe j) M a X env TMa
              (as-type (X ▸ Ma) (ext Ma env) (suc j) (Formers.universe j)
                (closed-stable (universe j) (X ▸ Ma) (ext Ma env))
                (closed-code R (suc j) (universe j) (ε (X ▸ Ma))
                  (universe-type j)))
              TM Ta
        I = Formers.instantiate (Formers.universe j) a
    in as-type X env j (Types.motive-at i j U0 E0 U+ E+ M a)
         (stable-at X env (suc j) (Types.motive-at i j U0 E0 U+ E+ M a) I T)
         (type-at X env (suc j) (Types.motive-at i j U0 E0 U+ E+ M a) I T ∙
           instantiate-value (Formers.universe j) a X env (term-stable Ta))

  induction-typed :
    {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M b s a : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Stable-Parameters U0 E0 U+ E+ X env
    → Parameters R products i (meaning U0 X env) (meaning E0 X env)
        (meaning U+ X env) (meaning E+ X env)
    → Typed-Methods i j U0 E0 U+ E+ M b s X env
    → Typed X env i a (Formers.subuniverse i U0 E0 U+ E+)
    → Typed X env j (Formers.subuniverse-induction i j U0 E0 U+ E+ M b s a)
        (Types.motive-at i j U0 E0 U+ E+ M a)
  induction-typed i j U0 E0 U+ E+ M b s a X env S P TM Ta =
    let open Stable-Parameters S
        open Typed-Methods TM
        Q = methods-at i j U0 E0 U+ E+ M b s X env S TM
        T = motive-at-typed i j U0 E0 U+ E+ M a X env
              (subuniverse-typed i U0 E0 U+ E+ X env S P) motive-typed Ta
    in record
      { type-stable =
          stable-at X env (suc j) (Types.motive-at i j U0 E0 U+ E+ M a)
            (Formers.universe j) T
      ; type-code =
          type-at X env (suc j) (Types.motive-at i j U0 E0 U+ E+ M a)
            (Formers.universe j) T
      ; term-stable = λ Y τ →
          ap₈ (induction i j) (base-stable Y τ)
              (base-decoding-stable Y τ) (step-stable Y τ)
              (step-decoding-stable Y τ) (term-stable motive-typed Y τ)
              (term-stable inclusion-method-typed Y τ)
              (term-stable closure-method-typed Y τ) (term-stable Ta Y τ) ∙
            induction-[] i j (meaning U0 X env) (meaning E0 X env)
                (meaning U+ X env) (meaning E+ X env) (meaning M X env)
                (meaning b X env) (meaning s X env) (meaning a X env) τ P Q
                (term-type Ta) ⁻¹
      ; term-type =
          induction-type i j (meaning U0 X env) (meaning E0 X env)
              (meaning U+ X env) (meaning E+ X env) (meaning M X env)
              (meaning b X env) (meaning s X env) (meaning a X env) P Q
              (term-type Ta) ∙
            motive-at-value i j U0 E0 U+ E+ M a X env ⁻¹
      }

  ----------------------------------------------------------------------
  -- The equations

  -- A term with another's value at every instance of the environment
  -- has its typing. The instance is typed at length n, as the premises'
  -- instances are: read as an argument of a value it would get the length
  -- 0 + n, and comparing the two spellings unfolds both values.
  equal-typed :
    {n : ℕ} (X : Ob) (env : Vec (Tm X) n) (l : ℕ)
    (t u A : Raw.Expression C n) → Typed X env l t A
    → ((Y : Ob) (τ : Hom Y X)
       → let env′ : Vec (Tm Y) n
             env′ = env [ τ ]ᵉ
         in meaning t Y env′ ＝ meaning u Y env′)
    → meaning t X env ＝ meaning u X env
    → Typed X env l u A
  equal-typed X env l t u A T e e₀ = record
    { type-stable = type-stable T
    ; type-code = type-code T
    ; term-stable = λ Y τ →
        e Y τ ⁻¹ ∙
          (term-stable T Y τ ∙ ap (λ v → v [ τ ]) e₀)
    ; term-type = ap type-of (e₀ ⁻¹) ∙ term-type T
    }

  -- El (El0' u) = E0 u.
  inclusion-decoding-value :
    {n : ℕ} (i : ℕ) (U0 E0 U+ E+ u : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Typed-Parameters i U0 E0 U+ E+ X env
    → Typed X env i u U0
    → meaning
        (Formers.decoding i U0 E0 U+ E+ (Formers.inclusion i U0 E0 U+ E+ u))
        X env
      ＝ meaning (Formers.application i (suc i) U0 (Formers.universe i) E0 u)
          X env
  inclusion-decoding-value i U0 E0 U+ E+ u X env T Tu =
    inclusion-decoding i (meaning U0 X env) (meaning E0 X env)
        (meaning U+ X env) (meaning E+ X env) (meaning u X env)
        (parameters-at i U0 E0 U+ E+ X env T) (term-type Tu) ∙
      application-value i (suc i) U0 (Formers.universe i) E0 u X env ⁻¹

  -- El (El+' A B c) = E+ (El A) (λ x. El (B x)) c.
  closure-decoding-value :
    {n : ℕ} (i : ℕ) (U0 E0 U+ E+ A B c : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Typed-Parameters i U0 E0 U+ E+ X env
    → Typed-Arguments i U0 E0 U+ E+ A B c X env
    → meaning
        (Formers.decoding i U0 E0 U+ E+
          (Formers.closure i U0 E0 U+ E+ A B c))
        X env
      ＝ meaning (Types.decoding-closure i U0 E0 U+ E+ A B c) X env
  closure-decoding-value i U0 E0 U+ E+ A B c X env T TA =
    let open Typed-Arguments TA
        S = stable-parameters i U0 E0 U+ E+ X env T
    in closure-decoding i (meaning U0 X env) (meaning E0 X env)
           (meaning U+ X env) (meaning E+ X env) (meaning A X env)
           (meaning B X env) (meaning c X env)
           (parameters-at i U0 E0 U+ E+ X env T)
           (arguments-at i U0 E0 U+ E+ A B c X env S TA) ∙
         decoding-closure-value i U0 E0 U+ E+ A B c X env S
             (term-stable code-typed) (term-stable family-typed) ⁻¹

  -- maElim at El0' u.
  inclusion-computation-value :
    {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M b s u : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n) → Typed-Parameters i U0 E0 U+ E+ X env
    → Typed-Methods i j U0 E0 U+ E+ M b s X env → Typed X env i u U0
    → meaning
        (Formers.subuniverse-induction i j U0 E0 U+ E+ M b s
          (Formers.inclusion i U0 E0 U+ E+ u))
        X env
      ＝ meaning (Types.induction-inclusion i j U0 E0 U+ E+ M b u) X env
  inclusion-computation-value i j U0 E0 U+ E+ M b s u X env T TM Tu =
    let S = stable-parameters i U0 E0 U+ E+ X env T
    in inclusion-computation i j (meaning U0 X env) (meaning E0 X env)
           (meaning U+ X env) (meaning E+ X env) (meaning M X env)
           (meaning b X env) (meaning s X env) (meaning u X env)
           (parameters-at i U0 E0 U+ E+ X env T)
           (methods-at i j U0 E0 U+ E+ M b s X env S TM) (term-type Tu) ∙
         induction-inclusion-value i j U0 E0 U+ E+ M b u X env S
             (term-stable (Typed-Methods.motive-typed TM)) ⁻¹

  -- maElim at El+' A B c.
  closure-computation-value :
    {n : ℕ} (i j : ℕ) (U0 E0 U+ E+ M b s A B c : Raw.Expression C n)
    (X : Ob) (env : Vec (Tm X) n) → Typed-Parameters i U0 E0 U+ E+ X env
    → Typed-Methods i j U0 E0 U+ E+ M b s X env
    → Typed-Arguments i U0 E0 U+ E+ A B c X env
    → meaning
        (Formers.subuniverse-induction i j U0 E0 U+ E+ M b s
          (Formers.closure i U0 E0 U+ E+ A B c))
        X env
      ＝ meaning (Types.induction-closure i j U0 E0 U+ E+ M b s A B c) X env
  closure-computation-value i j U0 E0 U+ E+ M b s A B c X env T TM TA =
    let open Typed-Methods TM
        open Typed-Arguments TA
        S = stable-parameters i U0 E0 U+ E+ X env T
    in closure-computation i j (meaning U0 X env) (meaning E0 X env)
           (meaning U+ X env) (meaning E+ X env) (meaning M X env)
           (meaning b X env) (meaning s X env) (meaning A X env)
           (meaning B X env) (meaning c X env)
           (parameters-at i U0 E0 U+ E+ X env T)
           (methods-at i j U0 E0 U+ E+ M b s X env S TM)
           (arguments-at i U0 E0 U+ E+ A B c X env S TA) ∙
         induction-closure-value i j U0 E0 U+ E+ M b s A B c X env S
             (term-stable motive-typed) (term-stable inclusion-method-typed)
             (term-stable closure-method-typed) (term-stable code-typed)
             (term-stable family-typed) ⁻¹

  ----------------------------------------------------------------------
  -- The rules of the operations subuniverses

  sound :
    {J : Judgment C} (r : Block.Rule C J)
    → ((k : Fin (length (Block.premises r)))
       → Valid (list-lookup (Block.premises r) k))
    → Valid J
  sound (Block.formation Γ i U0 E0 U+ E+) h =
    let (vΓ , TU0) = h fzero
        (_ , TE0) = h (1 ↑ʳ fzero)
        (_ , TU+) = h (2 ↑ʳ fzero)
        (_ , TE+) = h (3 ↑ʳ fzero)
        X = object Γ
        env = values Γ
        𝒫 : Typed-Parameters i U0 E0 U+ E+ X env
        𝒫 = typed-parameters TU0 TE0 TU+ TE+
    in vΓ
       , subuniverse-typed i U0 E0 U+ E+ X env
           (stable-parameters i U0 E0 U+ E+ X env 𝒫)
           (parameters-at i U0 E0 U+ E+ X env 𝒫)
  sound (Block.inclusion-introduction Γ i U0 E0 U+ E+ u) h =
    let (vΓ , TU0) = h fzero
        (_ , TE0) = h (1 ↑ʳ fzero)
        (_ , TU+) = h (2 ↑ʳ fzero)
        (_ , TE+) = h (3 ↑ʳ fzero)
        (_ , Tu) = h (4 ↑ʳ fzero)
        X = object Γ
        env = values Γ
        𝒫 : Typed-Parameters i U0 E0 U+ E+ X env
        𝒫 = typed-parameters TU0 TE0 TU+ TE+
    in vΓ
       , inclusion-typed i U0 E0 U+ E+ u X env
           (stable-parameters i U0 E0 U+ E+ X env 𝒫)
           (parameters-at i U0 E0 U+ E+ X env 𝒫) Tu
  sound (Block.closure-introduction Γ i U0 E0 U+ E+ A B c) h =
    let (vΓ , TU0) = h fzero
        (_ , TE0) = h (1 ↑ʳ fzero)
        (_ , TU+) = h (2 ↑ʳ fzero)
        (_ , TE+) = h (3 ↑ʳ fzero)
        (_ , TA) = h (4 ↑ʳ fzero)
        (_ , TB) = h (5 ↑ʳ fzero)
        (_ , Tc) = h (6 ↑ʳ fzero)
        X = object Γ
        env = values Γ
        𝒫 : Typed-Parameters i U0 E0 U+ E+ X env
        𝒫 = typed-parameters TU0 TE0 TU+ TE+
    in vΓ
       , closure-typed i U0 E0 U+ E+ A B c X env
           (stable-parameters i U0 E0 U+ E+ X env 𝒫)
           (parameters-at i U0 E0 U+ E+ X env 𝒫) (typed-arguments TA TB Tc)
  sound (Block.decoding-formation Γ i U0 E0 U+ E+ a) h =
    let (vΓ , TU0) = h fzero
        (_ , TE0) = h (1 ↑ʳ fzero)
        (_ , TU+) = h (2 ↑ʳ fzero)
        (_ , TE+) = h (3 ↑ʳ fzero)
        (_ , Ta) = h (4 ↑ʳ fzero)
        X = object Γ
        env = values Γ
        𝒫 : Typed-Parameters i U0 E0 U+ E+ X env
        𝒫 = typed-parameters TU0 TE0 TU+ TE+
    in vΓ
       , decoding-typed i U0 E0 U+ E+ a X env
           (stable-parameters i U0 E0 U+ E+ X env 𝒫)
           (parameters-at i U0 E0 U+ E+ X env 𝒫) Ta
  sound (Block.elimination Γ i j U0 E0 U+ E+ M b s a) h =
    let (vΓ , TU0) = h fzero
        (_ , TE0) = h (1 ↑ʳ fzero)
        (_ , TU+) = h (2 ↑ʳ fzero)
        (_ , TE+) = h (3 ↑ʳ fzero)
        (_ , TM) = h (4 ↑ʳ fzero)
        (_ , Tb) = h (5 ↑ʳ fzero)
        (_ , Ts) = h (6 ↑ʳ fzero)
        (_ , Ta) = h (7 ↑ʳ fzero)
        X = object Γ
        env = values Γ
        𝒫 : Typed-Parameters i U0 E0 U+ E+ X env
        𝒫 = typed-parameters TU0 TE0 TU+ TE+
    in vΓ
       , induction-typed i j U0 E0 U+ E+ M b s a X env
           (stable-parameters i U0 E0 U+ E+ X env 𝒫)
           (parameters-at i U0 E0 U+ E+ X env 𝒫) (typed-methods TM Tb Ts) Ta
  sound (Block.inclusion-decoding Γ i U0 E0 U+ E+ u) h =
    let (vΓ , TU0) = h fzero
        (_ , TE0) = h (1 ↑ʳ fzero)
        (_ , TU+) = h (2 ↑ʳ fzero)
        (_ , TE+) = h (3 ↑ʳ fzero)
        (_ , Tu) = h (4 ↑ʳ fzero)
        X = object Γ
        env = values Γ
        𝒫 : Typed-Parameters i U0 E0 U+ E+ X env
        𝒫 = typed-parameters TU0 TE0 TU+ TE+
        S = stable-parameters i U0 E0 U+ E+ X env 𝒫
        P = parameters-at i U0 E0 U+ E+ X env 𝒫
        v = Formers.inclusion i U0 E0 U+ E+ u
        TL = decoding-typed i U0 E0 U+ E+ v X env S P
               (inclusion-typed i U0 E0 U+ E+ u X env S P Tu)
        e = inclusion-decoding-value i U0 E0 U+ E+ u X env 𝒫 Tu
    in vΓ
       , TL
       , equal-typed X env (suc i) (Formers.decoding i U0 E0 U+ E+ v)
           (Formers.application i (suc i) U0 (Formers.universe i) E0 u)
           (Formers.universe i) TL
           (λ Y τ →
              inclusion-decoding-value i U0 E0 U+ E+ u Y (env [ τ ]ᵉ)
                (parameters-[] i U0 E0 U+ E+ X env 𝒫 τ)
                (typed-[] X env i u U0 Tu τ))
           e
       , e
  sound (Block.closure-decoding Γ i U0 E0 U+ E+ A B c) h =
    let (vΓ , TU0) = h fzero
        (_ , TE0) = h (1 ↑ʳ fzero)
        (_ , TU+) = h (2 ↑ʳ fzero)
        (_ , TE+) = h (3 ↑ʳ fzero)
        (_ , TA) = h (4 ↑ʳ fzero)
        (_ , TB) = h (5 ↑ʳ fzero)
        (_ , Tc) = h (6 ↑ʳ fzero)
        X = object Γ
        env = values Γ
        𝒫 : Typed-Parameters i U0 E0 U+ E+ X env
        𝒫 = typed-parameters TU0 TE0 TU+ TE+
        𝒜 : Typed-Arguments i U0 E0 U+ E+ A B c X env
        𝒜 = typed-arguments TA TB Tc
        S = stable-parameters i U0 E0 U+ E+ X env 𝒫
        P = parameters-at i U0 E0 U+ E+ X env 𝒫
        v = Formers.closure i U0 E0 U+ E+ A B c
        TL = decoding-typed i U0 E0 U+ E+ v X env S P
               (closure-typed i U0 E0 U+ E+ A B c X env S P 𝒜)
        e = closure-decoding-value i U0 E0 U+ E+ A B c X env 𝒫 𝒜
    in vΓ
       , TL
       , equal-typed X env (suc i) (Formers.decoding i U0 E0 U+ E+ v)
           (Types.decoding-closure i U0 E0 U+ E+ A B c) (Formers.universe i)
           TL
           (λ Y τ →
              closure-decoding-value i U0 E0 U+ E+ A B c Y (env [ τ ]ᵉ)
                (parameters-[] i U0 E0 U+ E+ X env 𝒫 τ)
                (arguments-[] i U0 E0 U+ E+ A B c X env 𝒜 τ))
           e
       , e
  sound (Block.inclusion-computation Γ i j U0 E0 U+ E+ M b s u) h =
    let (vΓ , TU0) = h fzero
        (_ , TE0) = h (1 ↑ʳ fzero)
        (_ , TU+) = h (2 ↑ʳ fzero)
        (_ , TE+) = h (3 ↑ʳ fzero)
        (_ , TM) = h (4 ↑ʳ fzero)
        (_ , Tb) = h (5 ↑ʳ fzero)
        (_ , Ts) = h (6 ↑ʳ fzero)
        (_ , Tu) = h (7 ↑ʳ fzero)
        X = object Γ
        env = values Γ
        𝒫 : Typed-Parameters i U0 E0 U+ E+ X env
        𝒫 = typed-parameters TU0 TE0 TU+ TE+
        ℳ : Typed-Methods i j U0 E0 U+ E+ M b s X env
        ℳ = typed-methods TM Tb Ts
        S = stable-parameters i U0 E0 U+ E+ X env 𝒫
        P = parameters-at i U0 E0 U+ E+ X env 𝒫
        v = Formers.inclusion i U0 E0 U+ E+ u
        TL = induction-typed i j U0 E0 U+ E+ M b s v X env S P ℳ
               (inclusion-typed i U0 E0 U+ E+ u X env S P Tu)
        e = inclusion-computation-value i j U0 E0 U+ E+ M b s u X env 𝒫 ℳ Tu
    in vΓ
       , TL
       , equal-typed X env j
           (Formers.subuniverse-induction i j U0 E0 U+ E+ M b s v)
           (Types.induction-inclusion i j U0 E0 U+ E+ M b u)
           (Types.motive-at i j U0 E0 U+ E+ M v) TL
           (λ Y τ →
              inclusion-computation-value i j U0 E0 U+ E+ M b s u Y
                (env [ τ ]ᵉ) (parameters-[] i U0 E0 U+ E+ X env 𝒫 τ)
                (methods-[] i j U0 E0 U+ E+ M b s X env ℳ τ)
                (typed-[] X env i u U0 Tu τ))
           e
       , e
  sound (Block.closure-computation Γ i j U0 E0 U+ E+ M b s A B c) h =
    let (vΓ , TU0) = h fzero
        (_ , TE0) = h (1 ↑ʳ fzero)
        (_ , TU+) = h (2 ↑ʳ fzero)
        (_ , TE+) = h (3 ↑ʳ fzero)
        (_ , TM) = h (4 ↑ʳ fzero)
        (_ , Tb) = h (5 ↑ʳ fzero)
        (_ , Ts) = h (6 ↑ʳ fzero)
        (_ , TA) = h (7 ↑ʳ fzero)
        (_ , TB) = h (8 ↑ʳ fzero)
        (_ , Tc) = h (9 ↑ʳ fzero)
        X = object Γ
        env = values Γ
        𝒫 : Typed-Parameters i U0 E0 U+ E+ X env
        𝒫 = typed-parameters TU0 TE0 TU+ TE+
        ℳ : Typed-Methods i j U0 E0 U+ E+ M b s X env
        ℳ = typed-methods TM Tb Ts
        𝒜 : Typed-Arguments i U0 E0 U+ E+ A B c X env
        𝒜 = typed-arguments TA TB Tc
        S = stable-parameters i U0 E0 U+ E+ X env 𝒫
        P = parameters-at i U0 E0 U+ E+ X env 𝒫
        v = Formers.closure i U0 E0 U+ E+ A B c
        TL = induction-typed i j U0 E0 U+ E+ M b s v X env S P ℳ
               (closure-typed i U0 E0 U+ E+ A B c X env S P 𝒜)
        e = closure-computation-value i j U0 E0 U+ E+ M b s A B c X env 𝒫 ℳ
              𝒜
    in vΓ
       , TL
       , equal-typed X env j
           (Formers.subuniverse-induction i j U0 E0 U+ E+ M b s v)
           (Types.induction-closure i j U0 E0 U+ E+ M b s A B c)
           (Types.motive-at i j U0 E0 U+ E+ M v) TL
           (λ Y τ →
              closure-computation-value i j U0 E0 U+ E+ M b s A B c Y
                (env [ τ ]ᵉ) (parameters-[] i U0 E0 U+ E+ X env 𝒫 τ)
                (methods-[] i j U0 E0 U+ E+ M b s X env ℳ τ)
                (arguments-[] i U0 E0 U+ E+ A B c X env 𝒜 τ))
           e
       , e
  sound (Block.formation-equal Γ i U0 U0′ E0 E0′ U+ U+′ E+ E+′) h =
    let (vΓ , TU0 , TU0′ , eU0) = h fzero
        (_ , TE0 , TE0′ , eE0) = h (1 ↑ʳ fzero)
        (_ , TU+ , TU+′ , eU+) = h (2 ↑ʳ fzero)
        (_ , TE+ , TE+′ , eE+) = h (3 ↑ʳ fzero)
        X = object Γ
        env = values Γ
        𝒫 : Typed-Parameters i U0 E0 U+ E+ X env
        𝒫 = typed-parameters TU0 TE0 TU+ TE+
        TL = subuniverse-typed i U0 E0 U+ E+ X env
               (stable-parameters i U0 E0 U+ E+ X env 𝒫)
               (parameters-at i U0 E0 U+ E+ X env 𝒫)
    in vΓ
       , TL
       , equal-typed X env (suc i) (Formers.subuniverse i U0 E0 U+ E+)
           (Formers.subuniverse i U0′ E0′ U+′ E+′) (Formers.universe i) TL
           (λ Y τ →
              ap₄ (subuniverse i)
                (equal-[] (meaning U0) (meaning U0′) X env (term-stable TU0)
                  (term-stable TU0′) eU0 τ)
                (equal-[] (meaning E0) (meaning E0′) X env (term-stable TE0)
                  (term-stable TE0′) eE0 τ)
                (equal-[] (meaning U+) (meaning U+′) X env (term-stable TU+)
                  (term-stable TU+′) eU+ τ)
                (equal-[] (meaning E+) (meaning E+′) X env (term-stable TE+)
                  (term-stable TE+′) eE+ τ))
           (ap₄ (subuniverse i) eU0 eE0 eU+ eE+)
       , ap₄ (subuniverse i) eU0 eE0 eU+ eE+
  sound (Block.inclusion-equal Γ i U0 U0′ E0 E0′ U+ U+′ E+ E+′ u u′) h =
    let (vΓ , TU0 , TU0′ , eU0) = h fzero
        (_ , TE0 , TE0′ , eE0) = h (1 ↑ʳ fzero)
        (_ , TU+ , TU+′ , eU+) = h (2 ↑ʳ fzero)
        (_ , TE+ , TE+′ , eE+) = h (3 ↑ʳ fzero)
        (_ , Tu , Tu′ , eu) = h (4 ↑ʳ fzero)
        X = object Γ
        env = values Γ
        𝒫 : Typed-Parameters i U0 E0 U+ E+ X env
        𝒫 = typed-parameters TU0 TE0 TU+ TE+
        TL = inclusion-typed i U0 E0 U+ E+ u X env
               (stable-parameters i U0 E0 U+ E+ X env 𝒫)
               (parameters-at i U0 E0 U+ E+ X env 𝒫) Tu
    in vΓ
       , TL
       , equal-typed X env i (Formers.inclusion i U0 E0 U+ E+ u)
           (Formers.inclusion i U0′ E0′ U+′ E+′ u′)
           (Formers.subuniverse i U0 E0 U+ E+) TL
           (λ Y τ →
              ap₅ (inclusion i)
                (equal-[] (meaning U0) (meaning U0′) X env (term-stable TU0)
                  (term-stable TU0′) eU0 τ)
                (equal-[] (meaning E0) (meaning E0′) X env (term-stable TE0)
                  (term-stable TE0′) eE0 τ)
                (equal-[] (meaning U+) (meaning U+′) X env (term-stable TU+)
                  (term-stable TU+′) eU+ τ)
                (equal-[] (meaning E+) (meaning E+′) X env (term-stable TE+)
                  (term-stable TE+′) eE+ τ)
                (equal-[] (meaning u) (meaning u′) X env (term-stable Tu)
                  (term-stable Tu′) eu τ))
           (ap₅ (inclusion i) eU0 eE0 eU+ eE+ eu)
       , ap₅ (inclusion i) eU0 eE0 eU+ eE+ eu
  sound
    (Block.closure-equal Γ i U0 U0′ E0 E0′ U+ U+′ E+ E+′ A A′ B B′ c c′) h =
    let (vΓ , TU0 , TU0′ , eU0) = h fzero
        (_ , TE0 , TE0′ , eE0) = h (1 ↑ʳ fzero)
        (_ , TU+ , TU+′ , eU+) = h (2 ↑ʳ fzero)
        (_ , TE+ , TE+′ , eE+) = h (3 ↑ʳ fzero)
        (_ , TA , TA′ , eA) = h (4 ↑ʳ fzero)
        (_ , TB , TB′ , eB) = h (5 ↑ʳ fzero)
        (_ , Tc , Tc′ , ec) = h (6 ↑ʳ fzero)
        X = object Γ
        env = values Γ
        𝒫 : Typed-Parameters i U0 E0 U+ E+ X env
        𝒫 = typed-parameters TU0 TE0 TU+ TE+
        TL = closure-typed i U0 E0 U+ E+ A B c X env
               (stable-parameters i U0 E0 U+ E+ X env 𝒫)
               (parameters-at i U0 E0 U+ E+ X env 𝒫)
               (typed-arguments TA TB Tc)
    in vΓ
       , TL
       , equal-typed X env i (Formers.closure i U0 E0 U+ E+ A B c)
           (Formers.closure i U0′ E0′ U+′ E+′ A′ B′ c′)
           (Formers.subuniverse i U0 E0 U+ E+) TL
           (λ Y τ →
              ap₇ (closure i)
                (equal-[] (meaning U0) (meaning U0′) X env (term-stable TU0)
                  (term-stable TU0′) eU0 τ)
                (equal-[] (meaning E0) (meaning E0′) X env (term-stable TE0)
                  (term-stable TE0′) eE0 τ)
                (equal-[] (meaning U+) (meaning U+′) X env (term-stable TU+)
                  (term-stable TU+′) eU+ τ)
                (equal-[] (meaning E+) (meaning E+′) X env (term-stable TE+)
                  (term-stable TE+′) eE+ τ)
                (equal-[] (meaning A) (meaning A′) X env (term-stable TA)
                  (term-stable TA′) eA τ)
                (equal-[] (meaning B) (meaning B′) X env (term-stable TB)
                  (term-stable TB′) eB τ)
                (equal-[] (meaning c) (meaning c′) X env (term-stable Tc)
                  (term-stable Tc′) ec τ))
           (ap₇ (closure i) eU0 eE0 eU+ eE+ eA eB ec)
       , ap₇ (closure i) eU0 eE0 eU+ eE+ eA eB ec
  sound (Block.decoding-equal Γ i U0 U0′ E0 E0′ U+ U+′ E+ E+′ a a′) h =
    let (vΓ , TU0 , TU0′ , eU0) = h fzero
        (_ , TE0 , TE0′ , eE0) = h (1 ↑ʳ fzero)
        (_ , TU+ , TU+′ , eU+) = h (2 ↑ʳ fzero)
        (_ , TE+ , TE+′ , eE+) = h (3 ↑ʳ fzero)
        (_ , Ta , Ta′ , ea) = h (4 ↑ʳ fzero)
        X = object Γ
        env = values Γ
        𝒫 : Typed-Parameters i U0 E0 U+ E+ X env
        𝒫 = typed-parameters TU0 TE0 TU+ TE+
        TL = decoding-typed i U0 E0 U+ E+ a X env
               (stable-parameters i U0 E0 U+ E+ X env 𝒫)
               (parameters-at i U0 E0 U+ E+ X env 𝒫) Ta
    in vΓ
       , TL
       , equal-typed X env (suc i) (Formers.decoding i U0 E0 U+ E+ a)
           (Formers.decoding i U0′ E0′ U+′ E+′ a′) (Formers.universe i) TL
           (λ Y τ →
              ap₅ (decoding i)
                (equal-[] (meaning U0) (meaning U0′) X env (term-stable TU0)
                  (term-stable TU0′) eU0 τ)
                (equal-[] (meaning E0) (meaning E0′) X env (term-stable TE0)
                  (term-stable TE0′) eE0 τ)
                (equal-[] (meaning U+) (meaning U+′) X env (term-stable TU+)
                  (term-stable TU+′) eU+ τ)
                (equal-[] (meaning E+) (meaning E+′) X env (term-stable TE+)
                  (term-stable TE+′) eE+ τ)
                (equal-[] (meaning a) (meaning a′) X env (term-stable Ta)
                  (term-stable Ta′) ea τ))
           (ap₅ (decoding i) eU0 eE0 eU+ eE+ ea)
       , ap₅ (decoding i) eU0 eE0 eU+ eE+ ea
  sound
    (Block.elimination-equal Γ i j U0 U0′ E0 E0′ U+ U+′ E+ E+′ M M′ b b′ s s′
      a a′)
    h =
    let (vΓ , TU0 , TU0′ , eU0) = h fzero
        (_ , TE0 , TE0′ , eE0) = h (1 ↑ʳ fzero)
        (_ , TU+ , TU+′ , eU+) = h (2 ↑ʳ fzero)
        (_ , TE+ , TE+′ , eE+) = h (3 ↑ʳ fzero)
        (_ , TM , TM′ , eM) = h (4 ↑ʳ fzero)
        (_ , Tb , Tb′ , eb) = h (5 ↑ʳ fzero)
        (_ , Ts , Ts′ , es) = h (6 ↑ʳ fzero)
        (_ , Ta , Ta′ , ea) = h (7 ↑ʳ fzero)
        X = object Γ
        env = values Γ
        𝒫 : Typed-Parameters i U0 E0 U+ E+ X env
        𝒫 = typed-parameters TU0 TE0 TU+ TE+
        TL = induction-typed i j U0 E0 U+ E+ M b s a X env
               (stable-parameters i U0 E0 U+ E+ X env 𝒫)
               (parameters-at i U0 E0 U+ E+ X env 𝒫) (typed-methods TM Tb Ts)
               Ta
    in vΓ
       , TL
       , equal-typed X env j
           (Formers.subuniverse-induction i j U0 E0 U+ E+ M b s a)
           (Formers.subuniverse-induction i j U0′ E0′ U+′ E+′ M′ b′ s′ a′)
           (Types.motive-at i j U0 E0 U+ E+ M a) TL
           (λ Y τ →
              ap₈ (induction i j)
                (equal-[] (meaning U0) (meaning U0′) X env (term-stable TU0)
                  (term-stable TU0′) eU0 τ)
                (equal-[] (meaning E0) (meaning E0′) X env (term-stable TE0)
                  (term-stable TE0′) eE0 τ)
                (equal-[] (meaning U+) (meaning U+′) X env (term-stable TU+)
                  (term-stable TU+′) eU+ τ)
                (equal-[] (meaning E+) (meaning E+′) X env (term-stable TE+)
                  (term-stable TE+′) eE+ τ)
                (equal-[] (meaning M) (meaning M′) X env (term-stable TM)
                  (term-stable TM′) eM τ)
                (equal-[] (meaning b) (meaning b′) X env (term-stable Tb)
                  (term-stable Tb′) eb τ)
                (equal-[] (meaning s) (meaning s′) X env (term-stable Ts)
                  (term-stable Ts′) es τ)
                (equal-[] (meaning a) (meaning a′) X env (term-stable Ta)
                  (term-stable Ta′) ea τ))
           (ap₈ (induction i j) eU0 eE0 eU+ eE+ eM eb es ea)
       , ap₈ (induction i j) eU0 eE0 eU+ eE+ eM eb es ea
