{-# OPTIONS --safe --without-K --no-projection-like #-}

module SPT.MartinLof.Soundness.Interpretation where

-- The interpretation of the core theory in a model, and what it is for a
-- judgment to hold there.
--
-- A raw expression at depth d in scope n has a value at every model
-- context X and environment of d + n terms over X (`⟦_⟧`). A variable is
-- looked up. A node applies the model's operation for its former to the
-- values of its children (`node`): a child binding k variables is
-- evaluated at the extension of X by the types its former gives them,
-- with the environment extended (`ext`). The operations are total, so
-- every raw expression has a value, typed or not. The value is the fold
-- of these actions (`algebra`, Foundation.Tree.Fold).
--
-- A raw context has a model context and the values of its variables
-- (`object`, `values`). A judgment holds when its context is valid
-- (`valid-context`) and its expressions have their types with stable
-- values (`Typed`, `Valid`).
--
-- Every section here and in the other Soundness modules takes the base
-- and the structures of a model, and the values of its constants, as
-- variables.

open import SPT.Base hiding (Lift; _∘_; id; lift; lower; zero)
import SPT.Base.Universes as Universes
import SPT.Foundation.Signature.Sum as Sig
import SPT.Foundation.Tree.Fold as Fold
import SPT.Foundation.Tree.Binding as Binding
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Judgment using
  (Context; ∅; _▸[_]_; Judgment; context; term; term-equal)
open import SPT.MartinLof.Model.Empty using (Empty)
open import SPT.MartinLof.Model.Identity using (Identity)
open import SPT.MartinLof.Model.Lift using (Lift)
open import SPT.MartinLof.Model.Natural using (Natural)
open import SPT.MartinLof.Model.Subuniverse using
  (Operations; Subuniverse)
open import SPT.MartinLof.Model.Pi using (Pi)
open import SPT.MartinLof.Model.Russell using (Russell; Code)
open import SPT.MartinLof.Model.Sigma using (Sigma)
open import SPT.MartinLof.Model.Sum using (Sum)
open import SPT.MartinLof.Model.Unit using (Unit)
open import SPT.MartinLof.Model.WellFounded using
  (WellFounded; children-type; hypotheses-type)
import SPT.MartinLof.Soundness.Environment as Environment
import SPT.Foundation.Tree as Tree

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
  (let Stable = Environment.Stable R)
  where

  ----------------------------------------------------------------------
  -- Values of raw expressions

  -- The value of a node of former o at depth d in scope n, from the values
  -- of its children.
  node :
    (n d : ℕ) (o : Raw.Former C)
    → ((p : Raw.Premise o) (X : Ob) → Vec (Tm X) ((Raw.depth o p + d) + n)
       → Tm X)
    → (X : Ob) → Vec (Tm X) (d + n) → Tm X
  node n d (Raw.universe l) v X env = universe l [ ε X ]
  node n d (Raw.lifted m k) v X env = lifted m k (v Raw.lifted-type X env)
  node n d (Raw.lift m k) v X env =
    lift m k (v Raw.lift-type X env) (v Raw.lift-term X env)
  node n d (Raw.lower m k) v X env =
    lower m k (v Raw.lower-type X env) (v Raw.lower-term X env)
  node n d (Raw.pi m k) v X env =
    let a = v Raw.pi-domain X env
    in pi m k a (v Raw.pi-codomain (X ▸ a) (ext a env))
  node n d (Raw.lambda m k) v X env =
    let a = v Raw.lambda-domain X env
    in lambda m k a (v Raw.lambda-codomain (X ▸ a) (ext a env))
         (v Raw.lambda-body (X ▸ a) (ext a env))
  node n d (Raw.application m k) v X env =
    let a = v Raw.application-domain X env
    in application m k a (v Raw.application-codomain (X ▸ a) (ext a env))
         (v Raw.application-function X env)
         (v Raw.application-argument X env)
  node n d (Raw.sigma m k) v X env =
    let a = v Raw.sigma-first X env
    in sigma m k a (v Raw.sigma-second (X ▸ a) (ext a env))
  node n d (Raw.pair m k) v X env =
    let a = v Raw.pair-first-type X env
    in pair m k a (v Raw.pair-second-type (X ▸ a) (ext a env))
         (v Raw.pair-first X env) (v Raw.pair-second X env)
  node n d (Raw.first m k) v X env =
    let a = v Raw.first-first-type X env
    in first m k a (v Raw.first-second-type (X ▸ a) (ext a env))
         (v Raw.first-pair X env)
  node n d (Raw.second m k) v X env =
    let a = v Raw.second-first-type X env
    in second m k a (v Raw.second-second-type (X ▸ a) (ext a env))
         (v Raw.second-pair X env)
  node n d (Raw.identity m) v X env =
    identity m (v Raw.identity-type X env) (v Raw.identity-left X env)
      (v Raw.identity-right X env)
  node n d (Raw.reflexivity m) v X env =
    reflexivity m (v Raw.reflexivity-type X env)
      (v Raw.reflexivity-point X env)
  node n d (Raw.path-induction m k) v X env =
    let a = v Raw.induction-type X env
        x = v Raw.induction-base X env
        I = identity m (a [ p ]) (x [ p ]) (q a)
    in path-induction m k a x
         (v Raw.induction-motive (X ▸ a ▸ I) (ext I (ext a env)))
         (v Raw.induction-method X env) (v Raw.induction-end X env)
         (v Raw.induction-path X env)
  node n d (Raw.tree m k) v X env =
    let a = v Raw.tree-shape X env
    in tree m k a (v Raw.tree-position (X ▸ a) (ext a env))
  node n d (Raw.supremum m k) v X env =
    let a = v Raw.supremum-shape-type X env
    in supremum m k a (v Raw.supremum-position-type (X ▸ a) (ext a env))
         (v Raw.supremum-shape X env) (v Raw.supremum-children X env)
  node n d (Raw.tree-induction m k l) v X env =
    let a = v Raw.recursion-shape-type X env
        b = v Raw.recursion-position-type (X ▸ a) (ext a env)
        w = tree m k a b
        M = v Raw.recursion-motive (X ▸ w) (ext w env)
        F = children-type R products m k a b w
        H = hypotheses-type R products m k l a b w M
    in tree-induction m k l a b M
         (v Raw.recursion-method (X ▸ a ▸ F ▸ H) (ext H (ext F (ext a env))))
         [ id ⨾ v Raw.recursion-tree X env ]
  node n d Raw.empty v X env = empty [ ε X ]
  node n d (Raw.absurd k) v X env =
    absurd k
      (v Raw.absurd-motive (X ▸ empty [ ε X ]) (ext (empty [ ε X ]) env))
      (v Raw.absurd-term X env)
  node n d Raw.unit v X env = unit [ ε X ]
  node n d Raw.star v X env = star [ ε X ]
  node n d (Raw.sum m k) v X env =
    sum m k (v Raw.sum-left X env) (v Raw.sum-right X env)
  node n d (Raw.left m k) v X env =
    left m k (v Raw.left-left-type X env) (v Raw.left-right-type X env)
      (v Raw.left-term X env)
  node n d (Raw.right m k) v X env =
    right m k (v Raw.right-left-type X env) (v Raw.right-right-type X env)
      (v Raw.right-term X env)
  node n d (Raw.case m k l) v X env =
    let a = v Raw.case-left-type X env
        b = v Raw.case-right-type X env
        s = sum m k a b
    in case m k l a b (v Raw.case-motive (X ▸ s) (ext s env))
         (v Raw.case-left-method (X ▸ a) (ext a env))
         (v Raw.case-right-method (X ▸ b) (ext b env))
         (v Raw.case-term X env)
  node n d Raw.natural v X env = natural [ ε X ]
  node n d Raw.zero v X env = zero [ ε X ]
  node n d Raw.successor v X env = successor (v Raw.successor-term X env)
  node n d (Raw.natural-induction l) v X env =
    let N = natural [ ε X ]
        M = v Raw.natural-motive (X ▸ N) (ext N env)
    in natural-induction l M (v Raw.natural-base X env)
         (v Raw.natural-step (X ▸ N ▸ M) (ext M (ext N env)))
         (v Raw.natural-term X env)
  node n d (Raw.constant c) v X env = constant c [ ε X ]
  node n d (Raw.subuniverse i) v X env =
    subuniverse i (v Raw.subuniverse-base X env)
      (v Raw.subuniverse-base-decoding X env) (v Raw.subuniverse-step X env)
      (v Raw.subuniverse-step-decoding X env)
  node n d (Raw.inclusion i) v X env =
    inclusion i (v Raw.inclusion-base X env)
      (v Raw.inclusion-base-decoding X env) (v Raw.inclusion-step X env)
      (v Raw.inclusion-step-decoding X env) (v Raw.inclusion-point X env)
  node n d (Raw.closure i) v X env =
    closure i (v Raw.closure-base X env) (v Raw.closure-base-decoding X env)
      (v Raw.closure-step X env) (v Raw.closure-step-decoding X env)
      (v Raw.closure-code X env) (v Raw.closure-family X env)
      (v Raw.closure-point X env)
  node n d (Raw.decoding i) v X env =
    decoding i (v Raw.decoding-base X env)
      (v Raw.decoding-base-decoding X env) (v Raw.decoding-step X env)
      (v Raw.decoding-step-decoding X env) (v Raw.decoding-code X env)
  node n d (Raw.subuniverse-induction i j) v X env =
    induction i j (v Raw.subinduction-base X env)
      (v Raw.subinduction-base-decoding X env)
      (v Raw.subinduction-step X env)
      (v Raw.subinduction-step-decoding X env)
      (v Raw.subinduction-motive X env) (v Raw.subinduction-inclusion X env)
      (v Raw.subinduction-closure X env) (v Raw.subinduction-code X env)

  -- The values as a tree algebra over the expressions in scope n: a
  -- variable is looked up, a node is the value of its former at the values
  -- of its children.
  algebra :
    (n : ℕ)
    → Fold.Algebra (Sig.to-signature (Binding.over (Raw.binding C)))
        (Binding.Variable n)
        (λ d → (X : Ob) → Vec (Tm X) (d + n) → Tm X)
  algebra n = record
    { on-hole = λ x X env → vector-lookup env x
    ; on-node = λ {d} o v → node n d o v
    }

  -- The value of a raw expression: fold of that algebra.
  ⟦_⟧ :
    {n d : ℕ} → Tree.Tree (Sig.to-signature (Binding.over (Raw.binding C)))
      (Binding.Variable n) d
    → (X : Ob) → Vec (Tm X) (d + n) → Tm X
  ⟦_⟧ {n} t = Fold.fold (algebra n) t

  ----------------------------------------------------------------------
  -- Contexts

  -- The model context of a raw context, and the values of its variables.
  object : {n : ℕ} → Context C n → Ob
  values : {n : ℕ} (Γ : Context C n) → Vec (Tm (object Γ)) n

  object ∅ = ◇
  object (Γ ▸[ l ] A) = object Γ ▸ ⟦ A ⟧ (object Γ) (values Γ)

  values ∅ = []
  values (Γ ▸[ l ] A) = ext (⟦ A ⟧ (object Γ) (values Γ)) (values Γ)

  -- Each entry is a stable type at its level.
  valid-context : {n : ℕ} → Context C n → Set ℓ
  valid-context ∅ = Universes.Lift ℓ 𝟙
  valid-context (Γ ▸[ l ] A) =
    valid-context Γ
    × Stable ⟦ A ⟧ (object Γ) (values Γ)
    × Code R l (⟦ A ⟧ (object Γ) (values Γ))

  ----------------------------------------------------------------------
  -- Judgments

  -- t has type A at level l in context X with environment env: A is a
  -- type at level l, t has type A, and both values are stable.
  record Typed
    {n : ℕ} (X : Ob) (env : Vec (Tm X) n) (l : ℕ)
    (t A : Raw.Expression C n) : Set ℓ where
    field
      type-stable : Stable ⟦ A ⟧ X env
      type-code : Code R l (⟦ A ⟧ X env)
      term-stable : Stable ⟦ t ⟧ X env
      term-type : type-of (⟦ t ⟧ X env) ＝ ⟦ A ⟧ X env

  Valid : Judgment C → Set ℓ
  Valid (context Γ) = valid-context Γ
  Valid (term Γ l t A) = valid-context Γ × Typed (object Γ) (values Γ) l t A
  Valid (term-equal Γ l t u A) =
    valid-context Γ
    × Typed (object Γ) (values Γ) l t A
    × Typed (object Γ) (values Γ) l u A
    × (⟦ t ⟧ (object Γ) (values Γ) ＝ ⟦ u ⟧ (object Γ) (values Γ))
