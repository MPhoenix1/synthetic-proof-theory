{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Skeleton where

-- Expressions of the core theory compared by their skeletons. The skeleton
-- of a tree is first order: a variable's number, or a former with the
-- skeletons of its children in the order of its premises (`Skeleton`,
-- `children`, `skeleton`). Trees with equal skeletons are extensionally
-- equal, as TreeRel _＝_ (`related`): equal skeletons have equal
-- formers and equal children at each premise (`node-injective`, `child`).
--
-- On a tree built from formers and variables, renaming, moving under
-- binders and substitution compute even when the outer scope, the
-- variables' numbers and the levels are abstract, and so does its
-- skeleton. Two such trees that differ only in how their children are
-- formed, such as a weakened or substituted expression and its literal
-- form, are related by `related s t refl`.

open import SPT.Base
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Signature.Sum as Sig
import SPT.Foundation.Tree as Tree
import SPT.Foundation.Tree.Relation as Relation
import SPT.Foundation.Tree.Binding as Binding
import SPT.MartinLof.Raw as Raw

------------------------------------------------------------------------
-- Skeletons

data Skeleton (C : Set) : Set where
  var : ℕ → Skeleton C
  node : Raw.Former C → List (Skeleton C) → Skeleton C

-- The children of a node in the order of its former's premises.
children :
  {C : Set} (o : Raw.Former C) → (Raw.Premise o → Skeleton C)
  → List (Skeleton C)
children (Raw.universe l) s = []
children (Raw.lifted m k) s = s Raw.lifted-type ∷ []
children (Raw.lift m k) s = s Raw.lift-type ∷ s Raw.lift-term ∷ []
children (Raw.lower m k) s = s Raw.lower-type ∷ s Raw.lower-term ∷ []
children (Raw.pi m k) s = s Raw.pi-domain ∷ s Raw.pi-codomain ∷ []
children (Raw.lambda m k) s =
  s Raw.lambda-domain ∷ s Raw.lambda-codomain ∷ s Raw.lambda-body ∷ []
children (Raw.application m k) s =
  s Raw.application-domain ∷ s Raw.application-codomain
  ∷ s Raw.application-function ∷ s Raw.application-argument ∷ []
children (Raw.sigma m k) s = s Raw.sigma-first ∷ s Raw.sigma-second ∷ []
children (Raw.pair m k) s =
  s Raw.pair-first-type ∷ s Raw.pair-second-type ∷ s Raw.pair-first
  ∷ s Raw.pair-second ∷ []
children (Raw.first m k) s =
  s Raw.first-first-type ∷ s Raw.first-second-type ∷ s Raw.first-pair ∷ []
children (Raw.second m k) s =
  s Raw.second-first-type ∷ s Raw.second-second-type ∷ s Raw.second-pair
  ∷ []
children (Raw.identity m) s =
  s Raw.identity-type ∷ s Raw.identity-left ∷ s Raw.identity-right ∷ []
children (Raw.reflexivity m) s =
  s Raw.reflexivity-type ∷ s Raw.reflexivity-point ∷ []
children (Raw.path-induction m k) s =
  s Raw.induction-type ∷ s Raw.induction-motive ∷ s Raw.induction-base
  ∷ s Raw.induction-method ∷ s Raw.induction-end ∷ s Raw.induction-path
  ∷ []
children (Raw.tree m k) s = s Raw.tree-shape ∷ s Raw.tree-position ∷ []
children (Raw.supremum m k) s =
  s Raw.supremum-shape-type ∷ s Raw.supremum-position-type
  ∷ s Raw.supremum-shape ∷ s Raw.supremum-children ∷ []
children (Raw.tree-induction m k l) s =
  s Raw.recursion-shape-type ∷ s Raw.recursion-position-type
  ∷ s Raw.recursion-motive ∷ s Raw.recursion-method ∷ s Raw.recursion-tree
  ∷ []
children Raw.empty s = []
children (Raw.absurd k) s = s Raw.absurd-motive ∷ s Raw.absurd-term ∷ []
children Raw.unit s = []
children Raw.star s = []
children (Raw.sum m k) s = s Raw.sum-left ∷ s Raw.sum-right ∷ []
children (Raw.left m k) s =
  s Raw.left-left-type ∷ s Raw.left-right-type ∷ s Raw.left-term ∷ []
children (Raw.right m k) s =
  s Raw.right-left-type ∷ s Raw.right-right-type ∷ s Raw.right-term ∷ []
children (Raw.case m k l) s =
  s Raw.case-left-type ∷ s Raw.case-right-type ∷ s Raw.case-motive
  ∷ s Raw.case-left-method ∷ s Raw.case-right-method ∷ s Raw.case-term
  ∷ []
children Raw.natural s = []
children Raw.zero s = []
children Raw.successor s = s Raw.successor-term ∷ []
children (Raw.natural-induction l) s =
  s Raw.natural-motive ∷ s Raw.natural-base ∷ s Raw.natural-step
  ∷ s Raw.natural-term ∷ []
children (Raw.subuniverse i) s =
  s Raw.subuniverse-base ∷ s Raw.subuniverse-base-decoding ∷
  s Raw.subuniverse-step ∷ s Raw.subuniverse-step-decoding ∷ []
children (Raw.inclusion i) s =
  s Raw.inclusion-base ∷ s Raw.inclusion-base-decoding ∷
  s Raw.inclusion-step ∷ s Raw.inclusion-step-decoding ∷
  s Raw.inclusion-point ∷ []
children (Raw.closure i) s =
  s Raw.closure-base ∷ s Raw.closure-base-decoding ∷ s Raw.closure-step ∷
  s Raw.closure-step-decoding ∷ s Raw.closure-code ∷ s Raw.closure-family ∷
  s Raw.closure-point ∷ []
children (Raw.decoding i) s =
  s Raw.decoding-base ∷ s Raw.decoding-base-decoding ∷ s Raw.decoding-step ∷
  s Raw.decoding-step-decoding ∷ s Raw.decoding-code ∷ []
children (Raw.subuniverse-induction i j) s =
  s Raw.subinduction-base ∷ s Raw.subinduction-base-decoding ∷
  s Raw.subinduction-step ∷ s Raw.subinduction-step-decoding ∷
  s Raw.subinduction-motive ∷ s Raw.subinduction-inclusion ∷
  s Raw.subinduction-closure ∷ s Raw.subinduction-code ∷ []
children (Raw.constant c) s = []

-- The skeleton of a tree at depth d in scope n.
skeleton :
  {C : Set} {n d : ℕ}
  → Tree.Tree (Sig.to-signature (Binding.over (Raw.binding C)))
      (Binding.Variable n) d
  → Skeleton C
skeleton (Tree.hole i) = var (to-ℕ i)
skeleton (Tree.node o ch) = node o (children o (λ p → skeleton (ch p)))

------------------------------------------------------------------------
-- Equal skeletons, equal trees

node-injective :
  {C : Set} {o o′ : Raw.Former C} {xs xs′ : List (Skeleton C)}
  → node o xs ＝ node o′ xs′ → (o ＝ o′) × (xs ＝ xs′)
node-injective refl = refl , refl

var-injective : {C : Set} {a b : ℕ} → var {C} a ＝ var b → a ＝ b
var-injective refl = refl

-- Equal lists of children have equal children at each premise.
child :
  {C : Set} (o : Raw.Former C) (s s′ : Raw.Premise o → Skeleton C)
  → children o s ＝ children o s′ → (p : Raw.Premise o) → s p ＝ s′ p
child (Raw.universe l) s s′ e ()
child (Raw.lifted m k) s s′ e Raw.lifted-type = ∷-injective-head e
child (Raw.lift m k) s s′ e Raw.lift-type = ∷-injective-head e
child (Raw.lift m k) s s′ e Raw.lift-term =
  ∷-injective-head (∷-injective-tail e)
child (Raw.lower m k) s s′ e Raw.lower-type = ∷-injective-head e
child (Raw.lower m k) s s′ e Raw.lower-term =
  ∷-injective-head (∷-injective-tail e)
child (Raw.pi m k) s s′ e Raw.pi-domain = ∷-injective-head e
child (Raw.pi m k) s s′ e Raw.pi-codomain =
  ∷-injective-head (∷-injective-tail e)
child (Raw.lambda m k) s s′ e Raw.lambda-domain = ∷-injective-head e
child (Raw.lambda m k) s s′ e Raw.lambda-codomain =
  ∷-injective-head (∷-injective-tail e)
child (Raw.lambda m k) s s′ e Raw.lambda-body =
  ∷-injective-head (∷-injective-tail (∷-injective-tail e))
child (Raw.application m k) s s′ e Raw.application-domain = ∷-injective-head e
child (Raw.application m k) s s′ e Raw.application-codomain =
  ∷-injective-head (∷-injective-tail e)
child (Raw.application m k) s s′ e Raw.application-function =
  ∷-injective-head (∷-injective-tail (∷-injective-tail e))
child (Raw.application m k) s s′ e Raw.application-argument =
  ∷-injective-head (∷-injective-tail (∷-injective-tail (∷-injective-tail e)))
child (Raw.sigma m k) s s′ e Raw.sigma-first = ∷-injective-head e
child (Raw.sigma m k) s s′ e Raw.sigma-second =
  ∷-injective-head (∷-injective-tail e)
child (Raw.pair m k) s s′ e Raw.pair-first-type = ∷-injective-head e
child (Raw.pair m k) s s′ e Raw.pair-second-type =
  ∷-injective-head (∷-injective-tail e)
child (Raw.pair m k) s s′ e Raw.pair-first =
  ∷-injective-head (∷-injective-tail (∷-injective-tail e))
child (Raw.pair m k) s s′ e Raw.pair-second =
  ∷-injective-head (∷-injective-tail (∷-injective-tail (∷-injective-tail e)))
child (Raw.first m k) s s′ e Raw.first-first-type = ∷-injective-head e
child (Raw.first m k) s s′ e Raw.first-second-type =
  ∷-injective-head (∷-injective-tail e)
child (Raw.first m k) s s′ e Raw.first-pair =
  ∷-injective-head (∷-injective-tail (∷-injective-tail e))
child (Raw.second m k) s s′ e Raw.second-first-type = ∷-injective-head e
child (Raw.second m k) s s′ e Raw.second-second-type =
  ∷-injective-head (∷-injective-tail e)
child (Raw.second m k) s s′ e Raw.second-pair =
  ∷-injective-head (∷-injective-tail (∷-injective-tail e))
child (Raw.identity m) s s′ e Raw.identity-type = ∷-injective-head e
child (Raw.identity m) s s′ e Raw.identity-left =
  ∷-injective-head (∷-injective-tail e)
child (Raw.identity m) s s′ e Raw.identity-right =
  ∷-injective-head (∷-injective-tail (∷-injective-tail e))
child (Raw.reflexivity m) s s′ e Raw.reflexivity-type = ∷-injective-head e
child (Raw.reflexivity m) s s′ e Raw.reflexivity-point =
  ∷-injective-head (∷-injective-tail e)
child (Raw.path-induction m k) s s′ e Raw.induction-type = ∷-injective-head e
child (Raw.path-induction m k) s s′ e Raw.induction-motive =
  ∷-injective-head (∷-injective-tail e)
child (Raw.path-induction m k) s s′ e Raw.induction-base =
  ∷-injective-head (∷-injective-tail (∷-injective-tail e))
child (Raw.path-induction m k) s s′ e Raw.induction-method =
  ∷-injective-head (∷-injective-tail (∷-injective-tail (∷-injective-tail e)))
child (Raw.path-induction m k) s s′ e Raw.induction-end =
  ∷-injective-head
    (∷-injective-tail
      (∷-injective-tail (∷-injective-tail (∷-injective-tail e))))
child (Raw.path-induction m k) s s′ e Raw.induction-path =
  ∷-injective-head
    (∷-injective-tail (∷-injective-tail (∷-injective-tail (∷-injective-tail
      (∷-injective-tail e)))))
child (Raw.tree m k) s s′ e Raw.tree-shape = ∷-injective-head e
child (Raw.tree m k) s s′ e Raw.tree-position =
  ∷-injective-head (∷-injective-tail e)
child (Raw.supremum m k) s s′ e Raw.supremum-shape-type = ∷-injective-head e
child (Raw.supremum m k) s s′ e Raw.supremum-position-type =
  ∷-injective-head (∷-injective-tail e)
child (Raw.supremum m k) s s′ e Raw.supremum-shape =
  ∷-injective-head (∷-injective-tail (∷-injective-tail e))
child (Raw.supremum m k) s s′ e Raw.supremum-children =
  ∷-injective-head (∷-injective-tail (∷-injective-tail (∷-injective-tail e)))
child (Raw.tree-induction m k l) s s′ e Raw.recursion-shape-type =
  ∷-injective-head e
child (Raw.tree-induction m k l) s s′ e Raw.recursion-position-type =
  ∷-injective-head (∷-injective-tail e)
child (Raw.tree-induction m k l) s s′ e Raw.recursion-motive =
  ∷-injective-head (∷-injective-tail (∷-injective-tail e))
child (Raw.tree-induction m k l) s s′ e Raw.recursion-method =
  ∷-injective-head (∷-injective-tail (∷-injective-tail (∷-injective-tail e)))
child (Raw.tree-induction m k l) s s′ e Raw.recursion-tree =
  ∷-injective-head
    (∷-injective-tail
      (∷-injective-tail (∷-injective-tail (∷-injective-tail e))))
child Raw.empty s s′ e ()
child (Raw.absurd k) s s′ e Raw.absurd-motive = ∷-injective-head e
child (Raw.absurd k) s s′ e Raw.absurd-term =
  ∷-injective-head (∷-injective-tail e)
child Raw.unit s s′ e ()
child Raw.star s s′ e ()
child (Raw.sum m k) s s′ e Raw.sum-left = ∷-injective-head e
child (Raw.sum m k) s s′ e Raw.sum-right = ∷-injective-head (∷-injective-tail e)
child (Raw.left m k) s s′ e Raw.left-left-type = ∷-injective-head e
child (Raw.left m k) s s′ e Raw.left-right-type =
  ∷-injective-head (∷-injective-tail e)
child (Raw.left m k) s s′ e Raw.left-term =
  ∷-injective-head (∷-injective-tail (∷-injective-tail e))
child (Raw.right m k) s s′ e Raw.right-left-type = ∷-injective-head e
child (Raw.right m k) s s′ e Raw.right-right-type =
  ∷-injective-head (∷-injective-tail e)
child (Raw.right m k) s s′ e Raw.right-term =
  ∷-injective-head (∷-injective-tail (∷-injective-tail e))
child (Raw.case m k l) s s′ e Raw.case-left-type = ∷-injective-head e
child (Raw.case m k l) s s′ e Raw.case-right-type =
  ∷-injective-head (∷-injective-tail e)
child (Raw.case m k l) s s′ e Raw.case-motive =
  ∷-injective-head (∷-injective-tail (∷-injective-tail e))
child (Raw.case m k l) s s′ e Raw.case-left-method =
  ∷-injective-head (∷-injective-tail (∷-injective-tail (∷-injective-tail e)))
child (Raw.case m k l) s s′ e Raw.case-right-method =
  ∷-injective-head
    (∷-injective-tail
      (∷-injective-tail (∷-injective-tail (∷-injective-tail e))))
child (Raw.case m k l) s s′ e Raw.case-term =
  ∷-injective-head
    (∷-injective-tail (∷-injective-tail (∷-injective-tail (∷-injective-tail
      (∷-injective-tail e)))))
child Raw.natural s s′ e ()
child Raw.zero s s′ e ()
child Raw.successor s s′ e Raw.successor-term = ∷-injective-head e
child (Raw.natural-induction l) s s′ e Raw.natural-motive = ∷-injective-head e
child (Raw.natural-induction l) s s′ e Raw.natural-base =
  ∷-injective-head (∷-injective-tail e)
child (Raw.natural-induction l) s s′ e Raw.natural-step =
  ∷-injective-head (∷-injective-tail (∷-injective-tail e))
child (Raw.natural-induction l) s s′ e Raw.natural-term =
  ∷-injective-head (∷-injective-tail (∷-injective-tail (∷-injective-tail e)))
child (Raw.subuniverse i) s s′ e Raw.subuniverse-base =
  ∷-injective-head e
child (Raw.subuniverse i) s s′ e Raw.subuniverse-base-decoding =
  ∷-injective-head (∷-injective-tail e)
child (Raw.subuniverse i) s s′ e Raw.subuniverse-step =
  ∷-injective-head (∷-injective-tail (∷-injective-tail e))
child (Raw.subuniverse i) s s′ e Raw.subuniverse-step-decoding =
  ∷-injective-head (∷-injective-tail (∷-injective-tail (∷-injective-tail e)))
child (Raw.inclusion i) s s′ e Raw.inclusion-base =
  ∷-injective-head e
child (Raw.inclusion i) s s′ e Raw.inclusion-base-decoding =
  ∷-injective-head (∷-injective-tail e)
child (Raw.inclusion i) s s′ e Raw.inclusion-step =
  ∷-injective-head (∷-injective-tail (∷-injective-tail e))
child (Raw.inclusion i) s s′ e Raw.inclusion-step-decoding =
  ∷-injective-head (∷-injective-tail (∷-injective-tail (∷-injective-tail e)))
child (Raw.inclusion i) s s′ e Raw.inclusion-point =
  ∷-injective-head
    (∷-injective-tail
      (∷-injective-tail (∷-injective-tail (∷-injective-tail e))))
child (Raw.closure i) s s′ e Raw.closure-base =
  ∷-injective-head e
child (Raw.closure i) s s′ e Raw.closure-base-decoding =
  ∷-injective-head (∷-injective-tail e)
child (Raw.closure i) s s′ e Raw.closure-step =
  ∷-injective-head (∷-injective-tail (∷-injective-tail e))
child (Raw.closure i) s s′ e Raw.closure-step-decoding =
  ∷-injective-head (∷-injective-tail (∷-injective-tail (∷-injective-tail e)))
child (Raw.closure i) s s′ e Raw.closure-code =
  ∷-injective-head
    (∷-injective-tail
      (∷-injective-tail (∷-injective-tail (∷-injective-tail e))))
child (Raw.closure i) s s′ e Raw.closure-family =
  ∷-injective-head
    (∷-injective-tail (∷-injective-tail (∷-injective-tail (∷-injective-tail
      (∷-injective-tail e)))))
child (Raw.closure i) s s′ e Raw.closure-point =
  ∷-injective-head
    (∷-injective-tail (∷-injective-tail (∷-injective-tail (∷-injective-tail
      (∷-injective-tail (∷-injective-tail e))))))
child (Raw.decoding i) s s′ e Raw.decoding-base =
  ∷-injective-head e
child (Raw.decoding i) s s′ e Raw.decoding-base-decoding =
  ∷-injective-head (∷-injective-tail e)
child (Raw.decoding i) s s′ e Raw.decoding-step =
  ∷-injective-head (∷-injective-tail (∷-injective-tail e))
child (Raw.decoding i) s s′ e Raw.decoding-step-decoding =
  ∷-injective-head (∷-injective-tail (∷-injective-tail (∷-injective-tail e)))
child (Raw.decoding i) s s′ e Raw.decoding-code =
  ∷-injective-head
    (∷-injective-tail
      (∷-injective-tail (∷-injective-tail (∷-injective-tail e))))
child (Raw.subuniverse-induction i j) s s′ e Raw.subinduction-base =
  ∷-injective-head e
child (Raw.subuniverse-induction i j) s s′ e Raw.subinduction-base-decoding =
  ∷-injective-head (∷-injective-tail e)
child (Raw.subuniverse-induction i j) s s′ e Raw.subinduction-step =
  ∷-injective-head (∷-injective-tail (∷-injective-tail e))
child (Raw.subuniverse-induction i j) s s′ e Raw.subinduction-step-decoding =
  ∷-injective-head (∷-injective-tail (∷-injective-tail (∷-injective-tail e)))
child (Raw.subuniverse-induction i j) s s′ e Raw.subinduction-motive =
  ∷-injective-head
    (∷-injective-tail
      (∷-injective-tail (∷-injective-tail (∷-injective-tail e))))
child (Raw.subuniverse-induction i j) s s′ e Raw.subinduction-inclusion =
  ∷-injective-head
    (∷-injective-tail (∷-injective-tail (∷-injective-tail (∷-injective-tail
      (∷-injective-tail e)))))
child (Raw.subuniverse-induction i j) s s′ e Raw.subinduction-closure =
  ∷-injective-head
    (∷-injective-tail (∷-injective-tail (∷-injective-tail (∷-injective-tail
      (∷-injective-tail (∷-injective-tail e))))))
child (Raw.subuniverse-induction i j) s s′ e Raw.subinduction-code =
  ∷-injective-head
    (∷-injective-tail (∷-injective-tail (∷-injective-tail (∷-injective-tail
      (∷-injective-tail (∷-injective-tail (∷-injective-tail e)))))))
child (Raw.constant c) s s′ e ()

-- Trees with equal skeletons are extensionally equal.
related :
  {C : Set} {n d : ℕ}
  (s t : Tree.Tree (Sig.to-signature (Binding.over (Raw.binding C)))
           (Binding.Variable n) d)
  → skeleton s ＝ skeleton t → Relation.TreeRel _＝_ s t
related (Tree.hole i) (Tree.hole j) e =
  Relation.hole-rel (to-ℕ-is-injective (var-injective e))
related (Tree.hole i) (Tree.node o ch) ()
related (Tree.node o ch) (Tree.hole j) ()
related (Tree.node o ch) (Tree.node o′ ch′) e with node-injective e
... | refl , es =
  Relation.node-rel
    (λ p → related (ch p) (ch′ p)
             (child o (λ q → skeleton (ch q)) (λ q → skeleton (ch′ q)) es p))
