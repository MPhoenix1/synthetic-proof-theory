{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.Generator.Tree.Child where

-- The immediate children of a tree: Child relates the subtree at a
-- position to the node it hangs from.  Child is well founded by induction
-- on trees (child-wf), also on closed trees (history-child-wf), and so is
-- every relation it contains (covered-wf).

open import Agda.Primitive using (Level; lzero; _⊔_)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Product using (Σ; _,_)

open import SPT.Cubical.Core.WellFounded using (Acc; acc; WellFounded)
open import SPT.Cubical.Core.WellFounded.Rank using (WFRel)
open import SPT.Cubical.Core.Generator.Tree public
  using
    ( Signature
    ; Judgment
    ; Op
    ; Pos
    ; boundary
    ; Tree
    ; hole
    ; node
    ; History
    )
open import SPT.Cubical.Core.WellFounded.Rewrite using (reverseRelationRewrite)
open import SPT.Cubical.Core.WellFounded.Subrelation using (subrel-wf)
open import SPT.Cubical.Core.WellFounded.Termination using
  (module Termination)

------------------------------------------------------------------------
-- Nodes and their immediate children

-- Node Σ X = Σ (j : Judgment Σ). Tree Σ X j, a tree with its judgment.
Node :
    ∀ {ℓj ℓo ℓp ℓx}
      (signature : Signature ℓj ℓo ℓp)
      (X : Judgment signature → Set ℓx)
  → Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx)
Node signature X =
  Σ (Judgment signature) (Tree signature X)

-- node-child p : Child (boundary o p , child p) (j , node o child).  A
-- witness selects one position of the operation, so one argument of the
-- node; holes and nullary operations have no children.
data Child
    {ℓj ℓo ℓp ℓx : Level}
    {signature : Signature ℓj ℓo ℓp}
    {X : Judgment signature → Set ℓx}
    : Node signature X
    → Node signature X
    → Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx)
  where
  node-child :
      ∀ {j}
        {operation : Op signature j}
        {child :
          (position : Pos signature operation)
          → Tree signature X
              (boundary signature operation position)}
      (position : Pos signature operation)
    → Child
        (boundary signature operation position , child position)
        (j , node operation child)

------------------------------------------------------------------------
-- Accessibility

-- tree-acc t : Acc Child (j , t), by induction on t: the predecessor
-- exposed by node-child p is accessible by the proof for the child at p.
tree-acc :
    ∀ {ℓj ℓo ℓp ℓx}
      {signature : Signature ℓj ℓo ℓp}
      {X : Judgment signature → Set ℓx}
      {j : Judgment signature}
      (tree : Tree signature X j)
  → Acc Child (j , tree)
tree-acc (hole payload) =
  acc (λ predecessor ())
tree-acc
    {signature = signature}
    {X = X}
    {j = j}
    (node operation child) =
  acc smaller
  where
  smaller :
      (predecessor : Node signature X)
    → Child predecessor (j , node operation child)
    → Acc Child predecessor
  smaller
      .(boundary signature operation position , child position)
      (node-child position) =
    tree-acc (child position)

node-acc :
    ∀ {ℓj ℓo ℓp ℓx}
      {signature : Signature ℓj ℓo ℓp}
      {X : Judgment signature → Set ℓx}
      (tree-node : Node signature X)
  → Acc Child tree-node
node-acc (j , tree) =
  tree-acc tree

child-wf :
    ∀ {ℓj ℓo ℓp ℓx}
      {signature : Signature ℓj ℓo ℓp}
      {X : Judgment signature → Set ℓx}
  → WellFounded (Child {signature = signature} {X = X})
child-wf =
  node-acc

-- child-wfrel = (Node Σ X , Child , child-wf), as a well-founded relation
-- for Core's pullbacks, subrelations and ranks.
child-wfrel :
    ∀ {ℓj ℓo ℓp ℓx}
      {signature : Signature ℓj ℓo ℓp}
      {X : Judgment signature → Set ℓx}
  → WFRel
      (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx)
      (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx)
child-wfrel {signature = signature} {X = X} = record
  { Carrier = Node signature X
  ; _<_ = Child {signature = signature} {X = X}
  ; wf = child-wf {signature = signature} {X = X}
  }

------------------------------------------------------------------------
-- Closed trees

-- HistoryNode Σ = Σ (j : Judgment Σ). History Σ j, the nodes of closed
-- trees.
HistoryNode :
    ∀ {ℓj ℓo ℓp}
      (signature : Signature ℓj ℓo ℓp)
  → Set (ℓj ⊔ ℓo ⊔ ℓp)
HistoryNode signature =
  Σ (Judgment signature) (History signature)

-- HistoryChild is Child at the empty family of holes.
HistoryChild :
    ∀ {ℓj ℓo ℓp}
      {signature : Signature ℓj ℓo ℓp}
  → HistoryNode signature
  → HistoryNode signature
  → Set (ℓj ⊔ ℓo ⊔ ℓp)
HistoryChild {signature = signature} =
  Child
    {signature = signature}
    {X = λ _ → ⊥ {lzero}}

history-node-acc :
    ∀ {ℓj ℓo ℓp}
      {signature : Signature ℓj ℓo ℓp}
      (history-node : HistoryNode signature)
  → Acc HistoryChild history-node
history-node-acc =
  node-acc

history-acc :
    ∀ {ℓj ℓo ℓp}
      {signature : Signature ℓj ℓo ℓp}
      {j : Judgment signature}
      (history : History signature j)
  → Acc HistoryChild (j , history)
history-acc history =
  tree-acc history

history-child-wf :
    ∀ {ℓj ℓo ℓp}
      {signature : Signature ℓj ℓo ℓp}
  → WellFounded (HistoryChild {signature = signature})
history-child-wf =
  history-node-acc

-- history-child-wfrel = (HistoryNode Σ , HistoryChild , history-child-wf).
history-child-wfrel :
    ∀ {ℓj ℓo ℓp}
      {signature : Signature ℓj ℓo ℓp}
  → WFRel
      (ℓj ⊔ ℓo ⊔ ℓp)
      (ℓj ⊔ ℓo ⊔ ℓp)
history-child-wfrel {signature = signature} = record
  { Carrier = HistoryNode signature
  ; _<_ = HistoryChild {signature = signature}
  ; wf = history-child-wf {signature = signature}
  }

------------------------------------------------------------------------
-- Relations contained in HistoryChild

-- A relation R on HistoryNode Σ contained in HistoryChild is well founded:
--
--   (Π {c p}. R c p → HistoryChild c p) → WellFounded R.

covered-wf :
    ∀ {ℓj ℓo ℓp ℓr : Level}
      {signature : Signature ℓj ℓo ℓp}
      {relation :
        HistoryNode signature → HistoryNode signature → Set ℓr}
  → (∀ {child parent}
      → relation child parent
      → HistoryChild child parent)
  → WellFounded relation
covered-wf covered =
  subrel-wf covered history-child-wf

-- Read as rewriting from parent to child, such an R terminates:
-- R ⊆ HistoryChild gives Term (reverseRelationRewrite R).

covered-termination :
    ∀ {ℓj ℓo ℓp ℓr : Level}
      {signature : Signature ℓj ℓo ℓp}
      {relation :
        HistoryNode signature → HistoryNode signature → Set ℓr}
  → (∀ {child parent}
      → relation child parent
      → HistoryChild child parent)
  → Termination.Term
      (reverseRelationRewrite relation)
covered-termination covered =
  covered-wf covered
