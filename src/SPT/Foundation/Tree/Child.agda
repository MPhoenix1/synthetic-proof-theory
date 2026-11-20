{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Tree.Child where

-- A node is a tree together with its judgment. `Child` relates the subtree at a
-- position to the node it hangs from: a witness selects one position of the
-- operation, so holes and nullary operations have no children. `Child` is
-- well-founded by induction on trees: a hole has no predecessors
-- (`holes-have-no-predecessors`), and the predecessors of a node are accessible
-- once its children are (`predecessors-of-node-are-accessible`), which the
-- proof for each child provides. The same holds on closed trees, and for every
-- relation contained in `HistoryChild`; read as rewriting from parent to child,
-- such a relation terminates.

open import SPT.Base
open import SPT.Foundation.Accessibility using
  ( is-accessible; acc; is-well-founded; Well-Founded-Relation
  ; well-founded-relation )
open import SPT.Foundation.WellFounded.Subrelation using
  (_⊆_; subrelations-are-well-founded)
open import SPT.Foundation.WellFounded.Rewriting using
  (reversed; terminates)
open import SPT.Foundation.Tree

------------------------------------------------------------------------
-- Nodes and their children

module _ {ℓj ℓo ℓp ℓx : Level} (S : Signature ℓj ℓo ℓp)
  (X : Judgment S → Set ℓx) where

  Node : Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx)
  Node = Σ (Judgment S) (Tree S X)

module _ {ℓj ℓo ℓp ℓx : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} where

  data Child : Node S X → Node S X → Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx) where
    node-child : {j : Judgment S} {operation : Op S j}
      {child : (position : Pos S operation) →
        Tree S X (boundary S operation position)}
      (position : Pos S operation) →
      Child (boundary S operation position , child position)
        (j , node operation child)

------------------------------------------------------------------------
-- Closed trees

module _ {ℓj ℓo ℓp : Level} (S : Signature ℓj ℓo ℓp) where

  HistoryNode : Set (ℓj ⊔ ℓo ⊔ ℓp)
  HistoryNode = Σ (Judgment S) (History S)

module _ {ℓj ℓo ℓp : Level} {S : Signature ℓj ℓo ℓp} where

  HistoryChild : HistoryNode S → HistoryNode S → Set (ℓj ⊔ ℓo ⊔ ℓp)
  HistoryChild = Child

------------------------------------------------------------------------
-- Child is well-founded

module _ {ℓj ℓo ℓp ℓx : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} where

  holes-have-no-predecessors : {j : Judgment S} (payload : X j)
    (predecessor : Node S X) → Child predecessor (j , hole payload) →
    is-accessible Child predecessor
  holes-have-no-predecessors payload predecessor ()

  predecessors-of-node-are-accessible : {j : Judgment S}
    (operation : Op S j)
    (child : (position : Pos S operation) →
      Tree S X (boundary S operation position)) →
    ((position : Pos S operation) →
      is-accessible Child (boundary S operation position , child position)) →
    (predecessor : Node S X) → Child predecessor (j , node operation child) →
    is-accessible Child predecessor
  predecessors-of-node-are-accessible operation child children
    .(boundary S operation position , child position)
    (node-child position) = children position

  tree-acc : {j : Judgment S} (tree : Tree S X j) →
    is-accessible Child (j , tree)
  tree-acc (hole payload) = acc (holes-have-no-predecessors payload)
  tree-acc (node operation child) =
    acc (predecessors-of-node-are-accessible operation child
      (λ position → tree-acc (child position)))

  node-acc : (tree-node : Node S X) → is-accessible Child tree-node
  node-acc (j , tree) = tree-acc tree

  child-wf : is-well-founded Child
  child-wf = node-acc

  child-wfrel : Well-Founded-Relation (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx)
    (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx)
  child-wfrel = well-founded-relation (Node S X) Child child-wf

------------------------------------------------------------------------
-- HistoryChild is well-founded

module _ {ℓj ℓo ℓp : Level} {S : Signature ℓj ℓo ℓp} where

  history-node-acc : (history-node : HistoryNode S) →
    is-accessible HistoryChild history-node
  history-node-acc = node-acc

  history-acc : {j : Judgment S} (history : History S j) →
    is-accessible HistoryChild (j , history)
  history-acc history = tree-acc history

  history-child-wf : is-well-founded HistoryChild
  history-child-wf = history-node-acc

  history-child-wfrel : Well-Founded-Relation (ℓj ⊔ ℓo ⊔ ℓp)
    (ℓj ⊔ ℓo ⊔ ℓp)
  history-child-wfrel =
    well-founded-relation (HistoryNode S) HistoryChild history-child-wf

------------------------------------------------------------------------
-- Relations contained in HistoryChild

--   (Π {c p}. R c p → HistoryChild c p) → is-well-founded R

module _ {ℓj ℓo ℓp ℓr : Level} {S : Signature ℓj ℓo ℓp}
  {relation : HistoryNode S → HistoryNode S → Set ℓr} where

  covered-wf : relation ⊆ HistoryChild → is-well-founded relation
  covered-wf covered =
    subrelations-are-well-founded covered history-child-wf

  covered-termination : relation ⊆ HistoryChild →
    terminates (reversed relation)
  covered-termination covered = covered-wf covered
