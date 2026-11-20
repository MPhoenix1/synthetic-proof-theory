{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Tree.W.Indexed where

-- The open trees of an indexed signature as one ordinary W-type with a
-- checking family. Raw trees are the closed trees of Tree.W over the labels
-- Σ j. X j ⊎ Op j, a hole payload branching over nothing and an operation
-- over its positions (`Label`, `label-arity`, `Raw-Tree`). A check of a raw
-- tree at j records at its root an identification of the root's judgment
-- with j; at a hole, also an identification of its children with the empty
-- family (`no-children`), the device of Hugunin's Why Not W? (TYPES 2020)
-- that needs no extensionality; at an operation, the checks of its children
-- (`Check`, `Checked`).
--
-- Checked trees have holes and nodes (`checked-hole`, `checked-node`) and
-- dependent induction whose two computation rules hold by refl
-- (`Checked-Steps`, `checked-induction`, `checked-induction-hole`,
-- `checked-induction-node`). So the trees of every signature reduce to one
-- ordinary W-type with identity types, Σ, Π, ⊎ and the empty type. Trees and
-- checked trees convert both ways (`write-checked`, `read-checked`, with
-- `read-checked-hole` and `read-checked-node` by refl); reading after
-- writing is a structural tree relation with no hypothesis
-- (`read-write-rel`), and both round trips are identifications under
-- extensionality for children (`read-write`, `write-read`).

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Extensionality using (FunExt)
open import SPT.Cubical.Foundation.Tree
open import SPT.Cubical.Foundation.Tree.Relation using
  (TreeRel; hole-rel; node-rel; ChildΠExt)
import SPT.Cubical.Foundation.Tree.W as W

module _
  {ℓj ℓo ℓp ℓx : Level} (S : Signature ℓj ℓo ℓp) (X : Judgment S → Set ℓx)
  where

  ----------------------------------------------------------------------
  -- Raw trees and their checks

  Label : Set (ℓj ⊔ ℓo ⊔ ℓx)
  Label = Σ (Judgment S) (λ j → X j ⊎ Op S j)

  label-arity : Label → Set ℓp
  label-arity (j , inl x) = Lift ℓp 𝟘
  label-arity (j , inr o) = Pos S o

  Raw-Tree : Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx)
  Raw-Tree = W.W Label label-arity

  -- The children of a hole: the empty family.
  no-children : Lift ℓp 𝟘 → Raw-Tree
  no-children (lift ())

  Check : Raw-Tree → Judgment S → Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx)
  Check (hole ()) j
  Check (node (i , inl x) k) j = (i ＝ j) × (no-children ＝ k)
  Check (node (i , inr o) k) j =
    (i ＝ j) × ((p : Pos S o) → Check (k p) (boundary S o p))

  Checked : Judgment S → Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx)
  Checked j = Σ Raw-Tree (λ t → Check t j)

  ----------------------------------------------------------------------
  -- Holes, nodes and induction

  checked-hole : {j : Judgment S} → X j → Checked j
  checked-hole {j} x = node (j , inl x) no-children , refl , refl

  checked-node :
    {j : Judgment S} (o : Op S j) →
    ((p : Pos S o) → Checked (boundary S o p)) → Checked j
  checked-node {j} o k =
    node (j , inr o) (λ p → pr₁ (k p)) , refl , (λ p → pr₂ (k p))

  -- The steps of an induction into a family over checked trees.
  record Checked-Steps {ν : Level} (P : (j : Judgment S) → Checked j → Set ν) :
    Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx ⊔ ν) where
    field
      holes : {j : Judgment S} (x : X j) → P j (checked-hole x)
      nodes :
        {j : Judgment S} (o : Op S j)
        (k : (p : Pos S o) → Checked (boundary S o p)) →
        ((p : Pos S o) → P (boundary S o p) (k p)) → P j (checked-node o k)

  -- Induction on a raw tree with its check: a hole's children are the empty
  -- family by its check, and a node's children are checked.
  raw-induction :
    {ν : Level} (P : (j : Judgment S) → Checked j → Set ν) → Checked-Steps P
    → (t : Raw-Tree) (j : Judgment S) (c : Check t j) → P j (t , c)
  raw-induction P m (hole ()) j c
  raw-induction P m (node (i , inl x) k) j (refl , refl) =
    Checked-Steps.holes m x
  raw-induction P m (node (i , inr o) k) j (refl , z) =
    Checked-Steps.nodes m o (λ p → k p , z p)
      (λ p → raw-induction P m (k p) (boundary S o p) (z p))

  checked-induction :
    {ν : Level} (P : (j : Judgment S) → Checked j → Set ν) → Checked-Steps P
    → (j : Judgment S) (t : Checked j) → P j t
  checked-induction P m j t = raw-induction P m (pr₁ t) j (pr₂ t)

  checked-induction-hole :
    {ν : Level} (P : (j : Judgment S) → Checked j → Set ν)
    (m : Checked-Steps P) {j : Judgment S} (x : X j) →
    checked-induction P m j (checked-hole x) ＝ Checked-Steps.holes m x
  checked-induction-hole P m x = refl

  checked-induction-node :
    {ν : Level} (P : (j : Judgment S) → Checked j → Set ν)
    (m : Checked-Steps P) {j : Judgment S} (o : Op S j)
    (k : (p : Pos S o) → Checked (boundary S o p)) →
    checked-induction P m j (checked-node o k)
      ＝ Checked-Steps.nodes m o k
          (λ p → checked-induction P m (boundary S o p) (k p))
  checked-induction-node P m o k = refl

  ----------------------------------------------------------------------
  -- Trees and checked trees

  write-checked : {j : Judgment S} → Tree S X j → Checked j
  write-checked (hole x) = checked-hole x
  write-checked (node o k) = checked-node o (λ p → write-checked (k p))

  -- Reading is induction into trees.
  Trees : (j : Judgment S) → Checked j → Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx)
  Trees j t = Tree S X j

  reading-steps : Checked-Steps Trees
  reading-steps = record
    { holes = hole
    ; nodes = λ o k r → node o r
    }

  read-checked : (j : Judgment S) → Checked j → Tree S X j
  read-checked = checked-induction Trees reading-steps

  read-checked-hole :
    {j : Judgment S} (x : X j) → read-checked j (checked-hole x) ＝ hole x
  read-checked-hole x = refl

  read-checked-node :
    {j : Judgment S} (o : Op S j)
    (k : (p : Pos S o) → Checked (boundary S o p)) →
    read-checked j (checked-node o k)
      ＝ node o (λ p → read-checked (boundary S o p) (k p))
  read-checked-node o k = refl

  read-write-rel :
    {j : Judgment S} (t : Tree S X j) →
    TreeRel _＝_ (read-checked j (write-checked t)) t
  read-write-rel (hole x) = hole-rel refl
  read-write-rel (node o k) = node-rel (λ p → read-write-rel (k p))

  read-write :
    ChildΠExt S X → {j : Judgment S} (t : Tree S X j) →
    read-checked j (write-checked t) ＝ t
  read-write πext (hole x) = refl
  read-write πext (node o k) =
    ap (node o)
      (πext o (λ p → read-checked (boundary S o p) (write-checked (k p))) k
        (λ p → read-write πext (k p)))

  -- Extensionality for the children of a node of checked trees.
  Checked-Children-Extensionality : Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx)
  Checked-Children-Extensionality =
    {j : Judgment S} (o : Op S j) →
    FunExt (Pos S o) (λ p → Checked (boundary S o p))

  -- Writing after reading, as a family over checked trees.
  Written : (j : Judgment S) → Checked j → Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx)
  Written j t = write-checked (read-checked j t) ＝ t

  write-read :
    Checked-Children-Extensionality → (j : Judgment S) (t : Checked j) →
    write-checked (read-checked j t) ＝ t
  write-read ext = checked-induction Written (record
    { holes = λ x → refl
    ; nodes = λ o k r →
        ap (checked-node o)
          (ext o (λ p → write-checked (read-checked (boundary S o p) (k p)))
            k r)
    })
