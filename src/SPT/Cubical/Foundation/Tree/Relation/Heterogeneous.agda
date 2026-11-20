{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Tree.Relation.Heterogeneous where

-- Structural relations between open trees whose judgment types,
-- signatures, operations, positions and hole families may all differ.
-- A lax comparison of a source and a target signature over a relation R
-- of their judgments relates operations over a judgment witness, and every
-- target position of a related pair selects its source antecedent and a
-- witness between the two boundary judgments
-- (`Lax-Signature-Relation`):
--
--   Operation-Cell r o o′ : Set,
--   project-target-position : Operation-Cell r o o′ → Pos o′ → Pos o,
--   boundary-cell c q : R (∂ o (project-target-position c q)) (∂ o′ q).
--
-- Source positions may disappear, so no forward position map is required.
-- Over a family of hole cells, two holes are related by a hole cell, and
-- two nodes by one operation cell with a related pair of children at every
-- target position, the source child taken at its projected antecedent
-- (`Heterogeneous-Tree-Rel`):
--
--   hole x ∼ hole y ⇐ Hole-Cell r x y,
--   node o k ∼ node o′ k′
--     ⇐ Σ (c : Operation-Cell r o o′).
--         Π (q : Pos o′). k (project-target-position c q) ∼ k′ q
--           over boundary-cell c q.
--
-- No forward survival of source positions, identification of trees or of
-- children, uniqueness of ancestry, tree action or fold theorem is
-- supplied.
--
-- The level of operation cells is an explicit parameter of the signature
-- relation, since no other parameter determines it.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Signature.Sum using
  (Signature-Over; Operation; Position; position-boundary; to-signature)
open import SPT.Cubical.Foundation.Tree using (Tree; hole; node)

------------------------------------------------------------------------
-- Lax comparisons of signatures

-- An operation cell relates one source operation to one target operation
-- over an already retained judgment witness; every target position then
-- selects its literal source antecedent and a witness between the two
-- boundary judgments. The record supplies no operation function, coverage
-- of source positions, inverse position law or tree action.

record Lax-Signature-Relation {ℓjs ℓjt ℓos ℓps ℓot ℓpt ℓr : Level}
  {Source-Judgment : Set ℓjs} {Target-Judgment : Set ℓjt}
  (Judgment-Relation : Source-Judgment → Target-Judgment → Set ℓr)
  (source : Signature-Over Source-Judgment ℓos ℓps)
  (target : Signature-Over Target-Judgment ℓot ℓpt) (ℓc : Level)
  : Set (lsuc (ℓjs ⊔ ℓjt ⊔ ℓos ⊔ ℓps ⊔ ℓot ⊔ ℓpt ⊔ ℓr ⊔ ℓc)) where
  field
    Operation-Cell : {source-judgment : Source-Judgment}
      {target-judgment : Target-Judgment} →
      Judgment-Relation source-judgment target-judgment →
      Operation source source-judgment → Operation target target-judgment →
      Set ℓc

    project-target-position : {source-judgment : Source-Judgment}
      {target-judgment : Target-Judgment}
      {judgment-cell : Judgment-Relation source-judgment target-judgment}
      {source-operation : Operation source source-judgment}
      {target-operation : Operation target target-judgment} →
      Operation-Cell judgment-cell source-operation target-operation →
      Position target target-operation → Position source source-operation

    boundary-cell : {source-judgment : Source-Judgment}
      {target-judgment : Target-Judgment}
      {judgment-cell : Judgment-Relation source-judgment target-judgment}
      {source-operation : Operation source source-judgment}
      {target-operation : Operation target target-judgment}
      (operation-cell :
        Operation-Cell judgment-cell source-operation target-operation)
      (target-position : Position target target-operation) →
      Judgment-Relation
        (position-boundary source source-operation
          (project-target-position operation-cell target-position))
        (position-boundary target target-operation target-position)

open Lax-Signature-Relation public

------------------------------------------------------------------------
-- The heterogeneous structural relation on open trees

-- At a node, one literal operation cell is retained, and every target
-- branch records its exact source antecedent and the cell of the two
-- children over the boundary witness. Changed operations and judgment
-- types are permitted; all ancestry justified by the projection of target
-- positions is kept.

module _ {ℓjs ℓjt ℓos ℓps ℓot ℓpt ℓr ℓc ℓx ℓy ℓh : Level}
  {Source-Judgment : Set ℓjs} {Target-Judgment : Set ℓjt}
  {Judgment-Relation : Source-Judgment → Target-Judgment → Set ℓr}
  {source : Signature-Over Source-Judgment ℓos ℓps}
  {target : Signature-Over Target-Judgment ℓot ℓpt}
  (signature-relation :
    Lax-Signature-Relation Judgment-Relation source target ℓc)
  {X : Source-Judgment → Set ℓx} {Y : Target-Judgment → Set ℓy}
  (Hole-Cell : {source-judgment : Source-Judgment}
    {target-judgment : Target-Judgment} →
    Judgment-Relation source-judgment target-judgment →
    X source-judgment → Y target-judgment → Set ℓh)
  where

  data Heterogeneous-Tree-Rel : {source-judgment : Source-Judgment}
    {target-judgment : Target-Judgment} →
    Judgment-Relation source-judgment target-judgment →
    Tree (to-signature source) X source-judgment →
    Tree (to-signature target) Y target-judgment →
    Set (ℓjs ⊔ ℓjt ⊔ ℓos ⊔ ℓps ⊔ ℓot ⊔ ℓpt ⊔ ℓr ⊔ ℓc ⊔ ℓx ⊔ ℓy ⊔ ℓh)
    where
    heterogeneous-hole-rel : {source-judgment : Source-Judgment}
      {target-judgment : Target-Judgment}
      {judgment-cell : Judgment-Relation source-judgment target-judgment}
      {source-payload : X source-judgment}
      {target-payload : Y target-judgment} →
      Hole-Cell judgment-cell source-payload target-payload →
      Heterogeneous-Tree-Rel judgment-cell (hole source-payload)
        (hole target-payload)

    heterogeneous-node-rel : {source-judgment : Source-Judgment}
      {target-judgment : Target-Judgment}
      {judgment-cell : Judgment-Relation source-judgment target-judgment}
      {source-operation : Operation source source-judgment}
      {target-operation : Operation target target-judgment}
      {source-child : (source-position : Position source source-operation) →
        Tree (to-signature source) X
          (position-boundary source source-operation source-position)}
      {target-child : (target-position : Position target target-operation) →
        Tree (to-signature target) Y
          (position-boundary target target-operation target-position)}
      (operation-cell : Operation-Cell signature-relation judgment-cell
        source-operation target-operation) →
      ((target-position : Position target target-operation) →
        Heterogeneous-Tree-Rel
          (boundary-cell signature-relation operation-cell target-position)
          (source-child (project-target-position signature-relation
            operation-cell target-position))
          (target-child target-position)) →
      Heterogeneous-Tree-Rel judgment-cell (node source-operation source-child)
        (node target-operation target-child)
