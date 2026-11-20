{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Tree.Fold.Relation.Heterogeneous where

-- Relational compatibility of tree algebras across changed judgment types,
-- signatures, operations and positions. Over a lax comparison of two
-- signatures (`Lax-Signature-Relation` of
-- SPT.Foundation.Tree.Relation.Heterogeneous), a family of hole cells and a
-- family of meaning cells, a heterogeneous relational algebra preserves
-- the cells at holes, and at a pair of operations related by an operation
-- cell c it turns a meaning cell at every target position q, the source
-- value taken at the projected antecedent of q, into a meaning cell of the
-- two node values (`Heterogeneous-Relational-Algebra`):
--
--   Hole-Cell r x y → Meaning-Cell r (on-hole A x) (on-hole B y),
--   (Π q. Meaning-Cell (boundary-cell c q) (d (project c q)) (e q))
--     → Meaning-Cell r (on-node A o d) (on-node B o′ e).
--
-- Heterogeneously related trees have related folds
-- (`heterogeneous-fold-rel`), by structural recursion on the tree cell,
-- which is consumed exactly once. Source positions may disappear, since
-- every target position selects its source antecedent, so no forward
-- position map, equality of child functions or function extensionality is
-- used.

open import SPT.Base
open import SPT.Foundation.Signature.Sum using
  (Signature-Over; Operation; Position; position-boundary; to-signature)
open import SPT.Foundation.Tree using (Tree)
open import SPT.Foundation.Tree.Fold using (Algebra; on-hole; on-node; fold)
open import SPT.Foundation.Tree.Relation.Heterogeneous using
  ( Lax-Signature-Relation; Operation-Cell; project-target-position
  ; boundary-cell; Heterogeneous-Tree-Rel; heterogeneous-hole-rel
  ; heterogeneous-node-rel )

------------------------------------------------------------------------
-- Heterogeneous relational algebras

-- The node clause receives one literal operation cell and one meaning cell
-- for every target child, the source child selected by the operation
-- cell's projection of target positions. The record supplies no equality
-- of algebras, folds, trees or child functions.

record Heterogeneous-Relational-Algebra
  {ℓjs ℓjt ℓos ℓps ℓot ℓpt ℓr ℓc ℓx ℓy ℓh ℓd ℓe ℓm : Level}
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
  {D : Source-Judgment → Set ℓd} {E : Target-Judgment → Set ℓe}
  (Meaning-Cell : {source-judgment : Source-Judgment}
    {target-judgment : Target-Judgment} →
    Judgment-Relation source-judgment target-judgment →
    D source-judgment → E target-judgment → Set ℓm)
  (source-algebra : Algebra (to-signature source) X D)
  (target-algebra : Algebra (to-signature target) Y E)
  : Set (ℓjs ⊔ ℓjt ⊔ ℓos ⊔ ℓps ⊔ ℓot ⊔ ℓpt ⊔ ℓr ⊔ ℓc ⊔ ℓx ⊔ ℓy ⊔ ℓh ⊔ ℓd
    ⊔ ℓe ⊔ ℓm) where
  field
    on-heterogeneous-hole-rel : {source-judgment : Source-Judgment}
      {target-judgment : Target-Judgment}
      {judgment-cell : Judgment-Relation source-judgment target-judgment}
      {source-payload : X source-judgment}
      {target-payload : Y target-judgment} →
      Hole-Cell judgment-cell source-payload target-payload →
      Meaning-Cell judgment-cell (on-hole source-algebra source-payload)
        (on-hole target-algebra target-payload)
    on-heterogeneous-node-rel : {source-judgment : Source-Judgment}
      {target-judgment : Target-Judgment}
      {judgment-cell : Judgment-Relation source-judgment target-judgment}
      {source-operation : Operation source source-judgment}
      {target-operation : Operation target target-judgment}
      (operation-cell : Operation-Cell signature-relation judgment-cell
        source-operation target-operation)
      {source-values : (source-position : Position source source-operation) →
        D (position-boundary source source-operation source-position)}
      {target-values : (target-position : Position target target-operation) →
        E (position-boundary target target-operation target-position)} →
      ((target-position : Position target target-operation) →
        Meaning-Cell
          (boundary-cell signature-relation operation-cell target-position)
          (source-values (project-target-position signature-relation
            operation-cell target-position))
          (target-values target-position)) →
      Meaning-Cell judgment-cell
        (on-node source-algebra source-operation source-values)
        (on-node target-algebra target-operation target-values)

open Heterogeneous-Relational-Algebra public

------------------------------------------------------------------------
-- Heterogeneously related trees have related folds

-- At a hole the hole clause is used; at a node the child cells are folded
-- at every literal target position and passed to the node clause.

module _ {ℓjs ℓjt ℓos ℓps ℓot ℓpt ℓr ℓc ℓx ℓy ℓh ℓd ℓe ℓm : Level}
  {Source-Judgment : Set ℓjs} {Target-Judgment : Set ℓjt}
  {Judgment-Relation : Source-Judgment → Target-Judgment → Set ℓr}
  {source : Signature-Over Source-Judgment ℓos ℓps}
  {target : Signature-Over Target-Judgment ℓot ℓpt}
  {signature-relation :
    Lax-Signature-Relation Judgment-Relation source target ℓc}
  {X : Source-Judgment → Set ℓx} {Y : Target-Judgment → Set ℓy}
  {Hole-Cell : {source-judgment : Source-Judgment}
    {target-judgment : Target-Judgment} →
    Judgment-Relation source-judgment target-judgment →
    X source-judgment → Y target-judgment → Set ℓh}
  {D : Source-Judgment → Set ℓd} {E : Target-Judgment → Set ℓe}
  {Meaning-Cell : {source-judgment : Source-Judgment}
    {target-judgment : Target-Judgment} →
    Judgment-Relation source-judgment target-judgment →
    D source-judgment → E target-judgment → Set ℓm}
  {source-algebra : Algebra (to-signature source) X D}
  {target-algebra : Algebra (to-signature target) Y E}
  (relational-algebra :
    Heterogeneous-Relational-Algebra signature-relation Hole-Cell
      Meaning-Cell source-algebra target-algebra) where

  heterogeneous-fold-rel : {source-judgment : Source-Judgment}
    {target-judgment : Target-Judgment}
    {judgment-cell : Judgment-Relation source-judgment target-judgment}
    {source-tree : Tree (to-signature source) X source-judgment}
    {target-tree : Tree (to-signature target) Y target-judgment} →
    Heterogeneous-Tree-Rel signature-relation Hole-Cell judgment-cell
      source-tree target-tree →
    Meaning-Cell judgment-cell (fold source-algebra source-tree)
      (fold target-algebra target-tree)
  heterogeneous-fold-rel (heterogeneous-hole-rel related) =
    on-heterogeneous-hole-rel relational-algebra related
  heterogeneous-fold-rel (heterogeneous-node-rel operation-cell related) =
    on-heterogeneous-node-rel relational-algebra operation-cell
      (λ target-position → heterogeneous-fold-rel (related target-position))
