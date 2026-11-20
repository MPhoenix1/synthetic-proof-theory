{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Tree.LaxTranslation where

-- The action of a lax signature translation
-- (SPT.Cubical.Foundation.Signature.LaxTranslation) on open trees, and the
-- canonical heterogeneous cells relating a tree to its image.
--
-- * A reindexed hole keeps the exact source judgment, the source payload
--   and the path placing it in the target fiber (`Reindexed-Hole`):
--
--     Reindexed-Hole f X j = Σ (i : J_S). Σ (x : X i). f i ＝ j.
--
--   A payload gives its canonical reindexed hole, and a hole action
--   collapses reindexed holes (`canonical-reindexed-hole`,
--   `collapse-reindexed-hole`).
-- * A translation acts on open trees (`reindex-tree`, keeping every source
--   hole; `map-lax-tree`, through a supplied hole action): an operation is
--   mapped, every target position takes the action on its projected
--   source child, transported along the boundary coherence, and source
--   positions without a target position are dropped.
-- * The graph of a translation is a lax comparison of the two signatures
--   over the judgment relation f i ＝ j (`lax-translation-signature-
--   relation`): an operation cell identifies the transported image of the
--   source operation with the target operation. Over it, every tree is
--   related to its image by a canonical heterogeneous tree cell
--   (`reindex-tree-cell`, over `Reindexed-Hole-Cell`; `map-lax-tree-cell`,
--   over `Lax-Hole-Action-Cell`).
--
-- No forward survival of source positions, occurrence equivalence,
-- equality of tree functions or fold naturality is supplied here.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Signature.Sum using
  (Signature-Over; Operation; Position; position-boundary; to-signature)
open import SPT.Cubical.Foundation.Signature.LaxTranslation using
  ( Lax-Signature-Translation; map-lax-operation; project-lax-position
  ; lax-boundary-coherence )
open import SPT.Cubical.Foundation.Tree using (Tree; hole; node)
open import SPT.Cubical.Foundation.Tree.Relation.Heterogeneous using
  ( Lax-Signature-Relation; Heterogeneous-Tree-Rel; heterogeneous-hole-rel
  ; heterogeneous-node-rel )

------------------------------------------------------------------------
-- Source provenance of reindexed holes

module _ {ℓj₁ ℓj₂ ℓx : Level} {Source-Judgment : Set ℓj₁}
  {Target-Judgment : Set ℓj₂}
  (on-judgment : Source-Judgment → Target-Judgment)
  (X : Source-Judgment → Set ℓx) where

  Reindexed-Hole : Target-Judgment → Set (ℓj₁ ⊔ ℓj₂ ⊔ ℓx)
  Reindexed-Hole target-judgment =
    Σ Source-Judgment (λ source-judgment →
      Σ (X source-judgment) (λ source-hole →
        on-judgment source-judgment ＝ target-judgment))

  canonical-reindexed-hole : {source-judgment : Source-Judgment} →
    X source-judgment → Reindexed-Hole (on-judgment source-judgment)
  canonical-reindexed-hole {source-judgment} source-hole =
    source-judgment , source-hole , refl

  collapse-reindexed-hole : {ℓy : Level} (Y : Target-Judgment → Set ℓy) →
    ((source-judgment : Source-Judgment) → X source-judgment →
      Y (on-judgment source-judgment)) →
    {target-judgment : Target-Judgment} →
    Reindexed-Hole target-judgment → Y target-judgment
  collapse-reindexed-hole Y on-hole
    (source-judgment , source-hole , judgment-path) =
    transport Y judgment-path (on-hole source-judgment source-hole)

-- A reindexed hole is related to exactly the source payload it retains,
-- over the path it stores.

data Reindexed-Hole-Cell {ℓj₁ ℓj₂ ℓx : Level} {Source-Judgment : Set ℓj₁}
  {Target-Judgment : Set ℓj₂}
  (on-judgment : Source-Judgment → Target-Judgment)
  (X : Source-Judgment → Set ℓx) : {source-judgment : Source-Judgment}
  {target-judgment : Target-Judgment} →
  on-judgment source-judgment ＝ target-judgment → X source-judgment →
  Reindexed-Hole on-judgment X target-judgment → Set (ℓj₁ ⊔ ℓj₂ ⊔ ℓx)
  where
  retained-reindexed-hole : {source-judgment : Source-Judgment}
    {target-judgment : Target-Judgment} (source-hole : X source-judgment)
    (judgment-cell : on-judgment source-judgment ＝ target-judgment) →
    Reindexed-Hole-Cell on-judgment X judgment-cell source-hole
      (source-judgment , source-hole , judgment-cell)

-- A hole action relates a source payload to the target payload it places
-- in the fiber at the related judgment.

module _ {ℓj₁ ℓj₂ ℓx ℓy : Level} {Source-Judgment : Set ℓj₁}
  {Target-Judgment : Set ℓj₂}
  (on-judgment : Source-Judgment → Target-Judgment)
  (X : Source-Judgment → Set ℓx) (Y : Target-Judgment → Set ℓy)
  (on-hole : (source-judgment : Source-Judgment) → X source-judgment →
    Y (on-judgment source-judgment)) where

  Lax-Hole-Action-Cell : {source-judgment : Source-Judgment}
    {target-judgment : Target-Judgment} →
    on-judgment source-judgment ＝ target-judgment → X source-judgment →
    Y target-judgment → Set ℓy
  Lax-Hole-Action-Cell {source-judgment} judgment-cell source-hole
    target-hole =
    transport Y judgment-cell (on-hole source-judgment source-hole)
      ＝ target-hole

------------------------------------------------------------------------
-- The action on open trees

module _ {ℓj₁ ℓo₁ ℓp₁ ℓj₂ ℓo₂ ℓp₂ : Level} {Source-Judgment : Set ℓj₁}
  {Target-Judgment : Set ℓj₂}
  {on-judgment : Source-Judgment → Target-Judgment}
  {source : Signature-Over Source-Judgment ℓo₁ ℓp₁}
  {target : Signature-Over Target-Judgment ℓo₂ ℓp₂}
  (translation : Lax-Signature-Translation on-judgment source target) where

  reindex-tree : {ℓx : Level} {X : Source-Judgment → Set ℓx}
    {source-judgment : Source-Judgment} →
    Tree (to-signature source) X source-judgment →
    Tree (to-signature target) (Reindexed-Hole on-judgment X)
      (on-judgment source-judgment)
  reindex-tree {ℓx} {X} (hole source-hole) =
    hole (canonical-reindexed-hole on-judgment X source-hole)
  reindex-tree {ℓx} {X} (node source-operation source-child) =
    node (map-lax-operation translation source-operation)
      (λ target-position →
        transport (Tree (to-signature target) (Reindexed-Hole on-judgment X))
          (lax-boundary-coherence translation source-operation
            target-position)
          (reindex-tree
            (source-child
              (project-lax-position translation source-operation
                target-position))))

  map-lax-tree : {ℓx ℓy : Level} {X : Source-Judgment → Set ℓx}
    (Y : Target-Judgment → Set ℓy) →
    ((source-judgment : Source-Judgment) → X source-judgment →
      Y (on-judgment source-judgment)) →
    {source-judgment : Source-Judgment} →
    Tree (to-signature source) X source-judgment →
    Tree (to-signature target) Y (on-judgment source-judgment)
  map-lax-tree Y on-hole (hole {source-judgment} source-hole) =
    hole (on-hole source-judgment source-hole)
  map-lax-tree Y on-hole (node source-operation source-child) =
    node (map-lax-operation translation source-operation)
      (λ target-position →
        transport (Tree (to-signature target) Y)
          (lax-boundary-coherence translation source-operation
            target-position)
          (map-lax-tree Y on-hole
            (source-child
              (project-lax-position translation source-operation
                target-position))))

  reindex-tree-hole : {ℓx : Level} (X : Source-Judgment → Set ℓx)
    {source-judgment : Source-Judgment} (source-hole : X source-judgment) →
    reindex-tree (hole source-hole)
      ＝ hole (canonical-reindexed-hole on-judgment X source-hole)
  reindex-tree-hole X source-hole = refl

  map-lax-tree-hole : {ℓx ℓy : Level} (X : Source-Judgment → Set ℓx)
    (Y : Target-Judgment → Set ℓy)
    (on-hole : (source-judgment : Source-Judgment) → X source-judgment →
      Y (on-judgment source-judgment))
    {source-judgment : Source-Judgment} (source-hole : X source-judgment) →
    map-lax-tree Y on-hole (hole source-hole)
      ＝ hole (on-hole source-judgment source-hole)
  map-lax-tree-hole X Y on-hole source-hole = refl

------------------------------------------------------------------------
-- The graph of a translation as a lax comparison of signatures

-- Over the judgment relation f i ＝ j, an operation cell identifies the
-- transported image of the source operation with the target operation;
-- target positions project by the translation, and the child witness is
-- the boundary coherence.

  Lax-Translation-Operation-Graph-Cell : {source-judgment : Source-Judgment}
    {target-judgment : Target-Judgment} →
    on-judgment source-judgment ＝ target-judgment →
    Operation source source-judgment → Operation target target-judgment →
    Set ℓo₂
  Lax-Translation-Operation-Graph-Cell judgment-cell source-operation
    target-operation =
    transport (Operation target) judgment-cell
      (map-lax-operation translation source-operation)
      ＝ target-operation

  lax-translation-graph-project : {source-judgment : Source-Judgment}
    {target-judgment : Target-Judgment}
    (judgment-cell : on-judgment source-judgment ＝ target-judgment)
    {source-operation : Operation source source-judgment}
    {target-operation : Operation target target-judgment} →
    Lax-Translation-Operation-Graph-Cell judgment-cell source-operation
      target-operation →
    Position target target-operation → Position source source-operation
  lax-translation-graph-project refl {source-operation} refl
    target-position =
    project-lax-position translation source-operation target-position

  lax-translation-graph-boundary : {source-judgment : Source-Judgment}
    {target-judgment : Target-Judgment}
    (judgment-cell : on-judgment source-judgment ＝ target-judgment)
    {source-operation : Operation source source-judgment}
    {target-operation : Operation target target-judgment}
    (operation-cell : Lax-Translation-Operation-Graph-Cell judgment-cell
      source-operation target-operation)
    (target-position : Position target target-operation) →
    on-judgment
      (position-boundary source source-operation
        (lax-translation-graph-project judgment-cell operation-cell
          target-position))
      ＝ position-boundary target target-operation target-position
  lax-translation-graph-boundary refl {source-operation} refl
    target-position =
    lax-boundary-coherence translation source-operation target-position

  lax-translation-signature-relation :
    Lax-Signature-Relation
      (λ source-judgment target-judgment →
        on-judgment source-judgment ＝ target-judgment)
      source target ℓo₂
  lax-translation-signature-relation = record
    { Operation-Cell = Lax-Translation-Operation-Graph-Cell
    ; project-target-position = λ {source-judgment} {target-judgment}
        {judgment-cell} → lax-translation-graph-project judgment-cell
    ; boundary-cell = λ {source-judgment} {target-judgment}
        {judgment-cell} → lax-translation-graph-boundary judgment-cell
    }

------------------------------------------------------------------------
-- Canonical cells of the two actions

-- Every source tree is related to its image over the graph: at a hole by
-- the retained or acted hole, at a node by the reflexive operation cell and
-- the cells of the projected children over the boundary coherences.

  reindex-tree-cell-at : {ℓx : Level} {X : Source-Judgment → Set ℓx}
    {source-judgment : Source-Judgment} {target-judgment : Target-Judgment}
    (judgment-cell : on-judgment source-judgment ＝ target-judgment)
    (source-tree : Tree (to-signature source) X source-judgment) →
    Heterogeneous-Tree-Rel lax-translation-signature-relation
      (Reindexed-Hole-Cell on-judgment X) judgment-cell source-tree
      (transport (Tree (to-signature target) (Reindexed-Hole on-judgment X))
        judgment-cell (reindex-tree source-tree))
  reindex-tree-cell-at refl (hole source-hole) =
    heterogeneous-hole-rel (retained-reindexed-hole source-hole refl)
  reindex-tree-cell-at refl (node source-operation source-child) =
    heterogeneous-node-rel refl
      (λ target-position →
        reindex-tree-cell-at
          (lax-boundary-coherence translation source-operation
            target-position)
          (source-child
            (project-lax-position translation source-operation
              target-position)))

  reindex-tree-cell : {ℓx : Level} {X : Source-Judgment → Set ℓx}
    {source-judgment : Source-Judgment}
    (source-tree : Tree (to-signature source) X source-judgment) →
    Heterogeneous-Tree-Rel lax-translation-signature-relation
      (Reindexed-Hole-Cell on-judgment X) refl source-tree
      (reindex-tree source-tree)
  reindex-tree-cell source-tree = reindex-tree-cell-at refl source-tree

  map-lax-tree-cell-at : {ℓx ℓy : Level} {X : Source-Judgment → Set ℓx}
    (Y : Target-Judgment → Set ℓy)
    (on-hole : (source-judgment : Source-Judgment) → X source-judgment →
      Y (on-judgment source-judgment))
    {source-judgment : Source-Judgment} {target-judgment : Target-Judgment}
    (judgment-cell : on-judgment source-judgment ＝ target-judgment)
    (source-tree : Tree (to-signature source) X source-judgment) →
    Heterogeneous-Tree-Rel lax-translation-signature-relation
      (Lax-Hole-Action-Cell on-judgment X Y on-hole) judgment-cell
      source-tree
      (transport (Tree (to-signature target) Y) judgment-cell
        (map-lax-tree Y on-hole source-tree))
  map-lax-tree-cell-at Y on-hole refl (hole source-hole) =
    heterogeneous-hole-rel refl
  map-lax-tree-cell-at Y on-hole refl (node source-operation source-child) =
    heterogeneous-node-rel refl
      (λ target-position →
        map-lax-tree-cell-at Y on-hole
          (lax-boundary-coherence translation source-operation
            target-position)
          (source-child
            (project-lax-position translation source-operation
              target-position)))

  map-lax-tree-cell : {ℓx ℓy : Level} {X : Source-Judgment → Set ℓx}
    (Y : Target-Judgment → Set ℓy)
    (on-hole : (source-judgment : Source-Judgment) → X source-judgment →
      Y (on-judgment source-judgment))
    {source-judgment : Source-Judgment}
    (source-tree : Tree (to-signature source) X source-judgment) →
    Heterogeneous-Tree-Rel lax-translation-signature-relation
      (Lax-Hole-Action-Cell on-judgment X Y on-hole) refl source-tree
      (map-lax-tree Y on-hole source-tree)
  map-lax-tree-cell Y on-hole source-tree =
    map-lax-tree-cell-at Y on-hole refl source-tree
