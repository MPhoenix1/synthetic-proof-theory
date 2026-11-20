{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Tree.Fold.Relation.Heterogeneous.LaxTranslation where

-- Fold naturality for the action of a lax signature translation on open
-- trees. For a translation τ over a judgment map f, a hole action h, two
-- algebras A and B, and meaning cells C_p over the graph p : f i ＝ j, a
-- heterogeneous relational algebra over the graph of τ and the hole cells
-- of h gives, for every source tree t (`lax-tree-fold-natural`),
--
--   C_refl (fold A t) (fold B (map-lax-tree τ h t)).
--
-- It is `heterogeneous-fold-rel` at the canonical cell `map-lax-tree-cell`:
-- at every target branch the algebra receives the target position, its
-- projected source antecedent, the boundary coherence and the folded
-- child cell. The local cells are not inferred; no identification of fold
-- functions and no identity or composition coherence is supplied.

open import SPT.Base
open import SPT.Foundation.Signature.Sum using
  (Signature-Over; to-signature)
open import SPT.Foundation.Signature.LaxTranslation using
  (Lax-Signature-Translation)
open import SPT.Foundation.Tree using (Tree)
open import SPT.Foundation.Tree.Fold using (Algebra; fold)
open import SPT.Foundation.Tree.LaxTranslation using
  ( Lax-Hole-Action-Cell; map-lax-tree; lax-translation-signature-relation
  ; map-lax-tree-cell )
open import SPT.Foundation.Tree.Fold.Relation.Heterogeneous using
  (Heterogeneous-Relational-Algebra; heterogeneous-fold-rel)

module _ {ℓj₁ ℓo₁ ℓp₁ ℓj₂ ℓo₂ ℓp₂ ℓx ℓy ℓd ℓe ℓm : Level}
  {Source-Judgment : Set ℓj₁} {Target-Judgment : Set ℓj₂}
  {on-judgment : Source-Judgment → Target-Judgment}
  {source : Signature-Over Source-Judgment ℓo₁ ℓp₁}
  {target : Signature-Over Target-Judgment ℓo₂ ℓp₂}
  (translation : Lax-Signature-Translation on-judgment source target)
  {X : Source-Judgment → Set ℓx} (Y : Target-Judgment → Set ℓy)
  (on-hole : (source-judgment : Source-Judgment) → X source-judgment →
    Y (on-judgment source-judgment))
  {D : Source-Judgment → Set ℓd} {E : Target-Judgment → Set ℓe}
  {Meaning-Cell : {source-judgment : Source-Judgment}
    {target-judgment : Target-Judgment} →
    on-judgment source-judgment ＝ target-judgment →
    D source-judgment → E target-judgment → Set ℓm}
  {source-algebra : Algebra (to-signature source) X D}
  {target-algebra : Algebra (to-signature target) Y E}
  (relational-algebra :
    Heterogeneous-Relational-Algebra
      (lax-translation-signature-relation translation)
      (Lax-Hole-Action-Cell on-judgment X Y on-hole) Meaning-Cell
      source-algebra target-algebra) where

  lax-tree-fold-natural : {source-judgment : Source-Judgment}
    (source-tree : Tree (to-signature source) X source-judgment) →
    Meaning-Cell refl (fold source-algebra source-tree)
      (fold target-algebra (map-lax-tree translation Y on-hole source-tree))
  lax-tree-fold-natural source-tree =
    heterogeneous-fold-rel relational-algebra
      (map-lax-tree-cell translation Y on-hole source-tree)
