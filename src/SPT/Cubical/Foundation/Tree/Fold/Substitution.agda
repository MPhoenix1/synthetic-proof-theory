{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Tree.Fold.Substitution where

-- Relational fold compatibility with substitution. The fold of a tree
-- after `bind f` is related to the fold of the tree itself when the fold of
-- every replacement f j x is related to the value of its hole, and the two
-- node actions preserve the relation at each literal operation
-- (`bind-fold-rel`):
--
--   (Π x. C (fold A (f j x)) (on-hole B x)) →
--   (Π o. (Π p. C (d p) (e p)) → C (on-node A o d) (on-node B o e)) →
--   Π t. C (fold A (bind f t)) (fold B t).
--
-- With one algebra and C the identification, this is the fusion of a fold
-- with substitution; with a relation that changes environments, it is a
-- substitution lemma. The comparison is pointwise at the children of a
-- node, so no function extensionality is used.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Tree using
  (Signature; Judgment; Op; Pos; boundary; Tree; hole; node)
open import SPT.Cubical.Foundation.Tree.Fold
  using (Algebra; on-hole; on-node; fold)
open import SPT.Cubical.Foundation.Tree.Substitution using (bind)

module _ {ℓj ℓo ℓp ℓx ℓy ℓd ℓe ℓc : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} {Y : Judgment S → Set ℓy}
  {D : Judgment S → Set ℓd} {E : Judgment S → Set ℓe}
  (C : {j : Judgment S} → D j → E j → Set ℓc)
  (left-algebra : Algebra S Y D) (right-algebra : Algebra S X E)
  (f : (j : Judgment S) → X j → Tree S Y j)
  (holes : {j : Judgment S} (x : X j) →
    C (fold left-algebra (f j x)) (on-hole right-algebra x))
  (nodes : {j : Judgment S} (o : Op S j)
    {left : (p : Pos S o) → D (boundary S o p)}
    {right : (p : Pos S o) → E (boundary S o p)} →
    ((p : Pos S o) → C (left p) (right p)) →
    C (on-node left-algebra o left) (on-node right-algebra o right))
  where

  bind-fold-rel : {j : Judgment S} (t : Tree S X j) →
    C (fold left-algebra (bind f t)) (fold right-algebra t)
  bind-fold-rel (hole x) = holes x
  bind-fold-rel (node o child) = nodes o (λ p → bind-fold-rel (child p))
