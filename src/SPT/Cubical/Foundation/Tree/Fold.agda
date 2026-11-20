{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Tree.Fold where

-- An algebra for a signature interprets each hole, and each operation on
-- interpreted children:
--
--   on-hole : X j → D j,
--   on-node : (o : Op j) → (Π p. D (∂ o p)) → D j.
--
-- A node action is congruent when children agreeing at every position give
-- the same value (`Congruent-Node-Action`); this is the one statement of
-- congruence for node actions, and Fold.Initiality's and Fold.Relation's
-- forms are derived from it.
--
-- Induction proves a property of every tree from its holes and from each
-- node given its children. The fold of a tree into an algebra is induction
-- at the constant motive of the carrier, the algebra's node operation read
-- as a method there (`node-method`), so every theorem about induction is
-- one about folds. Both compute on holes and nodes by `refl`.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Tree

------------------------------------------------------------------------
-- Algebras

record Algebra {ℓj ℓo ℓp ℓx ℓd : Level} (S : Signature ℓj ℓo ℓp)
  (X : Judgment S → Set ℓx) (D : Judgment S → Set ℓd) :
  Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx ⊔ ℓd) where
  field
    on-hole : {j : Judgment S} → X j → D j
    on-node : {j : Judgment S} (o : Op S j) →
      ((p : Pos S o) → D (boundary S o p)) → D j

open Algebra public

-- Children agreeing at every position give the same value.

module _ {ℓj ℓo ℓp ℓd : Level} {S : Signature ℓj ℓo ℓp}
  (D : Judgment S → Set ℓd) where

  Congruent-Node-Action :
    ({j : Judgment S} (o : Op S j) →
      ((p : Pos S o) → D (boundary S o p)) → D j) →
    Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓd)
  Congruent-Node-Action α =
    {j : Judgment S} (o : Op S j)
    {left right : (p : Pos S o) → D (boundary S o p)} →
    ((p : Pos S o) → left p ＝ right p) → α o left ＝ α o right

------------------------------------------------------------------------
-- Induction

module _ {ℓj ℓo ℓp ℓx ℓm : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} (P : (j : Judgment S) → Tree S X j → Set ℓm)
  (on-holeᴾ : {j : Judgment S} (x : X j) → P j (hole x))
  (on-nodeᴾ : {j : Judgment S} (o : Op S j)
    (child : (p : Pos S o) → Tree S X (boundary S o p)) →
    ((p : Pos S o) → P (boundary S o p) (child p)) → P j (node o child))
  where

  induction : {j : Judgment S} (tree : Tree S X j) → P j tree
  induction (hole x) = on-holeᴾ x
  induction (node o child) = on-nodeᴾ o child (λ p → induction (child p))

  induction-hole : {j : Judgment S} (x : X j) →
    induction (hole x) ＝ on-holeᴾ x
  induction-hole x = refl

  induction-node : {j : Judgment S} (o : Op S j)
    (child : (p : Pos S o) → Tree S X (boundary S o p)) →
    induction (node o child)
      ＝ on-nodeᴾ o child (λ p → induction (child p))
  induction-node o child = refl

------------------------------------------------------------------------
-- Folds

-- The node method of an algebra is its node operation, a method of
-- induction at the constant motive of its carrier that does not read the
-- children's trees; the fold is induction with it.

module _ {ℓj ℓo ℓp ℓx ℓd : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} {D : Judgment S → Set ℓd} where

  node-method : Algebra S X D → {j : Judgment S} (o : Op S j)
    (child : (p : Pos S o) → Tree S X (boundary S o p)) →
    ((p : Pos S o) → D (boundary S o p)) → D j
  node-method algebra o child values = on-node algebra o values

  fold : Algebra S X D → {j : Judgment S} → Tree S X j → D j
  fold algebra =
    induction (λ j tree → D j) (on-hole algebra) (node-method algebra)

  fold-hole : (algebra : Algebra S X D) {j : Judgment S} (x : X j) →
    fold algebra (hole x) ＝ on-hole algebra x
  fold-hole algebra x = refl

  fold-node : (algebra : Algebra S X D) {j : Judgment S} (o : Op S j)
    (child : (p : Pos S o) → Tree S X (boundary S o p)) →
    fold algebra (node o child)
      ＝ on-node algebra o (λ p → fold algebra (child p))
  fold-node algebra o child = refl
