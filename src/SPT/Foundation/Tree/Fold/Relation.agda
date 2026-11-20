{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Tree.Fold.Relation where

-- Relational compatibility of tree algebras over one signature. For a
-- relation R between the holes of two families and a relation C between
-- the values of two algebras, a relational algebra preserves the relation
-- at holes and at every operation, pointwise at its children
-- (`Relational-Algebra`):
--
--   R x y → C (on-hole A x) (on-hole B y),
--   (Π p. C (d p) (e p)) → C (on-node A o d) (on-node B o e).
--
-- An algebra whose node action is congruent (Tree.Fold's
-- `Congruent-Node-Action`) is relational over identity at both holes and
-- values (`congruent-relational-algebra`).
--
-- Trees related by R have related folds (`fold-rel`), by structural
-- recursion on the related trees. The comparison is pointwise at the
-- children of a node, so no equality of child functions and no function
-- extensionality is used.

open import SPT.Base
open import SPT.Foundation.Tree using
  (Signature; Judgment; Op; Pos; boundary; Tree)
open import SPT.Foundation.Tree.Fold using
  (Algebra; on-hole; on-node; Congruent-Node-Action; fold)
open import SPT.Foundation.Tree.Relation using (TreeRel; hole-rel; node-rel)

------------------------------------------------------------------------
-- Relational algebras

-- The record only states the two preservation clauses; it supplies no
-- equality of algebras, folds or child functions.

record Relational-Algebra {ℓj ℓo ℓp ℓx ℓy ℓd ℓe ℓr ℓc : Level}
  {S : Signature ℓj ℓo ℓp} {X : Judgment S → Set ℓx}
  {Y : Judgment S → Set ℓy} {D : Judgment S → Set ℓd}
  {E : Judgment S → Set ℓe} (R : {j : Judgment S} → X j → Y j → Set ℓr)
  (C : {j : Judgment S} → D j → E j → Set ℓc)
  (left-algebra : Algebra S X D) (right-algebra : Algebra S Y E)
  : Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx ⊔ ℓy ⊔ ℓd ⊔ ℓe ⊔ ℓr ⊔ ℓc) where
  field
    on-hole-rel : {j : Judgment S} {x : X j} {y : Y j} → R x y →
      C (on-hole left-algebra x) (on-hole right-algebra y)
    on-node-rel : {j : Judgment S} (o : Op S j)
      {left : (p : Pos S o) → D (boundary S o p)}
      {right : (p : Pos S o) → E (boundary S o p)} →
      ((p : Pos S o) → C (left p) (right p)) →
      C (on-node left-algebra o left) (on-node right-algebra o right)

open Relational-Algebra public

-- A congruent node action relates an algebra to itself over identity; the
-- hole clause is the action of the hole map on identifications.

module _ {ℓj ℓo ℓp ℓx ℓd : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} {D : Judgment S → Set ℓd}
  (algebra : Algebra S X D) where

  congruent-relational-algebra :
    Congruent-Node-Action D (on-node algebra) →
    Relational-Algebra _＝_ _＝_ algebra algebra
  congruent-relational-algebra congruence = record
    { on-hole-rel = ap (on-hole algebra)
    ; on-node-rel = congruence
    }

------------------------------------------------------------------------
-- Related trees have related folds

module _ {ℓj ℓo ℓp ℓx ℓy ℓd ℓe ℓr ℓc : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} {Y : Judgment S → Set ℓy}
  {D : Judgment S → Set ℓd} {E : Judgment S → Set ℓe}
  {R : {j : Judgment S} → X j → Y j → Set ℓr}
  {C : {j : Judgment S} → D j → E j → Set ℓc}
  {left-algebra : Algebra S X D} {right-algebra : Algebra S Y E}
  (relational-algebra :
    Relational-Algebra R C left-algebra right-algebra) where

  fold-rel : {j : Judgment S} {left : Tree S X j} {right : Tree S Y j} →
    TreeRel R left right →
    C (fold left-algebra left) (fold right-algebra right)
  fold-rel (hole-rel related) = on-hole-rel relational-algebra related
  fold-rel (node-rel {_} {o} related) =
    on-node-rel relational-algebra o (λ p → fold-rel (related p))
