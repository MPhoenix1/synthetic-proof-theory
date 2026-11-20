{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Tree.Substitution where

-- Substitution for the holes of open trees over one signature. A tree for each
-- hole payload replaces every hole, and every node keeps its operation and its
-- positions (`bind`):
--
--   bind f (hole x) = f j x,   bind f (node o child) = node o (bind f ∘ child).
--
-- Both equations hold by computation (`bind-hole`, `bind-node`). Substitution
-- respects lifted relations (`bind-cong`), and its right unit and
-- associativity laws hold up to `TreeRel _＝_`, with no identification of
-- functions:
--
--   bind (λ j x → hole x) t ∼ t,
--   bind g (bind f t) ∼ bind (λ j x → bind g (f j x)) t
--
-- (`bind-right-unit-rel`, `bind-assoc-rel`); under extensionality for the
-- children of nodes, passed explicitly, they are identifications
-- (`bind-right-unit`, `bind-assoc`). The left unit law is `bind-hole`.

open import SPT.Base
open import SPT.Foundation.Tree
open import SPT.Foundation.Tree.Relation using
  (TreeRel; hole-rel; node-rel; rel-refl; ChildΠExt; module Extensional)

module _ {ℓj ℓo ℓp ℓx ℓy : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} {Y : Judgment S → Set ℓy} where

  bind : ((j : Judgment S) → X j → Tree S Y j) → {j : Judgment S} →
    Tree S X j → Tree S Y j
  bind f (hole {j} x) = f j x
  bind f (node o child) = node o (λ p → bind f (child p))

  bind-hole : (f : (j : Judgment S) → X j → Tree S Y j) {j : Judgment S}
    (x : X j) → bind f (hole x) ＝ f j x
  bind-hole f x = refl

  bind-node : (f : (j : Judgment S) → X j → Tree S Y j) {j : Judgment S}
    (o : Op S j) (child : (p : Pos S o) → Tree S X (boundary S o p)) →
    bind f (node o child) ＝ node o (λ p → bind f (child p))
  bind-node f o child = refl

------------------------------------------------------------------------
-- Congruence

-- Related trees with related replacements of related holes give related
-- substituted trees; every operation and position is kept literally.

module _ {ℓj ℓo ℓp ℓx ℓy ℓu ℓv ℓr ℓs : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} {Y : Judgment S → Set ℓy}
  {U : Judgment S → Set ℓu} {V : Judgment S → Set ℓv}
  {R : {j : Judgment S} → X j → Y j → Set ℓr}
  {R′ : {j : Judgment S} → U j → V j → Set ℓs} where

  bind-cong : (f : (j : Judgment S) → X j → Tree S U j)
    (g : (j : Judgment S) → Y j → Tree S V j) →
    ({j : Judgment S} {x : X j} {y : Y j} → R x y →
      TreeRel R′ (f j x) (g j y)) →
    {j : Judgment S} {left : Tree S X j} {right : Tree S Y j} →
    TreeRel R left right → TreeRel R′ (bind f left) (bind g right)
  bind-cong f g on-holes (hole-rel related) = on-holes related
  bind-cong f g on-holes (node-rel related) =
    node-rel (λ p → bind-cong f g on-holes (related p))

------------------------------------------------------------------------
-- Unit and associativity, up to TreeRel _＝_

module _ {ℓj ℓo ℓp ℓx : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} where

  bind-right-unit-rel : {j : Judgment S} (tree : Tree S X j) →
    TreeRel _＝_ (bind (λ j x → hole x) tree) tree
  bind-right-unit-rel (hole x) = hole-rel refl
  bind-right-unit-rel (node o child) =
    node-rel (λ p → bind-right-unit-rel (child p))

  bind-right-unit : ChildΠExt S X → {j : Judgment S} (tree : Tree S X j) →
    bind (λ j x → hole x) tree ＝ tree
  bind-right-unit πext tree =
    Extensional.equality πext (bind (λ j x → hole x) tree) tree
      (bind-right-unit-rel tree)

module _ {ℓj ℓo ℓp ℓx ℓy ℓz : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} {Y : Judgment S → Set ℓy}
  {Z : Judgment S → Set ℓz} where

  bind-assoc-rel : (f : (j : Judgment S) → X j → Tree S Y j)
    (g : (j : Judgment S) → Y j → Tree S Z j) {j : Judgment S}
    (tree : Tree S X j) →
    TreeRel _＝_ (bind g (bind f tree)) (bind (λ j x → bind g (f j x)) tree)
  bind-assoc-rel f g (hole {j} x) = rel-refl (λ z → refl) (bind g (f j x))
  bind-assoc-rel f g (node o child) =
    node-rel (λ p → bind-assoc-rel f g (child p))

  bind-assoc : ChildΠExt S Z → (f : (j : Judgment S) → X j → Tree S Y j)
    (g : (j : Judgment S) → Y j → Tree S Z j) {j : Judgment S}
    (tree : Tree S X j) →
    bind g (bind f tree) ＝ bind (λ j x → bind g (f j x)) tree
  bind-assoc πext f g tree =
    Extensional.equality πext (bind g (bind f tree))
      (bind (λ j x → bind g (f j x)) tree) (bind-assoc-rel f g tree)
