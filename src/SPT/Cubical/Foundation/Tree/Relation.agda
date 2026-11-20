{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Tree.Relation where

-- A relation `R` between the holes of trees lifts to the trees: two trees are
-- related when they have the same operation at every node and related holes
-- (`TreeRel R`). Reflexivity, symmetry and composition lift from the holes, and
-- `map` respects lifted relations; the map laws hold up to `TreeRel _＝_`.
--
-- Given extensionality for the children of nodes, `TreeRel _＝_` is identity of
-- trees, and the map laws hold as identifications (`Extensional`). That
-- hypothesis, `ChildΠExt`, concerns only the children of nodes, so it is weaker
-- than function extensionality; it is a module parameter, not proved here.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Tree
open import SPT.Cubical.Foundation.Tree.Map using (map)

module _ {ℓj ℓo ℓp ℓx ℓy ℓr : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} {Y : Judgment S → Set ℓy}
  (R : {j : Judgment S} → X j → Y j → Set ℓr) where

  data TreeRel : {j : Judgment S} → Tree S X j → Tree S Y j →
    Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx ⊔ ℓy ⊔ ℓr) where
    hole-rel : {j : Judgment S} {x : X j} {y : Y j} → R x y →
      TreeRel (hole x) (hole y)
    node-rel : {j : Judgment S} {o : Op S j}
      {left : (p : Pos S o) → Tree S X (boundary S o p)}
      {right : (p : Pos S o) → Tree S Y (boundary S o p)} →
      ((p : Pos S o) → TreeRel (left p) (right p)) →
      TreeRel (node o left) (node o right)

ChildΠExt : {ℓj ℓo ℓp ℓx : Level} (S : Signature ℓj ℓo ℓp)
  (X : Judgment S → Set ℓx) → Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx)
ChildΠExt S X = {j : Judgment S} (o : Op S j)
  (left right : (p : Pos S o) → Tree S X (boundary S o p)) →
  ((p : Pos S o) → left p ＝ right p) → left ＝ right

------------------------------------------------------------------------
-- Reflexivity, symmetry and composition

module _ {ℓj ℓo ℓp ℓx ℓr : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} {R : {j : Judgment S} → X j → X j → Set ℓr}
  where

  rel-refl : ({j : Judgment S} (x : X j) → R x x) →
    {j : Judgment S} (tree : Tree S X j) → TreeRel R tree tree
  rel-refl reflR (hole x) = hole-rel (reflR x)
  rel-refl reflR (node o child) = node-rel (λ p → rel-refl reflR (child p))

module _ {ℓj ℓo ℓp ℓx ℓy ℓr ℓs : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} {Y : Judgment S → Set ℓy}
  {R : {j : Judgment S} → X j → Y j → Set ℓr}
  {R′ : {j : Judgment S} → Y j → X j → Set ℓs} where

  rel-sym : ({j : Judgment S} {x : X j} {y : Y j} → R x y → R′ y x) →
    {j : Judgment S} {left : Tree S X j} {right : Tree S Y j} →
    TreeRel R left right → TreeRel R′ right left
  rel-sym symR (hole-rel related) = hole-rel (symR related)
  rel-sym symR (node-rel related) = node-rel (λ p → rel-sym symR (related p))

module _ {ℓj ℓo ℓp ℓx ℓy ℓz ℓr ℓs ℓq : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} {Y : Judgment S → Set ℓy}
  {Z : Judgment S → Set ℓz} {R : {j : Judgment S} → X j → Y j → Set ℓr}
  {R′ : {j : Judgment S} → Y j → Z j → Set ℓs}
  {R″ : {j : Judgment S} → X j → Z j → Set ℓq} where

  rel-compose : ({j : Judgment S} {x : X j} {y : Y j} {z : Z j} →
      R x y → R′ y z → R″ x z) →
    {j : Judgment S} {left : Tree S X j} {middle : Tree S Y j}
    {right : Tree S Z j} →
    TreeRel R left middle → TreeRel R′ middle right →
    TreeRel R″ left right
  rel-compose compose (hole-rel left-related) (hole-rel right-related) =
    hole-rel (compose left-related right-related)
  rel-compose compose (node-rel left-related) (node-rel right-related) =
    node-rel (λ p →
      rel-compose compose (left-related p) (right-related p))

------------------------------------------------------------------------
-- Map congruence

module _ {ℓj ℓo ℓp ℓx ℓy ℓu ℓv ℓr ℓs : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} {Y : Judgment S → Set ℓy}
  {U : Judgment S → Set ℓu} {V : Judgment S → Set ℓv}
  {R : {j : Judgment S} → X j → Y j → Set ℓr}
  {R′ : {j : Judgment S} → U j → V j → Set ℓs} where

  map-cong : (f : (j : Judgment S) → X j → U j)
    (g : (j : Judgment S) → Y j → V j) →
    ({j : Judgment S} {x : X j} {y : Y j} → R x y → R′ (f j x) (g j y)) →
    {j : Judgment S} {left : Tree S X j} {right : Tree S Y j} →
    TreeRel R left right → TreeRel R′ (map f left) (map g right)
  map-cong f g congruence (hole-rel related) = hole-rel (congruence related)
  map-cong f g congruence (node-rel related) =
    node-rel (λ p → map-cong f g congruence (related p))

------------------------------------------------------------------------
-- The map laws, up to TreeRel _＝_

module _ {ℓj ℓo ℓp ℓx : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} where

  map-id-rel : {j : Judgment S} (tree : Tree S X j) →
    TreeRel _＝_ (map (λ j x → x) tree) tree
  map-id-rel (hole x) = hole-rel refl
  map-id-rel (node o child) = node-rel (λ p → map-id-rel (child p))

module _ {ℓj ℓo ℓp ℓx ℓy ℓz : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} {Y : Judgment S → Set ℓy}
  {Z : Judgment S → Set ℓz} where

  map-compose-rel : (f : (j : Judgment S) → X j → Y j)
    (g : (j : Judgment S) → Y j → Z j) {j : Judgment S}
    (tree : Tree S X j) →
    TreeRel _＝_ (map g (map f tree)) (map (λ j x → g j (f j x)) tree)
  map-compose-rel f g (hole x) = hole-rel refl
  map-compose-rel f g (node o child) =
    node-rel (λ p → map-compose-rel f g (child p))

------------------------------------------------------------------------
-- Identity of trees from extensionality for children

module Extensional {ℓj ℓo ℓp ℓx : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} (πext : ChildΠExt S X) where

  equality : {j : Judgment S} (left right : Tree S X j) →
    TreeRel _＝_ left right → left ＝ right
  equality (hole x) (hole y) (hole-rel related) = ap hole related
  equality (node o left) (node .o right) (node-rel related) =
    ap (node o)
      (πext o left right (λ p → equality (left p) (right p) (related p)))

  map-id : {j : Judgment S} (tree : Tree S X j) →
    map (λ j x → x) tree ＝ tree
  map-id tree = equality (map (λ j x → x) tree) tree (map-id-rel tree)

  map-compose : {ℓu ℓv : Level} {U : Judgment S → Set ℓu}
    {V : Judgment S → Set ℓv} (f : (j : Judgment S) → U j → V j)
    (g : (j : Judgment S) → V j → X j) {j : Judgment S}
    (tree : Tree S U j) →
    map g (map f tree) ＝ map (λ j x → g j (f j x)) tree
  map-compose f g tree =
    equality (map g (map f tree)) (map (λ j x → g j (f j x)) tree)
      (map-compose-rel f g tree)
