{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.Generator.Tree.Relation where

-- Relations between trees over one signature, lifted from a relation on
-- their holes (TreeRel): related trees have the same operation at every
-- node and related holes.  Reflexivity, symmetry and composition lift from
-- the holes; map respects TreeRel; and, given extensionality for children,
-- TreeRel _≡_ is equality of trees (Extensional).

open import Agda.Primitive using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import SPT.Cubical.Core.Generator.Tree public
  using
    ( Signature
    ; Judgment
    ; Op
    ; Pos
    ; boundary
    ; Tree
    ; hole
    ; node
    )
open import SPT.Cubical.Core.Generator.Tree.Map
  using (map)

------------------------------------------------------------------------
-- Lifting a relation on holes

-- TreeRel R (hole x) (hole y)       from R x y,
-- TreeRel R (node o k) (node o l)   from Π p. TreeRel R (k p) (l p).
-- Both nodes carry the same operation o.
data TreeRel
    {ℓj ℓo ℓp ℓx ℓy ℓr : Level}
    {Σ : Signature ℓj ℓo ℓp}
    {X : Judgment Σ → Set ℓx}
    {Y : Judgment Σ → Set ℓy}
    (R :
      ∀ {j}
      → X j
      → Y j
      → Set ℓr)
    : ∀ {j}
    → Tree Σ X j
    → Tree Σ Y j
    → Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx ⊔ ℓy ⊔ ℓr)
  where
  hole-rel :
      ∀ {j}
        {x : X j}
        {y : Y j}
    → R x y
    → TreeRel R (hole x) (hole y)

  node-rel :
      ∀ {j}
        {o : Op Σ j}
        {left :
          (p : Pos Σ o)
          → Tree Σ X (boundary Σ o p)}
        {right :
          (p : Pos Σ o)
          → Tree Σ Y (boundary Σ o p)}
    → ((p : Pos Σ o)
        → TreeRel R (left p) (right p))
    → TreeRel R (node o left) (node o right)

------------------------------------------------------------------------
-- Reflexivity, symmetry and composition

rel-refl :
    ∀ {ℓj ℓo ℓp ℓx ℓr : Level}
      {Σ : Signature ℓj ℓo ℓp}
      {X : Judgment Σ → Set ℓx}
      {R :
        ∀ {j}
        → X j
        → X j
        → Set ℓr}
  → (reflR :
      ∀ {j}
      → (x : X j)
      → R x x)
  → ∀ {j}
  → (tree : Tree Σ X j)
  → TreeRel R tree tree
rel-refl reflR (hole x) =
  hole-rel (reflR x)
rel-refl reflR (node o child) =
  node-rel
    (λ p → rel-refl reflR (child p))

rel-sym :
    ∀ {ℓj ℓo ℓp ℓx ℓy ℓr ℓs : Level}
      {Σ : Signature ℓj ℓo ℓp}
      {X : Judgment Σ → Set ℓx}
      {Y : Judgment Σ → Set ℓy}
      {R :
        ∀ {j}
        → X j
        → Y j
        → Set ℓr}
      {S :
        ∀ {j}
        → Y j
        → X j
        → Set ℓs}
  → (symR :
      ∀ {j}
        {x : X j}
        {y : Y j}
      → R x y
      → S y x)
  → ∀ {j}
      {left : Tree Σ X j}
      {right : Tree Σ Y j}
  → TreeRel R left right
  → TreeRel S right left
rel-sym symR (hole-rel related) =
  hole-rel (symR related)
rel-sym symR (node-rel related) =
  node-rel
    (λ p → rel-sym symR (related p))

rel-compose :
    ∀ {ℓj ℓo ℓp ℓx ℓy ℓz ℓr ℓs ℓq : Level}
      {Σ : Signature ℓj ℓo ℓp}
      {X : Judgment Σ → Set ℓx}
      {Y : Judgment Σ → Set ℓy}
      {Z : Judgment Σ → Set ℓz}
      {R :
        ∀ {j}
        → X j
        → Y j
        → Set ℓr}
      {S :
        ∀ {j}
        → Y j
        → Z j
        → Set ℓs}
      {Q :
        ∀ {j}
        → X j
        → Z j
        → Set ℓq}
  → (compose :
      ∀ {j}
        {x : X j}
        {y : Y j}
        {z : Z j}
      → R x y
      → S y z
      → Q x z)
  → ∀ {j}
      {left : Tree Σ X j}
      {middle : Tree Σ Y j}
      {right : Tree Σ Z j}
  → TreeRel R left middle
  → TreeRel S middle right
  → TreeRel Q left right
rel-compose compose
  (hole-rel left-related)
  (hole-rel right-related) =
    hole-rel (compose left-related right-related)
rel-compose compose
  (node-rel left-related)
  (node-rel right-related) =
    node-rel
      (λ p →
        rel-compose compose
          (left-related p)
          (right-related p))

------------------------------------------------------------------------
-- Map congruence

map-cong :
    ∀ {ℓj ℓo ℓp ℓx ℓy ℓu ℓv ℓr ℓs : Level}
      {Σ : Signature ℓj ℓo ℓp}
      {X : Judgment Σ → Set ℓx}
      {Y : Judgment Σ → Set ℓy}
      {U : Judgment Σ → Set ℓu}
      {V : Judgment Σ → Set ℓv}
      {R :
        ∀ {j}
        → X j
        → Y j
        → Set ℓr}
      {S :
        ∀ {j}
        → U j
        → V j
        → Set ℓs}
      (f :
        (j : Judgment Σ)
        → X j
        → U j)
      (g :
        (j : Judgment Σ)
        → Y j
        → V j)
  → (cong :
      ∀ {j}
        {x : X j}
        {y : Y j}
      → R x y
      → S (f j x) (g j y))
  → ∀ {j}
      {left : Tree Σ X j}
      {right : Tree Σ Y j}
  → TreeRel R left right
  → TreeRel S (map f left) (map g right)
map-cong f g cong (hole-rel related) =
  hole-rel (cong related)
map-cong f g cong (node-rel related) =
  node-rel
    (λ p → map-cong f g cong (related p))

------------------------------------------------------------------------
-- The map laws, up to TreeRel _≡_

map-id-rel :
    ∀ {ℓj ℓo ℓp ℓx : Level}
      {Σ : Signature ℓj ℓo ℓp}
      {X : Judgment Σ → Set ℓx}
      {j : Judgment Σ}
  → (tree : Tree Σ X j)
  → TreeRel _≡_
      (map (λ j x → x) tree)
      tree
map-id-rel (hole x) =
  hole-rel refl
map-id-rel (node o child) =
  node-rel
    (λ p → map-id-rel (child p))

map-compose-rel :
    ∀ {ℓj ℓo ℓp ℓx ℓy ℓz : Level}
      {Σ : Signature ℓj ℓo ℓp}
      {X : Judgment Σ → Set ℓx}
      {Y : Judgment Σ → Set ℓy}
      {Z : Judgment Σ → Set ℓz}
      (f :
        (j : Judgment Σ)
        → X j
        → Y j)
      (g :
        (j : Judgment Σ)
        → Y j
        → Z j)
      {j : Judgment Σ}
  → (tree : Tree Σ X j)
  → TreeRel _≡_
      (map g (map f tree))
      (map (λ j x → g j (f j x)) tree)
map-compose-rel f g (hole x) =
  hole-rel refl
map-compose-rel f g (node o child) =
  node-rel
    (λ p → map-compose-rel f g (child p))

------------------------------------------------------------------------
-- Equality from extensionality for children

-- Extensionality for the children of a node:
--
--   ChildΠExt Σ X = Π o (k l : Π p. Tree Σ X (boundary o p)).
--                     (Π p. k p ≡ l p) → k ≡ l.
--
-- It is a hypothesis of the module below, not proved here, and weaker than
-- function extensionality: it concerns only the children of nodes.

ChildΠExt :
    ∀ {ℓj ℓo ℓp ℓx : Level}
  → (Σ : Signature ℓj ℓo ℓp)
  → (X : Judgment Σ → Set ℓx)
  → Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx)
ChildΠExt Σ X =
  ∀ {j}
  → (o : Op Σ j)
  → (left right :
      (p : Pos Σ o)
      → Tree Σ X (boundary Σ o p))
  → ((p : Pos Σ o) → left p ≡ right p)
  → left ≡ right

-- Given ChildΠExt: TreeRel _≡_ k l → k ≡ l (equality), so the map laws
-- above hold as equalities (map-id, map-compose).

module Extensional
    {ℓj ℓo ℓp ℓx : Level}
    {Σ : Signature ℓj ℓo ℓp}
    {X : Judgment Σ → Set ℓx}
    (πext : ChildΠExt Σ X)
  where

  equality :
      ∀ {j}
        {left right : Tree Σ X j}
    → TreeRel _≡_ left right
    → left ≡ right
  equality (hole-rel related) =
    cong hole related
  equality
    (node-rel {o = o} {left = left} {right = right} related) =
      cong
        (node o)
        (πext o left right
          (λ p → equality (related p)))

  map-id :
      ∀ {j}
    → (tree : Tree Σ X j)
    → map (λ j x → x) tree ≡ tree
  map-id tree =
    equality (map-id-rel tree)

  map-compose :
      ∀ {ℓu ℓv : Level}
        {U : Judgment Σ → Set ℓu}
        {V : Judgment Σ → Set ℓv}
    → (f :
        (j : Judgment Σ)
        → U j
        → V j)
    → (g :
        (j : Judgment Σ)
        → V j
        → X j)
    → ∀ {j}
    → (tree : Tree Σ U j)
    → map g (map f tree)
        ≡ map (λ j x → g j (f j x)) tree
  map-compose f g tree =
    equality (map-compose-rel f g tree)
