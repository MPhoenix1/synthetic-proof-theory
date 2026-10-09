{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.Generator.Tree.Fold where

-- Folds of trees into an algebra, and dependent induction on trees, each
-- with its computation rules.

open import Agda.Primitive using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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

------------------------------------------------------------------------
-- Algebras

-- An algebra interprets each hole, and each operation on interpreted
-- children:
--
--   on-hole : X j → D j,   on-node : (o : Op j) → (Π p. D (∂ o p)) → D j.
record Algebra
    {ℓj ℓo ℓp ℓx ℓd : Level}
    (Σ : Signature ℓj ℓo ℓp)
    (X : Judgment Σ → Set ℓx)
    (D : Judgment Σ → Set ℓd)
    : Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx ⊔ ℓd)
  where
  field
    on-hole :
        ∀ {j}
      → X j
      → D j

    on-node :
        ∀ {j}
      → (o : Op Σ j)
      → ((p : Pos Σ o) → D (boundary Σ o p))
      → D j

open Algebra public

------------------------------------------------------------------------
-- Folds

-- fold A : Tree Σ X j → D j.  It computes on holes and nodes (fold-hole,
-- fold-node, both refl).
fold :
    ∀ {ℓj ℓo ℓp ℓx ℓd : Level}
      {Σ : Signature ℓj ℓo ℓp}
      {X : Judgment Σ → Set ℓx}
      {D : Judgment Σ → Set ℓd}
  → Algebra Σ X D
  → ∀ {j}
  → Tree Σ X j
  → D j
fold algebra (hole x) =
  on-hole algebra x
fold algebra (node o child) =
  on-node algebra o (λ p → fold algebra (child p))

fold-hole :
    ∀ {ℓj ℓo ℓp ℓx ℓd : Level}
      {Σ : Signature ℓj ℓo ℓp}
      {X : Judgment Σ → Set ℓx}
      {D : Judgment Σ → Set ℓd}
      (algebra : Algebra Σ X D)
      {j : Judgment Σ}
      (x : X j)
  → fold algebra (hole {Σ = Σ} {X = X} x)
      ≡ on-hole algebra x
fold-hole algebra x =
  refl

fold-node :
    ∀ {ℓj ℓo ℓp ℓx ℓd : Level}
      {Σ : Signature ℓj ℓo ℓp}
      {X : Judgment Σ → Set ℓx}
      {D : Judgment Σ → Set ℓd}
      (algebra : Algebra Σ X D)
      {j : Judgment Σ}
      (o : Op Σ j)
      (child :
        (p : Pos Σ o)
        → Tree Σ X (boundary Σ o p))
  → fold algebra (node {Σ = Σ} {X = X} o child)
      ≡ on-node algebra o
          (λ p → fold algebra (child p))
fold-node algebra o child =
  refl

------------------------------------------------------------------------
-- Dependent induction

-- From P (hole x), and P (node o child) given P (child p) for every p,
-- conclude P t for every tree t.  It computes on holes and nodes
-- (induction-hole, induction-node).
induction :
    ∀ {ℓj ℓo ℓp ℓx ℓm : Level}
      {Σ : Signature ℓj ℓo ℓp}
      {X : Judgment Σ → Set ℓx}
      (P :
        (j : Judgment Σ)
        → Tree Σ X j
        → Set ℓm)
  → (on-holeᴾ :
        ∀ {j}
        (x : X j)
      → P j (hole {Σ = Σ} {X = X} x))
  → (on-nodeᴾ :
        ∀ {j}
        (o : Op Σ j)
        (child :
          (p : Pos Σ o)
          → Tree Σ X (boundary Σ o p))
      → ((p : Pos Σ o)
          → P (boundary Σ o p) (child p))
      → P j (node {Σ = Σ} {X = X} o child))
  → ∀ {j}
  → (tree : Tree Σ X j)
  → P j tree
induction P on-holeᴾ on-nodeᴾ (hole x) =
  on-holeᴾ x
induction P on-holeᴾ on-nodeᴾ (node o child) =
  on-nodeᴾ o child
    (λ p → induction P on-holeᴾ on-nodeᴾ (child p))

induction-hole :
    ∀ {ℓj ℓo ℓp ℓx ℓm : Level}
      {Σ : Signature ℓj ℓo ℓp}
      {X : Judgment Σ → Set ℓx}
      (P :
        (j : Judgment Σ)
        → Tree Σ X j
        → Set ℓm)
      (on-holeᴾ :
        ∀ {j}
        (x : X j)
        → P j (hole {Σ = Σ} {X = X} x))
      (on-nodeᴾ :
        ∀ {j}
        (o : Op Σ j)
        (child :
          (p : Pos Σ o)
          → Tree Σ X (boundary Σ o p))
        → ((p : Pos Σ o)
            → P (boundary Σ o p) (child p))
        → P j (node {Σ = Σ} {X = X} o child))
      {j : Judgment Σ}
      (x : X j)
  → induction P on-holeᴾ on-nodeᴾ
      (hole {Σ = Σ} {X = X} x)
      ≡ on-holeᴾ x
induction-hole P on-holeᴾ on-nodeᴾ x =
  refl

induction-node :
    ∀ {ℓj ℓo ℓp ℓx ℓm : Level}
      {Σ : Signature ℓj ℓo ℓp}
      {X : Judgment Σ → Set ℓx}
      (P :
        (j : Judgment Σ)
        → Tree Σ X j
        → Set ℓm)
      (on-holeᴾ :
        ∀ {j}
        (x : X j)
        → P j (hole {Σ = Σ} {X = X} x))
      (on-nodeᴾ :
        ∀ {j}
        (o : Op Σ j)
        (child :
          (p : Pos Σ o)
          → Tree Σ X (boundary Σ o p))
        → ((p : Pos Σ o)
            → P (boundary Σ o p) (child p))
        → P j (node {Σ = Σ} {X = X} o child))
      {j : Judgment Σ}
      (o : Op Σ j)
      (child :
        (p : Pos Σ o)
        → Tree Σ X (boundary Σ o p))
  → induction P on-holeᴾ on-nodeᴾ
      (node {Σ = Σ} {X = X} o child)
      ≡ on-nodeᴾ o child
          (λ p →
            induction P on-holeᴾ on-nodeᴾ (child p))
induction-node P on-holeᴾ on-nodeᴾ o child =
  refl
