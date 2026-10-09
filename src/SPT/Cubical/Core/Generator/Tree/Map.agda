{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.Generator.Tree.Map where

-- Relabelling the holes of a tree.

open import Agda.Primitive using (Level)
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
-- Maps

-- map f : Tree Σ X j → Tree Σ Y j, for f : Π j. X j → Y j, changes only
-- the holes.
map :
    ∀ {ℓj ℓo ℓp ℓx ℓy : Level}
      {Σ : Signature ℓj ℓo ℓp}
      {X : Judgment Σ → Set ℓx}
      {Y : Judgment Σ → Set ℓy}
  → ((j : Judgment Σ) → X j → Y j)
  → ∀ {j}
  → Tree Σ X j
  → Tree Σ Y j
map f (hole {j} x) =
  hole (f j x)
map f (node o child) =
  node o (λ p → map f (child p))

-- Both computation rules hold by refl.

map-hole :
    ∀ {ℓj ℓo ℓp ℓx ℓy : Level}
      {Σ : Signature ℓj ℓo ℓp}
      {X : Judgment Σ → Set ℓx}
      {Y : Judgment Σ → Set ℓy}
      (f : (j : Judgment Σ) → X j → Y j)
      {j : Judgment Σ}
      (x : X j)
  → map f (hole {Σ = Σ} {X = X} x)
      ≡ hole {Σ = Σ} {X = Y} (f j x)
map-hole f x =
  refl

map-node :
    ∀ {ℓj ℓo ℓp ℓx ℓy : Level}
      {Σ : Signature ℓj ℓo ℓp}
      {X : Judgment Σ → Set ℓx}
      {Y : Judgment Σ → Set ℓy}
      (f : (j : Judgment Σ) → X j → Y j)
      {j : Judgment Σ}
      (o : Op Σ j)
      (child :
        (p : Pos Σ o)
        → Tree Σ X (boundary Σ o p))
  → map f (node {Σ = Σ} {X = X} o child)
      ≡ node {Σ = Σ} {X = Y} o
          (λ p → map f (child p))
map-node f o child =
  refl
