{-# OPTIONS --safe --without-K #-}

module SPT.IR.Description where

-- Dybjer–Setzer descriptions with arities of level s (`DS`, `Desc`): ι
-- gives an output, σ a small sum, and δ an A-indexed family of recursive
-- inputs whose decodings select the continuation. An indexed family is a
-- carrier of any level κ with a decoding (`Indexed`); a description acts on
-- it by its shapes and their outputs (`Shape`, `Mark`), at the level s ⊔ κ.
-- Nothing here imports induction–recursion, and nothing built on it does
-- except the native induction–recursive types of Universal and Indexed.

open import SPT.Base

------------------------------------------------------------------------
-- Descriptions

-- Mathematical shape:
--
--   ι : E → DS D E
--   σ : (A : Set s) → (A → DS D E) → DS D E
--   δ : (A : Set s) → ((A → D) → DS D E) → DS D E.

data DS {s d e : Level} (D : Set d) (E : Set e) :
  Set (lsuc s ⊔ d ⊔ e) where
  ι : E → DS {s = s} D E
  σ : (A : Set s) → (A → DS {s = s} D E) → DS {s = s} D E
  δ : (A : Set s) → ((A → D) → DS {s = s} D E) → DS {s = s} D E

Desc : {s d : Level} → Set d → Set (lsuc s ⊔ d)
Desc {s} D = DS {s = s} D D

------------------------------------------------------------------------
-- Indexed families and the action of a description

record Indexed {d : Level} (κ : Level) (D : Set d) : Set (lsuc κ ⊔ d) where
  constructor indexed
  field
    carrier : Set κ
    index : carrier → D

open Indexed public

-- Mathematical shape:
--
--   Shape (ι e) Z = 𝟙
--   Shape (σ A f) Z = Σ (a : A). Shape (f a) Z
--   Shape (δ A F) Z = Σ (g : A → carrier Z). Shape (F (index Z ∘ g)) Z.

Shape :
  {s κ d e : Level} {D : Set d} {E : Set e} → DS {s = s} D E
  → Indexed κ D → Set (s ⊔ κ)
Shape {s} {κ} (ι e) Z = Lift (s ⊔ κ) 𝟙
Shape (σ A f) Z = Σ A (λ a → Shape (f a) Z)
Shape (δ A F) Z =
  Σ (A → carrier Z) (λ g → Shape (F (λ a → index Z (g a))) Z)

Mark :
  {s κ d e : Level} {D : Set d} {E : Set e} (γ : DS {s = s} D E)
  (Z : Indexed κ D) → Shape γ Z → E
Mark (ι e) Z _ = e
Mark (σ A f) Z (a , x) = Mark (f a) Z x
Mark (δ A F) Z (g , x) = Mark (F (λ a → index Z (g a))) Z x
