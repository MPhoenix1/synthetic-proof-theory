{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.Generator.Tree.W where

-- W-types as closed trees at one judgment: labels a : A branching over
-- B a (Branching), with induction from Fold.

open import Agda.Primitive using (Level; lzero; _⊔_)
open import Data.Empty.Polymorphic using (⊥-elim)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import SPT.Cubical.Core.Generator.Tree as Tree
import SPT.Cubical.Core.Generator.Tree.Fold as Fold

module Branching {ℓa ℓb : Level} (A : Set ℓa) (B : A → Set ℓb) where

  signature : Tree.Signature lzero ℓa ℓb
  signature = record
    { Judgment = ⊤ {lzero}
    ; Op = λ _ → A
    ; Pos = B
    ; boundary = λ _ _ → tt
    }

  Open : ∀ {ℓx} → Set ℓx → Set (ℓa ⊔ ℓb ⊔ ℓx)
  Open X = Tree.Tree signature (λ _ → X) tt

  Closed : Set (ℓa ⊔ ℓb)
  Closed = Tree.History signature tt

  ind : ∀ {ν} (P : Closed → Set ν)
    → ((a : A) (k : B a → Closed)
      → ((b : B a) → P (k b)) → P (Tree.node a k))
    → (t : Closed) → P t
  ind P step = Fold.induction (λ _ → P) ⊥-elim step

  ind-β : ∀ {ν} (P : Closed → Set ν)
    (step : (a : A) (k : B a → Closed)
      → ((b : B a) → P (k b)) → P (Tree.node a k))
    (a : A) (k : B a → Closed)
    → ind P step (Tree.node a k)
      ≡ step a k (λ b → ind P step (k b))
  ind-β P step a k = refl
