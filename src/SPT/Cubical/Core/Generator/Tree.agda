{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.Generator.Tree where

-- Open trees over an indexed signature, with holes carrying a payload, and
-- closed histories, the trees without holes.

open import Agda.Primitive using (Level; lzero; _⊔_)
open import Data.Empty.Polymorphic using (⊥)

open import SPT.Cubical.Core.Generator.Signature public
  using (Signature; Judgment; Op; Pos; boundary)

------------------------------------------------------------------------
-- Open trees

--   Tree Σ X j ≅ X(j) ⊎ Σ(o : Op(j)). Π(p : Pos(o)). Tree Σ X (boundary(o,p)).
--
-- Branching may be empty, finite or infinite.
data Tree
    {ℓj ℓo ℓp ℓx : Level}
    (Σ : Signature ℓj ℓo ℓp)
    (X : Judgment Σ → Set ℓx)
    : Judgment Σ
    → Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx)
  where
  hole :
      ∀ {j}
    → X j
    → Tree Σ X j

  node :
      ∀ {j}
    → (o : Op Σ j)
    → ((p : Pos Σ o) → Tree Σ X (boundary Σ o p))
    → Tree Σ X j

------------------------------------------------------------------------
-- Closed histories

-- Closed histories: History Σ j = Tree Σ (λ _ → ⊥) j.
History :
    ∀ {ℓj ℓo ℓp}
    (Σ : Signature ℓj ℓo ℓp)
  → Judgment Σ
  → Set (ℓj ⊔ ℓo ⊔ ℓp)
History Σ =
  Tree Σ (λ _ → ⊥ {lzero})
