{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Tree.Descendant.Route where

-- The route of a descendant. A descendant of a node of a closed tree is the
-- subtree at a route below its root (descendant-route): an immediate child at
-- a position p is p followed by the root of that child, and a descendant
-- nested through the child at p is p followed by its route in that child.
--
--   Descendant c (j , t)   ⊢   Σ (ρ : Below t). subtree-at t (inr ρ) ＝ c.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Tree
open import SPT.Cubical.Foundation.Tree.Child using (HistoryNode; node-child)
open import SPT.Cubical.Foundation.Tree.Descendant using
  (Descendant; immediate; nested)
open import SPT.Cubical.Foundation.Tree.Routes using (Below; subtree-at)

module _ {ℓj ℓo ℓp : Level} {S : Signature ℓj ℓo ℓp} where

  -- Mathematical shape: c below d along a nonempty route of children is the
  -- subtree of d at that route.
  descendant-route : {c d : HistoryNode S} → Descendant c d →
    Σ (Below (pr₂ d)) (λ ρ → subtree-at (pr₂ d) (inr ρ) ＝ c)
  descendant-route (immediate (node-child p)) = (p , inl (lift ⋆)) , refl
  descendant-route (nested (node-child p) e) =
    (p , inr (pr₁ (descendant-route e))) , pr₂ (descendant-route e)
