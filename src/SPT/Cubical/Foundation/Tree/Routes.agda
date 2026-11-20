{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Tree.Routes where

-- Routes inside one open tree: the root, or a position of the root node
-- followed by a route of the child there; a hole has nothing below it
-- (`Below`, `Routes`). Only the level of the positions enters: judgments,
-- operations and hole payloads stay in the tree.
--
--   Below (hole x)   = 𝟘,
--   Below (node o k) = Σ (p : Pos o). 𝟙 ⊎ Below (k p),
--   Routes t         = 𝟙 ⊎ Below t.
--
-- The subtree at a route comes with its actual judgment (`subtree-at`).
-- At the root it is the tree, and a route through a child ends where it
-- ends in that child, both by refl (`subtree-at-root`, `subtree-at-child`).

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Tree

module _
  {ℓj ℓo ℓp ℓx : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx}
  where

  Below : {j : Judgment S} → Tree S X j → Set ℓp
  Below (hole x) = Lift ℓp 𝟘
  Below (node o k) = Σ (Pos S o) (λ p → Lift ℓp 𝟙 ⊎ Below (k p))

  Routes : {j : Judgment S} → Tree S X j → Set ℓp
  Routes t = Lift ℓp 𝟙 ⊎ Below t

  subtree-at :
    {j : Judgment S} (t : Tree S X j) → Routes t → Σ (Judgment S) (Tree S X)
  subtree-at {j} t (inl _) = j , t
  subtree-at (hole x) (inr (lift ()))
  subtree-at (node o k) (inr (p , r)) = subtree-at (k p) r

  root-route : {j : Judgment S} (t : Tree S X j) → Routes t
  root-route t = inl (lift ⋆)

  subtree-at-root :
    {j : Judgment S} (t : Tree S X j) → subtree-at t (root-route t) ＝ (j , t)
  subtree-at-root t = refl

  child-route :
    {j : Judgment S} (o : Op S j)
    (k : (p : Pos S o) → Tree S X (boundary S o p)) (p : Pos S o) →
    Routes (k p) → Routes (node o k)
  child-route o k p r = inr (p , r)

  subtree-at-child :
    {j : Judgment S} (o : Op S j)
    (k : (p : Pos S o) → Tree S X (boundary S o p)) (p : Pos S o)
    (r : Routes (k p)) →
    subtree-at (node o k) (child-route o k p r) ＝ subtree-at (k p) r
  subtree-at-child o k p r = refl
