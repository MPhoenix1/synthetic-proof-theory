{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Tree where

-- An open tree over a signature `S`, with holes carrying a payload `X j` at
-- judgment `j`, is either a hole or a node: an operation with a tree at each of
-- its positions,
--
--   Tree S X j ≅ X j ⊎ Σ (o : Op j). Π (p : Pos o). Tree S X (∂ (o , p)).
--
-- A history is a closed tree, one whose holes carry no payload.

open import SPT.Cubical.Foundation.Signature public
  using (Signature; Judgment; Op; Pos; boundary)
open import SPT.Cubical.Base

data Tree {ℓj ℓo ℓp ℓx : Level} (S : Signature ℓj ℓo ℓp)
  (X : Judgment S → Set ℓx) : Judgment S → Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx)
  where
  hole : {j : Judgment S} → X j → Tree S X j
  node : {j : Judgment S} (o : Op S j) →
    ((p : Pos S o) → Tree S X (boundary S o p)) → Tree S X j

History : {ℓj ℓo ℓp : Level} (S : Signature ℓj ℓo ℓp) → Judgment S →
  Set (ℓj ⊔ ℓo ⊔ ℓp)
History S = Tree S (λ _ → 𝟘)
