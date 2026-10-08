{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Postcomposed.Equivalence
  where

-- An equivalence as a split embedding.  It is a separate module so that the
-- inverse law of the equivalence is normalized once.

open import Agda.Primitive using (Level)

import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.SplitEmbedding
  as Split

import Cubical.Foundations.Equiv as Equiv

private
  variable
    ℓ-A ℓ-B : Level
    A : Set ℓ-A
    B : Set ℓ-B

-- (A ≃ B) → SplitEmbedding A B, from the fields of the equivalence.

equivalenceSplitEmbedding :
    A Equiv.≃ B
  → Split.SplitEmbedding A B
equivalenceSplitEmbedding equivalence =
  Split.split-embedding
    (Equiv.equivFun equivalence)
    (Equiv.invEq equivalence)
    (Equiv.retEq equivalence)
