{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.Generator.Signature where

-- Indexed dependent-polynomial signatures: judgments, operations at each
-- judgment, positions of each operation, and the judgment required at each
-- position.

open import Agda.Primitive using (Level; lsuc; _⊔_)

------------------------------------------------------------------------
-- Indexed signatures

--   Σ = (J, Op, Pos, ∂),   Op(j) : Set,   Pos(o) : Set,   ∂(o,p) : J.
--
-- An operation o : Op j concludes j and asks for one child of judgment
-- `boundary o p` at each position p : Pos o.
record Signature
    (ℓj ℓo ℓp : Level)
    : Set (lsuc (ℓj ⊔ ℓo ⊔ ℓp))
  where
  field
    Judgment :
      Set ℓj

    Op :
      Judgment
      → Set ℓo

    Pos :
        {j : Judgment}
      → Op j
      → Set ℓp

    boundary :
        {j : Judgment}
      → (o : Op j)
      → Pos o
      → Judgment

open Signature public
