{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Signature where

-- An indexed signature `S = (J, Op, Pos, ∂)` has a type of judgments, for each
-- judgment a type of operations concluding it, for each operation a type of
-- positions, and for each position the judgment of the child required there:
--
--   Op j : Set,   Pos o : Set,   ∂ (o , p) : J.
--
-- An operation `o : Op j` concludes `j` and asks for one child of judgment
-- `boundary o p` at each position `p : Pos o`. Branching may be empty, finite
-- or infinite.

open import SPT.Cubical.Base

record Signature (ℓj ℓo ℓp : Level) : Set (lsuc (ℓj ⊔ ℓo ⊔ ℓp)) where
  field
    Judgment : Set ℓj
    Op : Judgment → Set ℓo
    Pos : {j : Judgment} → Op j → Set ℓp
    boundary : {j : Judgment} (o : Op j) → Pos o → Judgment

open Signature public
