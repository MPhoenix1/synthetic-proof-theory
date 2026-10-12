{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Multiplication.Left where

-- − · Q respects equivalence: P ≃ P′ gives P · Q ≃ P′ · Q (equivalence).
-- P · Q is the sum of copies of P over the normalized points of Q, so an
-- equivalence of P with P′ is an equivalence of every block
-- (Sum.Indexed.Equivalence). Multiplication.equivalence is the same for
-- the right factor.

open import Agda.Primitive using (Level)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Sum.Indexed.Equivalence
  as Blocks
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Multiplication using
  (_·_; index)

private
  variable
    ℓ : Level

opaque
  unfolding _·_

  -- Mathematical shape: P ≃ P′ → P · Q ≃ P′ · Q.
  equivalence : {P P′ : 𝒫 ℓ} → P Presented.≃𝒫 P′ → (Q : 𝒫 ℓ)
    → (P · Q) Presented.≃𝒫 (P′ · Q)
  equivalence {P = P} {P′} e Q =
    Blocks.equivalence {I = index Q} {F = λ _ → P} {G = λ _ → P′} (λ _ → e)
