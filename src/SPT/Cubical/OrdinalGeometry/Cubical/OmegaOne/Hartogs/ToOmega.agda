{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Hartogs.ToOmega
  where

-- The map H_ℕ → ω₁ under excluded middle: a point goes to the point of ω₁
-- bounding its well-order.

open import Agda.Primitive using (Level)

import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Countability
  as NatCountability
import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Base as Hartogs
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Base as Omega
open import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Hartogs.Below public

import Cubical.Foundations.Prelude as Cubical

private
  variable
    ℓ : Level

toOmega :
    NatCountability.ExcludedMiddle ℓ
  → Hartogs.Carrier ℓ
  → Cubical.fst (Omega.ω₁ ℓ)
toOmega excluded-middle point =
  Cubical.fst
    (below excluded-middle point)
