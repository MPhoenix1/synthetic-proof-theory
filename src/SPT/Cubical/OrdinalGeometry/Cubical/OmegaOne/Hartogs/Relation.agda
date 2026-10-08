{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Hartogs.Relation
  where

-- The equivalence ω₁ ≃ H_ℕ preserves and reflects the order, pointwise.

open import Agda.Primitive using (Level)

import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Countability
  as NatCountability
import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Base as Hartogs
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Base as Omega
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Hartogs
  as Comparison

import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.Prelude as Cubical
import Cubical.Relation.Binary.Order.Woset.Base as Woset

private
  variable
    ℓ : Level

-- x < y ≃ e(x) < e(y), where e is the carrier map of ω₁(ℓ) ≃ H_ℕ(ℓ).

strict-equivalence :
    (excluded-middle : NatCountability.ExcludedMiddle ℓ)
  → (left right : Cubical.fst (Omega.ω₁ ℓ))
  → Equiv._≃_
      (Woset.WosetStr._≺_
        (Cubical.snd (Omega.ω₁ ℓ)) left right)
      (Hartogs.Strict
        (Equiv.equivFun
          (Cubical.fst
            (Comparison.equivalence
              excluded-middle))
          left)
        (Equiv.equivFun
          (Cubical.fst
            (Comparison.equivalence
              excluded-middle))
          right))
strict-equivalence
    excluded-middle left right =
  Woset.IsWosetEquiv.pres≺
    (Cubical.snd
      (Comparison.equivalence excluded-middle))
    left right
