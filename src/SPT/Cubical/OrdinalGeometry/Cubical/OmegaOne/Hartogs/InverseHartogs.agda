{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Hartogs.InverseHartogs
  where

-- toHartogs ∘ toOmega is the identity on H_ℕ.

open import Agda.Primitive using (Level)

import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Countability
  as NatCountability
import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Base as Hartogs
open import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Hartogs.ToHartogs
open import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Hartogs.ToOmega

import Cubical.Data.Sigma.Properties as SigmaProperties
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.Prelude as Cubical
import Cubical.Relation.Binary.Order.Woset.Base as Woset

private
  variable
    ℓ : Level

toHartogs-toOmega :
    (excluded-middle : NatCountability.ExcludedMiddle ℓ)
  → (point : Hartogs.Carrier ℓ)
  → toHartogs excluded-middle
      (Cubical.fst
        (below
          excluded-middle point))
      Cubical.≡ point
toHartogs-toOmega excluded-middle point =
  SigmaProperties.Σ≡Prop
    (λ _ → NatCountability.isPropMerelyEmbedsInNat)
    (Equiv.equivFun
      (Woset.WosetPath
        (Cubical.fst
          (toHartogs excluded-middle
            (Cubical.fst
              (below
                excluded-middle point))))
        (Cubical.fst point))
      (Woset.compWosetEquiv
        (toHartogs-segment
          excluded-middle
          (Cubical.fst
            (below
              excluded-middle point)))
        (Cubical.snd
          (below
            excluded-middle point))))
