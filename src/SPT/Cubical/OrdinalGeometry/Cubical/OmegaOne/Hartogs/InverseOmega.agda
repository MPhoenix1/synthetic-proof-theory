{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Hartogs.InverseOmega
  where

-- toOmega ∘ toHartogs is the identity on ω₁: principal segments of ω₁ are
-- injective.

open import Agda.Primitive using (Level)

import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Countability
  as NatCountability
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Base as Omega
open import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Hartogs.ToHartogs
open import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Hartogs.ToOmega

import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.Prelude as Cubical
import Cubical.Functions.Embedding as Embedding
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

private
  variable
    ℓ : Level

toOmega-toHartogs :
    (excluded-middle : NatCountability.ExcludedMiddle ℓ)
  → (point : Cubical.fst (Omega.ω₁ ℓ))
  → Cubical.fst
      (below
        excluded-middle
        (toHartogs excluded-middle point))
      Cubical.≡ point
toOmega-toHartogs {ℓ} excluded-middle point =
  Embedding.isEmbedding→Inj
    (Simulation.isEmbedding↓ (Omega.ω₁ ℓ))
    (Cubical.fst
      (below
        excluded-middle
        (toHartogs excluded-middle point)))
    point
    (Equiv.equivFun
      (Woset.WosetPath
        (Simulation._↓_ (Omega.ω₁ ℓ)
          (Cubical.fst
            (below
              excluded-middle
              (toHartogs excluded-middle point))))
        (Simulation._↓_ (Omega.ω₁ ℓ) point))
      (Woset.compWosetEquiv
        (Cubical.snd
          (below
            excluded-middle
            (toHartogs excluded-middle point)))
        (toHartogs-segment
          excluded-middle point)))
