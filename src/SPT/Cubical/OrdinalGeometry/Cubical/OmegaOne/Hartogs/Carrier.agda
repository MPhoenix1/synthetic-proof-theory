{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Hartogs.Carrier
  where

-- Under excluded middle, the carriers of ω₁ and H_ℕ are isomorphic,
-- through toHartogs and toOmega.

open import Agda.Primitive using (Level)

import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Countability
  as NatCountability
import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Base as Hartogs
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Base
  as Omega
open import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Hartogs.ToHartogs
  public
open import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Hartogs.ToOmega public
open import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Hartogs.InverseHartogs
  public
open import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Hartogs.InverseOmega
  public

import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.Isomorphism as Iso
import Cubical.Foundations.Prelude as Cubical

private
  variable
    ℓ : Level

-- |ω₁(ℓ)| ≅ |H_ℕ(ℓ)|, and the induced equivalence.

carrierIso :
    NatCountability.ExcludedMiddle ℓ
  → Iso.Iso
      (Cubical.fst (Omega.ω₁ ℓ))
      (Hartogs.Carrier ℓ)
carrierIso excluded-middle = record
  { fun = toHartogs excluded-middle
  ; inv = toOmega excluded-middle
  ; rightInv = toHartogs-toOmega excluded-middle
  ; leftInv = toOmega-toHartogs excluded-middle
  }

carrierEquiv :
    NatCountability.ExcludedMiddle ℓ
  → Equiv._≃_
      (Cubical.fst (Omega.ω₁ ℓ))
      (Hartogs.Carrier ℓ)
carrierEquiv excluded-middle =
  Iso.isoToEquiv
    (carrierIso excluded-middle)
