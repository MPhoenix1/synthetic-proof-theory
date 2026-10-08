{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Supremum.TypeTopology
  where

-- The supremum of a small family of presentations among TypeTopology's
-- ordinals (Ordinals.Type), transported along toOrdinal.
--
-- For F : I → 𝒫 ℓ with I : Set ℓ, the image of the Cubical supremum
-- bounds the images of the order types, and it is least among all
-- TypeTopology ordinals that bound them: a bound γ is read back as
-- woset γ, with the carrier and relation of γ, where the Cubical
-- supremum is least.

open import Agda.Primitive using (Level)
open import SPT.Cubical.TypeTopology.Ordinals.Type using (Ordinal)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType using
  (orderType)
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Supremum as Supremum
open import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Bridge using
  (toOrdinal)
open import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Simulation
  using (_⊴_; woset; to; from; simulation)

private
  variable
    ℓ : Level

-- Mathematical shape, writing ⌜A⌝ for toOrdinal A:
--
--   ordinal F = ⌜sup F⌝ : Ordinal ℓ,
--   ⌜ord(F i)⌝ ⊴ ordinal F,
--   (∀ i. ⌜ord(F i)⌝ ⊴ γ) → ordinal F ⊴ γ.
ordinal : {I : Set ℓ} (F : I → 𝒫 ℓ) → Ordinal ℓ
ordinal F = toOrdinal (Supremum.supremum F)

upper : {I : Set ℓ} (F : I → 𝒫 ℓ) (i : I)
  → toOrdinal (orderType (F i)) ⊴ ordinal F
upper F i =
  simulation (orderType (F i)) (Supremum.supremum F)
    (Supremum.upper F i)

least : {I : Set ℓ} (F : I → 𝒫 ℓ) (γ : Ordinal ℓ)
  → ((i : I) → toOrdinal (orderType (F i)) ⊴ γ)
  → ordinal F ⊴ γ
least F γ h =
  to (Supremum.supremum F) γ
    (Supremum.least F (woset γ) λ i →
      from (orderType (F i)) γ (h i))

-- Presented upper bounds, by initial maps, bound the TypeTopology
-- supremum.
least-initial : {I : Set ℓ} (F : I → 𝒫 ℓ) (Q : 𝒫 ℓ)
  → ((i : I) → Maps.Initial (F i) Q)
  → ordinal F ⊴ toOrdinal (orderType Q)
least-initial F Q f =
  simulation (Supremum.supremum F) (orderType Q)
    (Supremum.least-initial F Q f)
