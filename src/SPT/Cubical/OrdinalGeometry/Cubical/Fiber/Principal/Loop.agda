{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Principal.Loop
  where

-- A nontrivial loop in UnitPresentations(G), so that space is not a set,
-- not a proposition and not contractible, while its truncation
-- MerelyPresented is contractible; so the truncation map is not an
-- embedding.

open import Agda.Primitive using (Level; lzero)
open import Data.Empty using (⊥)
open import Data.Unit.Polymorphic as PolyUnit using ()

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Cut as Cut
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Position
  as Position
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Principal
  as Principal
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Principal.Retraction
  as Retraction

import Cubical.Foundations.Prelude as Cubical
import Cubical.Functions.Embedding as Embedding
import Cubical.HITs.PropositionalTruncation as Truncation

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- The swap loop

-- swapPath(G) = cong retain swapLoop: the presentation changes by the swap
-- of 𝟐 × 𝟐 while the segment stays fixed.

swapPath :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
  → Retraction.retain
      geometry Position.pointedBoolPair
      Cubical.≡
    Retraction.retain
      geometry Position.pointedBoolPair
swapPath geometry =
  Cubical.cong
    (Retraction.retain geometry)
    Position.pointedSwapLoop

swapPath-not-refl :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
  → swapPath geometry Cubical.≡ Cubical.refl
  → ⊥
swapPath-not-refl
  geometry principal-loop=refl =
  Position.pointedSwapLoop-not-refl
    (Cubical.sym
      (Retraction.recover-retain-path
        geometry Position.pointedSwapLoop)
    Cubical.∙
    Cubical.cong
      (Cubical.cong
        (Retraction.recover geometry))
      principal-loop=refl)

-- UnitPresentations(G) is not a set, since recovery would make the swap
-- loop trivial; hence not a proposition and not contractible.

not-set :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
  → Cubical.isSet (Principal.UnitPresentations geometry)
  → ⊥
not-set geometry principal-is-set =
  swapPath-not-refl geometry
    (principal-is-set
      (Retraction.retain
        geometry Position.pointedBoolPair)
      (Retraction.retain
        geometry Position.pointedBoolPair)
      (swapPath geometry)
      Cubical.refl)

not-prop :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
  → Cubical.isProp (Principal.UnitPresentations geometry)
  → ⊥
not-prop geometry principal-is-prop =
  not-set geometry
    (Cubical.isProp→isSet principal-is-prop)

not-contractible :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
  → Cubical.isContr (Principal.UnitPresentations geometry)
  → ⊥
not-contractible geometry principal-is-contr =
  not-prop geometry
    (Cubical.isContr→isProp principal-is-contr)

------------------------------------------------------------------------
-- The truncation

-- The truncation map Presentations → ‖Presentations‖ = MerelyPresented.

truncation :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → Principal.UnitPresentations geometry
  → Cut.MerelyPresented
      (Principal.unitSegment geometry)
truncation geometry represented =
  Truncation.∣ represented ∣₁

merelyPresented :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → Cut.MerelyPresented
      (Principal.unitSegment geometry)
merelyPresented {ℓ} geometry =
  truncation geometry
    (Retraction.retain geometry
      (PolyUnit.⊤ {ℓ} Cubical., PolyUnit.tt))

-- MerelyPresented of the unit segment is contractible.

merelyPresented-isContr :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → Cubical.isContr
      (Cut.MerelyPresented
        (Principal.unitSegment geometry))
merelyPresented-isContr geometry =
  merelyPresented geometry
  Cubical.,
  Cut.isPropMerelyPresented
    (Principal.unitSegment geometry)
    (merelyPresented geometry)

-- So the truncation map is not an embedding at level zero.

truncation-not-embedding :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
  → Embedding.isEmbedding (truncation geometry)
  → ⊥
truncation-not-embedding geometry embedding =
  not-prop geometry
    (Embedding.Embedding-into-isProp→isProp
      (truncation geometry Cubical., embedding)
      (Cut.isPropMerelyPresented
        (Principal.unitSegment geometry)))
