{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Supremum.Comparison
  where

-- Under LPO the supremum of every ℕ-family of presentations is presented.
-- The running maxima of the family (Arithmetic.Comparison.Running) form a
-- chain whose completion presents the supremum of its stages
-- (Chain.chain), and the family and its running maxima bound each other
-- (running). With the discriminator Supremum.Discriminator.
-- presented this is exact:
--
--   LPO ⇔ Π F : ℕ → 𝒫. MerelyPresented (sup F)          (strength).
--
-- These suprema lie strictly below the presented ω₁ of every geometry
-- (below).

open import Agda.Primitive using (Level; lzero)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Function.Bundles using (_⇔_; mk⇔)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Limit as Limit
import SPT.Cubical.OrdinalGeometry.Presentation.Limit.Discriminator as Stream
import SPT.Cubical.OrdinalGeometry.Arithmetic.Comparison as Comparison
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType using
  (orderType)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Simulation using
  (initial)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Supremum using
  (supremum; upper; least)
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Supremum.Chain as Chain
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Supremum.Discriminator
  as Discriminator
open import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Cut using
  (MerelyPresented)
open import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Base using
  ( ω₁ᴳ
  ; orderType-strictᴳ
  )

import Cubical.Foundations.Prelude as Cubical
import Cubical.HITs.PropositionalTruncation as Truncation
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

private
  variable
    ℓ : Level

-- Mathematical shape: sup F ≃ sup (running maxima of F).
running : (lpo : Stream.LPO) (F : ℕ → 𝒫 ℓ)
  → Woset.WosetEquiv (supremum F)
      (supremum (Limit.Chain.stage (Comparison.Running.chain lpo F)))
running lpo F =
  Simulation.isAntisym≼Equiv (supremum F) (supremum maxima) forward backward
  where
  maxima : ℕ → 𝒫 _
  maxima = Limit.Chain.stage (Comparison.Running.chain lpo F)

  forward : supremum F Simulation.≼ supremum maxima
  forward =
    least F (supremum maxima) λ n →
      Simulation.isTrans≼ (orderType (F n))
        (orderType (maxima n)) (supremum maxima)
        (initial (Comparison.Running.above lpo F n))
        (upper maxima n)

  backward : supremum maxima Simulation.≼ supremum F
  backward =
    least maxima (supremum F) λ n →
      upper F (Comparison.Running.index lpo F n)

-- Mathematical shape: LPO → Π F : ℕ → 𝒫. Σ R. R′ ≃ sup F.
presented : Stream.LPO → (F : ℕ → 𝒫 ℓ)
  → Σ (𝒫 ℓ) (λ R →
      Woset.WosetEquiv (orderType R) (supremum F))
presented lpo F =
  Limit.completion (Comparison.Running.chain lpo F)
  , Woset.invWosetEquiv
      (Woset.compWosetEquiv (running lpo F)
        (Chain.chain (Comparison.Running.chain lpo F)))

-- Mathematical shape: LPO → Π F : ℕ → 𝒫. MerelyPresented (sup F).
merely : Stream.LPO → (F : ℕ → 𝒫 ℓ) → MerelyPresented (supremum F)
merely lpo F =
  Truncation.∣ Cubical._,_ (proj₁ (presented lpo F))
    (proj₂ (presented lpo F)) ∣₁

-- Mathematical shape: LPO ⇔ Π F : ℕ → 𝒫. MerelyPresented (sup F).
strength : Stream.LPO
  ⇔ ((F : ℕ → 𝒫 lzero) → MerelyPresented (supremum F))
strength = mk⇔ (λ lpo → merely lpo) Discriminator.presented

-- Mathematical shape: LPO → sup F ≺ ω₁(G).
below : Stream.LPO → (G : Presented.𝒫ω₁𝒢 ℓ) (F : ℕ → 𝒫 ℓ)
  → supremum F Simulation.≺ ω₁ᴳ G
below lpo G F =
  Simulation.≺RespectsEquivL (ω₁ᴳ G)
    (proj₂ (presented lpo F))
    (orderType-strictᴳ G
      (proj₁ (presented lpo F)))
