{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Supremum where

-- Suprema of families of presentations among the Cubical well-ordered
-- sets: row 8 of the KNFX table in the form of Kraus, Nordvall Forsberg
-- and Xu, where Ord has suprema of small families (their Lemma 60).
--
-- The supremum of F : I → 𝒫 ℓ is the supremum of the order types
-- ord(F i), the library's quotient (Σ i. |F i|)/∼ of
-- HoTT book Lemma 10.3.22. It is least among Woset upper bounds, hence
-- among presented ones: initial maps F i → Q bound it by Q. No
-- omniscience principle is used.

open import Agda.Primitive using (Level; _⊔_)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType using
  (orderType)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Simulation using
  (initial)

import Cubical.Foundations.Prelude as Cubical
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

private
  variable
    ℓ ℓ′ : Level

-- Mathematical shape:
--
--   sup F : Woset(ℓ′ ⊔ ℓ, ℓ),
--   ord(F i) ≼ sup F,
--   (∀ i. ord(F i) ≼ W) → sup F ≼ W   for W : Woset(ℓ, ℓ).
--
-- A small index, I : Set ℓ, gives a small supremum, Woset(ℓ, ℓ). The
-- construction is sealed; only these three laws are exported.
-- Nonclaim: sup F need not be presented. OmegaOne.Cut
-- characterizes the presented ordinals below ω₁.
abstract
  supremum : {I : Set ℓ′} (F : I → 𝒫 ℓ) → Woset.Woset (ℓ′ ⊔ ℓ) ℓ
  supremum F =
    Cubical.fst (Simulation.sup λ i → orderType (F i))

  upper : {I : Set ℓ′} (F : I → 𝒫 ℓ) (i : I)
    → orderType (F i) Simulation.≼ supremum F
  upper F =
    Cubical.fst
      (Cubical.snd (Simulation.sup λ i → orderType (F i)))

  least : {I : Set ℓ′} (F : I → 𝒫 ℓ) (W : Woset.Woset ℓ ℓ)
    → ((i : I) → orderType (F i) Simulation.≼ W)
    → supremum F Simulation.≼ W
  least F =
    Cubical.snd
      (Cubical.snd (Simulation.sup λ i → orderType (F i)))

-- Mathematical shape:
--
--   (∀ i. Initial (F i) Q) → sup F ≼ ord(Q).
--
-- A presented upper bound, in the order of presentations, bounds the
-- supremum: each initial map is a simulation of order types.
least-initial : {I : Set ℓ′} (F : I → 𝒫 ℓ) (Q : 𝒫 ℓ)
  → ((i : I) → Maps.Initial (F i) Q)
  → supremum F Simulation.≼ orderType Q
least-initial F Q f =
  least F (orderType Q) λ i → initial (f i)
