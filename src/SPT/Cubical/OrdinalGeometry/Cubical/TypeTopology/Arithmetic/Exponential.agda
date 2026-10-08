{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Arithmetic.Exponential
  where

-- The reflected ω^ satisfies the exponentiation specification of Kraus,
-- Nordvall Forsberg and Xu (Definition 14, base ω) among well-ordered
-- sets, with TypeTopology's arithmetic:
--
--   (ω^Z)′ ≃ Z′ +ₒ 𝟙ₒ                   for Z a zero,
--   (ω^S)′ ≃ (ω^P)′ ×ₒ ω′               for S a successor of P,
--   (ω^A)′ ≃ sup_n (ω^(Pₙ))′            for A the limit of Pₙ,
--
-- the supremum that of Reflection.Supremum, least among all
-- TypeTopology ordinals bounding the (ω^(Pₙ))′ (Supremum.
-- TypeTopology). Nonclaim: this is not a comparison with TypeTopology's
-- own exponentiation (Ordinals.Exponentiation), which assumes univalence,
-- propositional truncations and set replacement in TypeTopology's terms;
-- among well-ordered sets the specification does not determine the
-- operation.

open import Agda.Primitive using (Level)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Limit as Limit
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization using
  (Zero; Successor; Strong; module Successors; Supremum; module Suprema;
   Increasing)
open import SPT.Cubical.OrdinalGeometry.Operation.Exponential using (exp)
import SPT.Cubical.OrdinalGeometry.Operation.Exponential
  as GeneratedExponential
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Exponential using (omega)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Exponential as Exponential
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType using
  (orderType; orderType-equivalence)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Supremum using
  (supremum)
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Supremum.Chain as Chain
open import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Simulation
  using (woset)
open import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Arithmetic
  using (_+ₒ_; _×ₒ_; 𝟙ₒ; ordinal; successor; product)

import Cubical.Relation.Binary.Order.Woset.Base as Woset

private
  variable
    ℓ : Level

-- (52): the order type of ω^Z is the successor of Z′.
zero-law : (Z : 𝒫 ℓ) → Zero Z
  → Woset.WosetEquiv (orderType (exp Z)) (woset (ordinal Z +ₒ 𝟙ₒ))
zero-law Z z =
  Woset.compWosetEquiv
    (orderType-equivalence
      (Exponential.zero-law Z z (Strong.successor (Successors.next Z))))
    (successor Z)

-- (53): the order type of ω^S is that of ω^P times ω.
successor-law : {P S : 𝒫 ℓ} → Successor P S
  → Woset.WosetEquiv (orderType (exp S))
      (woset (ordinal (exp P) ×ₒ ordinal omega))
successor-law {P = P} s =
  Woset.compWosetEquiv
    (orderType-equivalence (Exponential.successor-law s))
    (product (exp P) omega)

-- (54): the order type of ω^A is the supremum of those of the ω^(Pₙ).
limit-law : (s : Increasing ℓ) {A : 𝒫 ℓ}
  → Supremum (Increasing.stage s) A
  → Woset.WosetEquiv (orderType (exp A))
      (supremum λ n → exp (Increasing.stage s n))
limit-law s sup =
  Woset.compWosetEquiv
    (orderType-equivalence
      (Exponential.limit-law s sup (Suprema.completion chain)))
    (Woset.invWosetEquiv (Chain.chain chain))
  where
  chain : Limit.Chain _
  chain = record
    { stage = λ n → exp (Increasing.stage s n)
    ; edge = λ n →
        GeneratedExponential.initial (Maps.inclusion (Increasing.step s n))
    }
