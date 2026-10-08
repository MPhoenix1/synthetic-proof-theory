{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Supremum.Discriminator
  where

-- Suprema of arbitrary countable families of presentations are not
-- presented constructively: if the supremum of every ℕ-indexed family
-- merely had a presentation, LPO would follow.
--
-- For a Boolean stream s, take the family (possible s + 1, 1, 1, …). A
-- presentation R of its supremum receives simulations of both members,
-- which the converse comparison reads as initial maps into R. A common
-- initial bound of possible s + 1 and 1 decides s
-- (Arithmetic.Ambient.Discriminator.common). The decision is first made
-- under the truncation and then extracted, since a hit of s can be
-- searched for (Settled, unsettle; OmegaOne.Regularity extracts its
-- decision the same way). The presented form of row 8 holds for chains
-- instead (Supremum.Chain).

open import Agda.Primitive using (lzero)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Limit.Discriminator as Stream
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Ambient.Discriminator using
  (common; family)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType using
  (orderType)
open import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Cut using
  (MerelyPresented)
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Simulation.Converse
  as Converse
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Supremum using
  (supremum; upper)

import Cubical.Data.Bool as CubicalBool
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality.Conversion as EqualityConversion
import Cubical.Data.Nat.Order.Recursive as NatOrder
import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Prelude as Cubical
import Cubical.HITs.PropositionalTruncation as Truncation
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation
import Cubical.Relation.Nullary as Nullary

------------------------------------------------------------------------
-- Decisions of LPO under truncation

-- The decision of LPO at s, with the inductive identity of Stream.
Decision : (ℕ → Bool) → Set
Decision s = Stream.Hit s ⊎ ((n : ℕ) → s n ≡ false)

-- The same decision with paths, and with the hit truncated: a
-- proposition, since a hit and its absence exclude each other.
Settled : (ℕ → Bool) → Set
Settled s =
  Truncation.∥ Σ ℕ (λ n → s n Cubical.≡ true) ∥₁
    ⊎ ((n : ℕ) → s n Cubical.≡ false)

private
  clash : (s : ℕ → Bool) → Σ ℕ (λ n → s n Cubical.≡ true)
    → ((n : ℕ) → s n Cubical.≡ false) → Empty.⊥
  clash s (n , p) none =
    CubicalBool.true≢false (Cubical.sym p Cubical.∙ none n)

settled : (s : ℕ → Bool) → Cubical.isProp (Settled s)
settled s (inj₁ a) (inj₁ b) =
  Cubical.cong inj₁ (Truncation.isPropPropTrunc a b)
settled s (inj₁ a) (inj₂ b) =
  Empty.rec (Truncation.rec Empty.isProp⊥ (λ h → clash s h b) a)
settled s (inj₂ a) (inj₁ b) =
  Empty.rec (Truncation.rec Empty.isProp⊥ (λ h → clash s h a) b)
settled s (inj₂ a) (inj₂ b) =
  Cubical.cong inj₂
    (HLevels.isPropΠ (λ n → CubicalBool.isSetBool (s n) false) a b)

settle : (s : ℕ → Bool) → Decision s → Settled s
settle s (inj₁ (n , p)) =
  inj₁ Truncation.∣ n , EqualityConversion.eqToPath p ∣₁
settle s (inj₂ none) = inj₂ λ n → EqualityConversion.eqToPath (none n)

-- A truncated hit yields the least hit, by search.
unsettle : (s : ℕ → Bool) → Settled s → Decision s
unsettle s (inj₁ t) =
  let n , p =
        Nullary.Collapsible→SplitSupport
          (NatOrder.Decidable→Collapsible
            (λ n → CubicalBool.isSetBool (s n) true)
            (λ n → s n CubicalBool.≟ true))
          t
  in inj₁ (n , EqualityConversion.pathToEq p)
unsettle s (inj₂ none) =
  inj₂ λ n → EqualityConversion.pathToEq (none n)

------------------------------------------------------------------------
-- Suprema of countable families

private
  -- A presentation of the supremum of family s decides s.
  decide : (s : ℕ → Bool)
    → Σ (𝒫 lzero) (λ R →
        Woset.WosetEquiv (orderType R) (supremum (family s)))
    → Decision s
  decide s (R , e) =
    common s R (Converse.initial (into zero))
      (Converse.initial (into (suc zero)))
    where
    into : (n : ℕ)
      → orderType (family s n) Simulation.≼ orderType R
    into n =
      Simulation.isTrans≼ (orderType (family s n))
        (supremum (family s)) (orderType R)
        (upper (family s) n)
        (Simulation.WosetEquiv→≼ (Woset.invWosetEquiv e))

-- Mathematical shape:
--
--   (Π F : ℕ → 𝒫. MerelyPresented(sup F)) → LPO.
presented : ((F : ℕ → 𝒫 lzero) → MerelyPresented (supremum F))
  → Stream.LPO
presented supremum-presented s =
  unsettle s
    (Truncation.rec (settled s) (λ σ → settle s (decide s σ))
      (supremum-presented (family s)))
