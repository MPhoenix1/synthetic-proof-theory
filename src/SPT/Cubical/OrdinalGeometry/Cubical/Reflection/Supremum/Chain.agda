{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Supremum.Chain where

-- Presented suprema: the completion of a chain of initial maps presents
-- the supremum of its stages among the Cubical well-ordered sets, and so
-- does the completion that Ambient.supremum builds for a sequence of
-- ordinals of one ambient. Being presented, both lie strictly below the
-- presented ω₁ of every geometry.
--
-- The supremum maps to the completion by its least property. That
-- simulation is onto, because every point of the completion lies in the
-- image of a stage (coverage) and simulations are unique. A surjective
-- simulation is an equivalence of well-ordered sets.

open import Agda.Primitive using (Level)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
open import SPT.Cubical.OrdinalGeometry.Presentation.Sum using (∂)
import SPT.Cubical.OrdinalGeometry.Presentation.Limit as Limit
import SPT.Cubical.OrdinalGeometry.Arithmetic.Ambient as Ambient
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType using
  (orderType)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Simulation using
  (initial)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Supremum using
  (supremum; upper; least; least-initial)
open import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Base using
  ( ω₁ᴳ
  ; orderType-strictᴳ
  )

import Cubical.Data.Equality.Conversion as EqualityConversion
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.Prelude as Cubical
import Cubical.Functions.Embedding as Embedding
import Cubical.Functions.Surjection as Surjection
import Cubical.HITs.PropositionalTruncation as Truncation
import Cubical.HITs.SetQuotients as Quotient
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

private
  variable
    ℓ ℓa ℓa′ ℓb ℓb′ : Level

-- A surjective simulation is an equivalence of well-ordered sets: it is
-- an embedding, and its lifting reflects strictness.
surjective : (A : Woset.Woset ℓa ℓa′) (B : Woset.Woset ℓb ℓb′)
  → (f : A Simulation.≼ B)
  → Surjection.isSurjection (Cubical.fst f)
  → Woset.WosetEquiv A B
surjective A B f onto =
  Cubical._,_
    (Cubical._,_ (Cubical.fst f)
      (Surjection.isEmbedding×isSurjection→isEquiv
        (Cubical._,_ embedding onto)))
    (Woset.iswosetequiv λ a a′ →
      Equiv.propBiimpl→Equiv
        (Woset.IsWoset.is-prop-valued
          (Woset.WosetStr.isWoset (Cubical.snd A)) a a′)
        (Woset.IsWoset.is-prop-valued
          (Woset.WosetStr.isWoset (Cubical.snd B))
          (Cubical.fst f a) (Cubical.fst f a′))
        (Cubical.fst (Cubical.snd f) a a′)
        (reflect a a′))
  where
  embedding : Embedding.isEmbedding (Cubical.fst f)
  embedding =
    Simulation.isSimulation→isEmbedding A B (Cubical.fst f) (Cubical.snd f)

  reflect : (a a′ : Cubical.fst A)
    → Woset.WosetStr._≺_ (Cubical.snd B) (Cubical.fst f a)
        (Cubical.fst f a′)
    → Woset.WosetStr._≺_ (Cubical.snd A) a a′
  reflect a a′ r =
    let fib = Cubical.snd (Cubical.snd f) a′ (Cubical.fst f a) r
    in Cubical.subst (λ c → Woset.WosetStr._≺_ (Cubical.snd A) c a′)
         (Embedding.isEmbedding→Inj embedding
           (Cubical.fst (Cubical.fst fib)) a (Cubical.snd fib))
         (Cubical.snd (Cubical.fst fib))

-- Mathematical shape: for a chain C of initial maps,
--
--   sup_n ord(C n) ≃ ord(completion C).
--
-- On the class of a point x of stage n, the simulation from the
-- supremum agrees with the class map of the stage inclusion, by
-- uniqueness of simulations; coverage puts every point there.
chain : (C : Limit.Chain ℓ)
  → Woset.WosetEquiv (supremum (Limit.Chain.stage C))
      (orderType (Limit.completion C))
chain C =
  surjective (supremum F) (orderType (Limit.completion C)) h onto
  where
  F : ℕ → 𝒫 _
  F = Limit.Chain.stage C

  h : supremum F Simulation.≼ orderType (Limit.completion C)
  h = least-initial F (Limit.completion C) (Limit.stage C)

  agree : (n : ℕ)
    → Simulation.isTrans≼ (orderType (F n)) (supremum F)
        (orderType (Limit.completion C)) (upper F n) h
      Cubical.≡ initial (Limit.stage C n)
  agree n =
    Simulation.isPropValued≼ (orderType (F n))
      (orderType (Limit.completion C)) _ _

  onto : Surjection.isSurjection (Cubical.fst h)
  onto =
    Quotient.elimProp
      (λ _ → Truncation.isPropPropTrunc)
      (λ y →
        let n , x , p = Limit.coverage C y
        in Truncation.∣
             Cubical._,_
               (Cubical.fst (upper F n) Quotient.[ x ])
               ((λ i → Cubical.fst (agree n i) Quotient.[ x ])
                 Cubical.∙ Cubical.cong Quotient.[_]
                   (EqualityConversion.eqToPath p))
           ∣₁)

-- Mathematical shape: for an ambient W and f : ℕ → W,
--
--   sup_n ord(∂(f n))
--     ≃ ord(completion of the cones at the running maxima),
--
-- the completion of Ambient.supremum. The cones at f n and at the running
-- maxima bound each other, so their suprema are equivalent.
ambient : (W : 𝒫 ℓ) (f : ℕ → 𝒫.X W)
  → Woset.WosetEquiv (supremum (λ n → ∂ W (f n)))
      (orderType (Limit.completion (Ambient.chain W f)))
ambient W f =
  Woset.compWosetEquiv
    (Simulation.isAntisym≼Equiv (supremum cone) (supremum running)
      forward backward)
    (chain (Ambient.chain W f))
  where
  cone : ℕ → 𝒫 _
  cone n = ∂ W (f n)

  running : ℕ → 𝒫 _
  running n = ∂ W (Ambient.peak W f n)

  forward : supremum cone Simulation.≼ supremum running
  forward =
    least cone (supremum running) λ n →
      Simulation.isTrans≼ (orderType (cone n))
        (orderType (running n)) (supremum running)
        (initial (Ambient.included W (Ambient.peak-above W f n)))
        (upper running n)

  backward : supremum running Simulation.≼ supremum cone
  backward =
    least running (supremum cone) λ n →
      let k , q = Ambient.peak-from W f n
      in Simulation.isTrans≼ (orderType (running n))
           (orderType (cone k)) (supremum cone)
           (initial (Maps.equivalence (Ambient.same W q)))
           (upper cone k)

------------------------------------------------------------------------
-- Below the presented ω₁

-- Mathematical shape: sup_n ord(C n) ≺ ω₁(G) for every
-- geometry G, since the completion presents the supremum. For the
-- canonical geometry, ω₁(G) is ω₁.
chain-below : (G : Presented.𝒫ω₁𝒢 ℓ) (C : Limit.Chain ℓ)
  → supremum (Limit.Chain.stage C)
      Simulation.≺ ω₁ᴳ G
chain-below G C =
  Simulation.≺RespectsEquivL (ω₁ᴳ G)
    (Woset.invWosetEquiv (chain C))
    (orderType-strictᴳ G
      (Limit.completion C))

ambient-below : (G : Presented.𝒫ω₁𝒢 ℓ) (W : 𝒫 ℓ) (f : ℕ → 𝒫.X W)
  → supremum (λ n → ∂ W (f n))
      Simulation.≺ ω₁ᴳ G
ambient-below G W f =
  Simulation.≺RespectsEquivL (ω₁ᴳ G)
    (Woset.invWosetEquiv (ambient W f))
    (orderType-strictᴳ G
      (Limit.completion (Ambient.chain W f)))
