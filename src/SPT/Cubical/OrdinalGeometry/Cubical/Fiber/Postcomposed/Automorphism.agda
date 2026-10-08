{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Postcomposed.Automorphism
  where

-- Pointed automorphisms survive as loops in every postcomposed fiber: the
-- pointed automorphisms of (T , t) embed, preserving the point, into the
-- loops of the fiber of A ∘ q_G at retain(T , t), and so does each finite
-- iterated loop type of them, one dimension higher.

open import Agda.Primitive using (Level)
open import Data.Nat using (ℕ)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Position
  as Position
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Postcomposed
  as Postcomposition
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Postcomposed.PointedUnivalence
  as PointedLoops
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.IteratedLoop
  as Iterated

import Cubical.Foundations.Prelude as Cubical
import Cubical.Relation.Binary.Order.Woset.Base as Woset

private
  variable
    ℓ ℓ-target : Level
    Target : Set ℓ-target

-- Automorphisms as loops

pointedEmbedding :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (adapter : Woset.Woset ℓ ℓ → Target)
    (pointed : Position.PointedType ℓ)
  → Iterated.PointedSplitEmbedding
      (Position.PointedType ℓ)
      pointed
      (Postcomposition.PostcomposedFiber geometry adapter)
      (Postcomposition.retain
        geometry adapter pointed)
pointedEmbedding
    geometry adapter pointed =
  Iterated.pointed-split-embedding
    (Postcomposition.universeEmbedding
      geometry adapter)
    Cubical.refl

-- Aut∗(T,t) embeds into Loop(fiber of A ∘ q_G, retain(T,t)): pointed
-- univalence, then the loop map of the retract of Postcomposed.  It is a
-- split embedding, not an equivalence.

automorphismEmbedding :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (adapter : Woset.Woset ℓ ℓ → Target)
    (pointed : Position.PointedType ℓ)
  → Iterated.PointedSplitEmbedding
      (PointedLoops.PointedAutomorphism pointed)
      (PointedLoops.identityAutomorphism pointed)
      (Iterated.Loop
        (Postcomposition.PostcomposedFiber geometry adapter)
        (Postcomposition.retain
          geometry adapter pointed))
      Cubical.refl
automorphismEmbedding
    geometry adapter pointed =
  Iterated.composePointedSplitEmbedding
    (PointedLoops.automorphism-loop-embedding
      pointed)
    (Iterated.liftPointedSplitEmbedding
      (pointedEmbedding
        geometry adapter pointed))

-- Every iterated loop type Ωʰ(Aut∗(T,t)) embeds into Ω^(h+1) of the same
-- fiber.

iteratedEmbedding :
    (height : ℕ)
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (adapter : Woset.Woset ℓ ℓ → Target)
    (pointed : Position.PointedType ℓ)
  → Iterated.PointedSplitEmbedding
      (Iterated.IteratedLoop height
        (PointedLoops.PointedAutomorphism pointed)
        (PointedLoops.identityAutomorphism pointed))
      (Iterated.iteratedLoopPoint height
        (PointedLoops.PointedAutomorphism pointed)
        (PointedLoops.identityAutomorphism pointed))
      (Iterated.IteratedLoop (Data.Nat.suc height)
        (Postcomposition.PostcomposedFiber geometry adapter)
        (Postcomposition.retain
          geometry adapter pointed))
      (Iterated.iteratedLoopPoint (Data.Nat.suc height)
        (Postcomposition.PostcomposedFiber geometry adapter)
        (Postcomposition.retain
          geometry adapter pointed))
iteratedEmbedding
    height geometry adapter pointed =
  Iterated.iteratePointedSplitEmbedding height
    (automorphismEmbedding
      geometry adapter pointed)
