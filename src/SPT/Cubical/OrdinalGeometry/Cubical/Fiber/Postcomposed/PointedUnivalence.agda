{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Postcomposed.PointedUnivalence
  where

-- Pointed univalence as a split embedding of the pointed automorphisms of
-- (T , t) into the loops of the pointed universe at (T , t).  It is a
-- separate module so that univalence is normalized once.

open import Agda.Primitive using (Level)

import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Position
  as Position
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Postcomposed.Equivalence
  as EquivalenceEmbedding
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.IteratedLoop
  as Iterated

import Cubical.Foundations.Pointed.Base as Pointed
import Cubical.Foundations.Prelude as Cubical
import Cubical.Structures.Pointed as PointedStructure

private
  variable
    ℓ : Level

-- Aut∗(T,t) = ((T,t) ≃∗ (T,t)), pointed self-equivalences.

PointedAutomorphism :
  Position.PointedType ℓ → Set ℓ
PointedAutomorphism pointed =
  Pointed._≃∙_ pointed pointed

identityAutomorphism :
    (pointed : Position.PointedType ℓ)
  → PointedAutomorphism pointed
identityAutomorphism = Pointed.idEquiv∙

-- Aut∗(T,t) embeds into Loop(PointedType ℓ, (T,t)) by pointed univalence,
-- preserving the point: the identity goes to refl.

automorphism-loop-embedding :
    (pointed : Position.PointedType ℓ)
  → Iterated.PointedSplitEmbedding
      (PointedAutomorphism pointed)
      (identityAutomorphism pointed)
      (Iterated.Loop (Position.PointedType ℓ) pointed)
      Cubical.refl
automorphism-loop-embedding pointed =
  Iterated.pointed-split-embedding
    (EquivalenceEmbedding.equivalenceSplitEmbedding
      (PointedStructure.pointedSIP pointed pointed))
    (PointedStructure.pointed-sip-idEquiv∙ pointed)
