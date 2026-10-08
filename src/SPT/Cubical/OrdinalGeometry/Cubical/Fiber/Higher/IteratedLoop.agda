{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.IteratedLoop
  where

-- Iterated loop spaces, right associated so that
--
--   IteratedLoop (suc n) A a  reduces to  IteratedLoop n (a = a) refl,
--
-- and pointed split embeddings, which lift through every iterated loop
-- space without a separate reassociation proof.

open import Agda.Primitive using (Level; _⊔_)
open import Data.Empty using (⊥)
import Data.Nat.Base as Nat

import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.SplitEmbedding
  as Split

import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Prelude as Cubical

private
  variable
    ℓ-A ℓ-B ℓ-C : Level
    A : Set ℓ-A
    B : Set ℓ-B
    C : Set ℓ-C

Loop : (A : Set ℓ-A) → A → Set ℓ-A
Loop A point = point Cubical.≡ point

------------------------------------------------------------------------
-- Iterated loop spaces

--   L(0,A,a) = A,   L(suc n,A,a) = L(n, a = a, refl).

IteratedLoop :
    (height : Nat.ℕ)
    (A : Set ℓ-A)
    (point : A)
  → Set ℓ-A
IteratedLoop Nat.zero A point = A
IteratedLoop (Nat.suc height) A point =
  IteratedLoop height (Loop A point) Cubical.refl

iteratedLoopPoint :
    (height : Nat.ℕ)
    (A : Set ℓ-A)
    (point : A)
  → IteratedLoop height A point
iteratedLoopPoint Nat.zero A point = point
iteratedLoopPoint (Nat.suc height) A point =
  iteratedLoopPoint height (Loop A point) Cubical.refl

------------------------------------------------------------------------
-- Point-preserving split embeddings

-- A pointed split embedding (A,a) ◁∗ (B,b) is A ◁ B with include(a) = b.

record PointedSplitEmbedding
    (A : Set ℓ-A)
    (source-point : A)
    (B : Set ℓ-B)
    (target-point : B)
    : Set (ℓ-A ⊔ ℓ-B) where
  constructor pointed-split-embedding
  field
    splitEmbedding : Split.SplitEmbedding A B
    include-point :
      Split.include splitEmbedding source-point Cubical.≡ target-point

open PointedSplitEmbedding public

identityPointedSplitEmbedding :
    (point : A)
  → PointedSplitEmbedding A point A point
identityPointedSplitEmbedding point =
  pointed-split-embedding Split.identitySplitEmbedding Cubical.refl

composePointedSplitEmbedding :
    {source-point : A}
    {middle-point : B}
    {target-point : C}
  → PointedSplitEmbedding A source-point B middle-point
  → PointedSplitEmbedding B middle-point C target-point
  → PointedSplitEmbedding A source-point C target-point
composePointedSplitEmbedding first second =
  pointed-split-embedding
    (Split.composeSplitEmbedding
      (splitEmbedding first)
      (splitEmbedding second))
    (Cubical.cong
      (Split.include (splitEmbedding second))
      (include-point first)
    Cubical.∙
    include-point second)

preserves-nonbase :
    {source-point : A}
    {target-point : B}
    (embedding : PointedSplitEmbedding A source-point B target-point)
    (point : A)
  → (point Cubical.≡ source-point → ⊥)
  → Split.include (splitEmbedding embedding) point
      Cubical.≡ target-point
  → ⊥
preserves-nonbase
    embedding point point-not-base image-is-base =
  point-not-base
    (Split.splitEmbedding-injective
      (splitEmbedding embedding)
      point
      _
      (image-is-base Cubical.∙ Cubical.sym (include-point embedding)))

------------------------------------------------------------------------
-- One canonical loop lift

liftPointedSplitEmbedding :
    {source-point : A}
    {target-point : B}
  → PointedSplitEmbedding A source-point B target-point
  → PointedSplitEmbedding
      (Loop A source-point)
      Cubical.refl
      (Loop B target-point)
      Cubical.refl
liftPointedSplitEmbedding embedding =
  pointed-split-embedding
    (Split.composeSplitEmbedding
      (Split.liftPathSplitEmbedding
        (splitEmbedding embedding)
        _ _)
      (Split.rebaseLoopSplitEmbedding (include-point embedding)))
    (Split.rebaseLoopSplitEmbedding-refl (include-point embedding))

------------------------------------------------------------------------
-- Iteration

iteratePointedSplitEmbedding :
    {source-point : A}
    {target-point : B}
    (height : Nat.ℕ)
  → PointedSplitEmbedding A source-point B target-point
  → PointedSplitEmbedding
      (IteratedLoop height A source-point)
      (iteratedLoopPoint height A source-point)
      (IteratedLoop height B target-point)
      (iteratedLoopPoint height B target-point)
iteratePointedSplitEmbedding Nat.zero embedding = embedding
iteratePointedSplitEmbedding (Nat.suc height) embedding =
  iteratePointedSplitEmbedding height
    (liftPointedSplitEmbedding embedding)

iteratedLoopEmbedding :
    {source-point : A}
    {target-point : B}
    (height : Nat.ℕ)
  → PointedSplitEmbedding A source-point B target-point
  → Split.SplitEmbedding
      (IteratedLoop height A source-point)
      (IteratedLoop height B target-point)
iteratedLoopEmbedding height embedding =
  splitEmbedding (iteratePointedSplitEmbedding height embedding)

iteratedLoopEmbedding-point-computes :
    {source-point : A}
    {target-point : B}
    (height : Nat.ℕ)
    (embedding : PointedSplitEmbedding A source-point B target-point)
  → Split.include (iteratedLoopEmbedding height embedding)
      (iteratedLoopPoint height A source-point)
      Cubical.≡
    iteratedLoopPoint height B target-point
iteratedLoopEmbedding-point-computes height embedding =
  include-point (iteratePointedSplitEmbedding height embedding)

iteratedLoopEmbedding-nonbase :
    {source-point : A}
    {target-point : B}
    (height : Nat.ℕ)
    (embedding : PointedSplitEmbedding A source-point B target-point)
    (cell : IteratedLoop height A source-point)
  → (cell Cubical.≡ iteratedLoopPoint height A source-point → ⊥)
  → Split.include (iteratedLoopEmbedding height embedding) cell
      Cubical.≡ iteratedLoopPoint height B target-point
  → ⊥
iteratedLoopEmbedding-nonbase height embedding cell =
  preserves-nonbase
    (iteratePointedSplitEmbedding height embedding)
    cell

------------------------------------------------------------------------
-- h-levels and iterated loops

iteratedLoop-isProp :
    (height : Nat.ℕ)
    (point : A)
  → HLevels.isOfHLevel (Nat.suc (Nat.suc height)) A
  → Cubical.isProp
      (IteratedLoop (Nat.suc height) A point)
iteratedLoop-isProp Nat.zero point hlevel =
  hlevel point point
iteratedLoop-isProp
    (Nat.suc height) point hlevel =
  iteratedLoop-isProp
    height Cubical.refl (hlevel point point)
