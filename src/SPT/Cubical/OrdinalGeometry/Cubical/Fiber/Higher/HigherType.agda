{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.HigherType
  where

-- One small type containing every K(ℤ,n): HigherType = Π n. K(ℤ,n).  Each
-- coordinate is a pointed split retract of it, so every cell of
-- EilenbergMacLane lies over the one point 0.

open import Agda.Primitive using (Level; lzero)
open import Data.Empty using (⊥)
import Data.Nat.Base as Nat

import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.EilenbergMacLane
  as EMLadder
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.IteratedLoop
  as Iterated
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.SplitEmbedding
  as Split

import Cubical.Foundations.Prelude as Cubical

------------------------------------------------------------------------
-- The type

--   HigherType = Π(n : ℕ). K(ℤ,n), pointed by 0 in every coordinate.

HigherType : Set lzero
HigherType = (height : Nat.ℕ) → EMLadder.EMType height

higherTypePoint : HigherType
higherTypePoint height = EMLadder.EMPoint height

------------------------------------------------------------------------
-- Updating one coordinate

pointUpdate :
    {ℓ : Level}
    {family : Nat.ℕ → Set ℓ}
  → ((index : Nat.ℕ) → family index)
  → (selected : Nat.ℕ)
  → family selected
  → (index : Nat.ℕ)
  → family index
pointUpdate base Nat.zero selected-point Nat.zero = selected-point
pointUpdate base Nat.zero selected-point (Nat.suc index) =
  base (Nat.suc index)
pointUpdate base (Nat.suc selected) selected-point Nat.zero =
  base Nat.zero
pointUpdate {family = family}
    base (Nat.suc selected) selected-point (Nat.suc index) =
  pointUpdate
    {family = λ inner → family (Nat.suc inner)}
    (λ inner → base (Nat.suc inner))
    selected selected-point index

pointUpdate-selected-computes :
    {ℓ : Level}
    {family : Nat.ℕ → Set ℓ}
    (base : (index : Nat.ℕ) → family index)
    (selected : Nat.ℕ)
    (selected-point : family selected)
  → pointUpdate base selected selected-point selected
      Cubical.≡ selected-point
pointUpdate-selected-computes base Nat.zero selected-point = Cubical.refl
pointUpdate-selected-computes {family = family}
    base (Nat.suc selected) selected-point =
  pointUpdate-selected-computes
    {family = λ inner → family (Nat.suc inner)}
    (λ inner → base (Nat.suc inner))
    selected selected-point

pointUpdate-base-pointwise :
    {ℓ : Level}
    {family : Nat.ℕ → Set ℓ}
    (base : (index : Nat.ℕ) → family index)
    (selected index : Nat.ℕ)
  → pointUpdate base selected (base selected) index
      Cubical.≡ base index
pointUpdate-base-pointwise base Nat.zero Nat.zero = Cubical.refl
pointUpdate-base-pointwise base Nat.zero (Nat.suc index) = Cubical.refl
pointUpdate-base-pointwise base (Nat.suc selected) Nat.zero = Cubical.refl
pointUpdate-base-pointwise {family = family}
    base (Nat.suc selected) (Nat.suc index) =
  pointUpdate-base-pointwise
    {family = λ inner → family (Nat.suc inner)}
    (λ inner → base (Nat.suc inner))
    selected index

pointUpdate-base-computes :
    {ℓ : Level}
    {family : Nat.ℕ → Set ℓ}
    (base : (index : Nat.ℕ) → family index)
    (selected : Nat.ℕ)
  → pointUpdate base selected (base selected) Cubical.≡ base
pointUpdate-base-computes base selected =
  Cubical.funExt (pointUpdate-base-pointwise base selected)

------------------------------------------------------------------------
-- Each K(ℤ,n) is a retract

coordinateSplitEmbedding :
    (height : Nat.ℕ)
  → Split.SplitEmbedding (EMLadder.EMType height) HigherType
coordinateSplitEmbedding height =
  Split.split-embedding
    (pointUpdate higherTypePoint height)
    (λ whole → whole height)
    (pointUpdate-selected-computes higherTypePoint height)

coordinatePointedSplitEmbedding :
    (height : Nat.ℕ)
  → Iterated.PointedSplitEmbedding
      (EMLadder.EMType height)
      (EMLadder.EMPoint height)
      HigherType
      higherTypePoint
coordinatePointedSplitEmbedding height =
  Iterated.pointed-split-embedding
    (coordinateSplitEmbedding height)
    (pointUpdate-base-computes higherTypePoint height)

------------------------------------------------------------------------
-- Cells at every height

-- higherCell(n) : L(n, HigherType, 0) is not refl; it changes only
-- coordinate n.

higherCell :
    (height : Nat.ℕ)
  → Iterated.IteratedLoop height HigherType higherTypePoint
higherCell height =
  Split.include
    (Iterated.iteratedLoopEmbedding height
      (coordinatePointedSplitEmbedding height))
    (EMLadder.emCell height)

higherCell-nontrivial :
    (height : Nat.ℕ)
  → higherCell height Cubical.≡
      Iterated.iteratedLoopPoint height HigherType higherTypePoint
  → ⊥
higherCell-nontrivial height =
  Iterated.iteratedLoopEmbedding-nonbase
    height
    (coordinatePointedSplitEmbedding height)
    (EMLadder.emCell height)
    (EMLadder.emCell-nontrivial height)
