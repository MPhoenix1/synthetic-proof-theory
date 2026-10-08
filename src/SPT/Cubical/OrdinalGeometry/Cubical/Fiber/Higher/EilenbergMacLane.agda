{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.EilenbergMacLane
  where

-- A nontrivial cell in every iterated loop space of the Eilenberg–MacLane
-- spaces K(ℤ,n), from the equivalence K(ℤ,n) ≃ Ω K(ℤ,n+1).

open import Agda.Primitive using (lzero)
open import Data.Empty using (⊥)
import Data.Nat.Base as Nat

import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.IteratedLoop
  as Iterated
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.SplitEmbedding
  as Split

import Cubical.Algebra.AbGroup.Instances.Int as IntegerAbGroup
import Cubical.Data.Equality.Conversion as EqualityConversion
import Cubical.Data.Int as Integer
import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Isomorphism as Isomorphism
import Cubical.Foundations.Prelude as Cubical
import Cubical.Homotopy.EilenbergMacLane.Base as EM
import Cubical.Homotopy.EilenbergMacLane.Properties as EMProperties

------------------------------------------------------------------------
-- The spaces K(ℤ,n)

EMType : Nat.ℕ → Set lzero
EMType height = EM.EM IntegerAbGroup.ℤAbGroup height

EMPoint : (height : Nat.ℕ) → EMType height
EMPoint height = EM.0ₖ height

-- K(ℤ,n) ◁∗ Ω(K(ℤ,n+1), 0), from the loop equivalence of the cubical
-- library.

emLoopSplitEmbedding :
    (height : Nat.ℕ)
  → Split.SplitEmbedding
      (EMType height)
      (Iterated.Loop (EMType (Nat.suc height))
        (EMPoint (Nat.suc height)))
emLoopSplitEmbedding height =
  Split.split-embedding
    (EMProperties.EM→ΩEM+1
      {G = IntegerAbGroup.ℤAbGroup}
      height)
    (EMProperties.ΩEM+1→EM
      {G = IntegerAbGroup.ℤAbGroup}
      height)
    (Isomorphism.Iso.leftInv
      (EMProperties.Iso-EM-ΩEM+1
        {G = IntegerAbGroup.ℤAbGroup}
        height))

emLoopPointedSplitEmbedding :
    (height : Nat.ℕ)
  → Iterated.PointedSplitEmbedding
      (EMType height)
      (EMPoint height)
      (Iterated.Loop (EMType (Nat.suc height))
        (EMPoint (Nat.suc height)))
      Cubical.refl
emLoopPointedSplitEmbedding height =
  Iterated.pointed-split-embedding
    (emLoopSplitEmbedding height)
    (EMProperties.EM→ΩEM+1-0ₖ
      {G = IntegerAbGroup.ℤAbGroup}
      height)

------------------------------------------------------------------------
-- One nonzero point at height zero

integerOne : EMType Nat.zero
integerOne = Integer.pos (Nat.suc Nat.zero)

integerOne-not-zero : integerOne Cubical.≡ EMPoint Nat.zero → ⊥
integerOne-not-zero path with EqualityConversion.pathToEq path
... | ()

------------------------------------------------------------------------
-- The height-n ladder map

emSuccessorPointedSplitEmbedding :
    (height : Nat.ℕ)
  → Iterated.PointedSplitEmbedding
      (Iterated.IteratedLoop height
        (EMType height)
        (EMPoint height))
      (Iterated.iteratedLoopPoint height
        (EMType height)
        (EMPoint height))
      (Iterated.IteratedLoop (Nat.suc height)
        (EMType (Nat.suc height))
        (EMPoint (Nat.suc height)))
      (Iterated.iteratedLoopPoint (Nat.suc height)
        (EMType (Nat.suc height))
        (EMPoint (Nat.suc height)))
emSuccessorPointedSplitEmbedding height =
  Iterated.iteratePointedSplitEmbedding height
    (emLoopPointedSplitEmbedding height)

------------------------------------------------------------------------
-- A nontrivial canonical cell at every finite height

-- emCell(n) : L(n, K(ℤ,n), 0) is not refl: 1 at height zero, carried up
-- through the loop embedding.

emCell :
    (height : Nat.ℕ)
  → Iterated.IteratedLoop height
      (EMType height)
      (EMPoint height)
emCell Nat.zero = integerOne
emCell (Nat.suc height) =
  Split.include
    (Iterated.splitEmbedding
      (emSuccessorPointedSplitEmbedding height))
    (emCell height)

emCell-nontrivial :
    (height : Nat.ℕ)
  → emCell height Cubical.≡
      Iterated.iteratedLoopPoint height
        (EMType height)
        (EMPoint height)
  → ⊥
emCell-nontrivial Nat.zero = integerOne-not-zero
emCell-nontrivial (Nat.suc height) =
  Iterated.preserves-nonbase
    (emSuccessorPointedSplitEmbedding height)
    (emCell height)
    (emCell-nontrivial height)

------------------------------------------------------------------------
-- An h-level bound for each space

emType-not-lower-hlevel :
    (height : Nat.ℕ)
  → HLevels.isOfHLevel (Nat.suc height) (EMType height)
  → ⊥
emType-not-lower-hlevel Nat.zero em-is-proposition =
  integerOne-not-zero
    (em-is-proposition integerOne (EMPoint Nat.zero))
emType-not-lower-hlevel (Nat.suc height) em-is-lower =
  emCell-nontrivial (Nat.suc height)
    (Iterated.iteratedLoop-isProp
      height
      (EMPoint (Nat.suc height))
      em-is-lower
      (emCell (Nat.suc height))
      (Iterated.iteratedLoopPoint (Nat.suc height)
        (EMType (Nat.suc height))
        (EMPoint (Nat.suc height))))
