{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.PointedUniverse
  where

-- One pointed small type, RigidPointedType = (𝟐 × HigherType , (false , 0)),
-- whose iterated loops in the pointed universe contain every cell of
-- HigherType.  Translation acts on the component marked true, the base
-- point lies in the other, and transporting a marked point recovers the
-- translation.

open import Agda.Primitive using (lzero)
open import Data.Bool using (Bool; false; true)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₂)
import Data.Nat.Base as Nat

import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Position
  as Position
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.HigherType
  as Higher
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.IteratedLoop
  as Iterated
import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.SplitEmbedding
  as Split

import Cubical.Algebra.AbGroup.Instances.Int as IntegerAbGroup
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.Isomorphism as Isomorphism
import Cubical.Foundations.Pointed.Base as Pointed
import Cubical.Foundations.Prelude as Cubical
import Cubical.Foundations.Univalence as Univalence
import Cubical.Homotopy.EilenbergMacLane.GroupStructure as EMGroup
import Cubical.Structures.Pointed as PointedStructure

------------------------------------------------------------------------
-- Translations of HigherType

higherTranslationIso :
    Higher.HigherType
  → Isomorphism.Iso Higher.HigherType Higher.HigherType
Isomorphism.Iso.fun (higherTranslationIso translation) whole height =
  Isomorphism.Iso.fun
    (EMGroup.addIso
      {G = IntegerAbGroup.ℤAbGroup}
      height
      (translation height))
    (whole height)
Isomorphism.Iso.inv (higherTranslationIso translation) whole height =
  Isomorphism.Iso.inv
    (EMGroup.addIso
      {G = IntegerAbGroup.ℤAbGroup}
      height
      (translation height))
    (whole height)
Isomorphism.Iso.rightInv (higherTranslationIso translation) whole =
  Cubical.funExt λ height →
    Isomorphism.Iso.rightInv
      (EMGroup.addIso
        {G = IntegerAbGroup.ℤAbGroup}
        height
        (translation height))
      (whole height)
Isomorphism.Iso.leftInv (higherTranslationIso translation) whole =
  Cubical.funExt λ height →
    Isomorphism.Iso.leftInv
      (EMGroup.addIso
        {G = IntegerAbGroup.ℤAbGroup}
        height
        (translation height))
      (whole height)

higherTranslation-zero-input :
    (translation : Higher.HigherType)
  → Isomorphism.Iso.fun (higherTranslationIso translation)
      Higher.higherTypePoint
      Cubical.≡ translation
higherTranslation-zero-input translation =
  Cubical.funExt λ height →
    EMGroup.lUnitₖ
      {G = IntegerAbGroup.ℤAbGroup}
      height
      (translation height)

------------------------------------------------------------------------
-- The pointed type and its twists

RigidCarrier : Set
RigidCarrier = Bool × Higher.HigherType

rigidBase : RigidCarrier
rigidBase = false , Higher.higherTypePoint

rigidMarkedPoint : RigidCarrier
rigidMarkedPoint = true , Higher.higherTypePoint

truePoint : Higher.HigherType → RigidCarrier
truePoint whole = true , whole

RigidPointedType : Position.PointedType lzero
RigidPointedType = RigidCarrier Cubical., rigidBase

twistIso :
    Higher.HigherType
  → Isomorphism.Iso RigidCarrier RigidCarrier
Isomorphism.Iso.fun (twistIso translation) (false , whole) = false , whole
Isomorphism.Iso.fun (twistIso translation) (true , whole) =
  true , Isomorphism.Iso.fun (higherTranslationIso translation) whole
Isomorphism.Iso.inv (twistIso translation) (false , whole) = false , whole
Isomorphism.Iso.inv (twistIso translation) (true , whole) =
  true , Isomorphism.Iso.inv (higherTranslationIso translation) whole
Isomorphism.Iso.rightInv (twistIso translation) (false , whole) =
  Cubical.refl
Isomorphism.Iso.rightInv (twistIso translation) (true , whole) =
  Cubical.cong truePoint
    (Isomorphism.Iso.rightInv (higherTranslationIso translation) whole)
Isomorphism.Iso.leftInv (twistIso translation) (false , whole) =
  Cubical.refl
Isomorphism.Iso.leftInv (twistIso translation) (true , whole) =
  Cubical.cong truePoint
    (Isomorphism.Iso.leftInv (higherTranslationIso translation) whole)

twistEquivalence :
    Higher.HigherType
  → RigidCarrier Equiv.≃ RigidCarrier
twistEquivalence translation =
  Isomorphism.isoToEquiv (twistIso translation)

twistPointedEquivalence :
    Higher.HigherType
  → Pointed._≃∙_ RigidPointedType RigidPointedType
twistPointedEquivalence translation =
  twistEquivalence translation Cubical., Cubical.refl

twistPointedPath :
    Higher.HigherType
  → RigidPointedType Cubical.≡ RigidPointedType
twistPointedPath translation =
  PointedStructure.pointed-sip
    RigidPointedType RigidPointedType
    (twistPointedEquivalence translation)

------------------------------------------------------------------------
-- Recovering a translation

recoverHigher :
    Iterated.Loop
      (Position.PointedType lzero)
      RigidPointedType
  → Higher.HigherType
recoverHigher loop =
  proj₂
    (Cubical.transport
      (Cubical.cong Cubical.fst loop)
      rigidMarkedPoint)

recover-twistPointedPath :
    (translation : Higher.HigherType)
  → recoverHigher (twistPointedPath translation)
      Cubical.≡ translation
recover-twistPointedPath translation =
  Cubical.cong proj₂
    (Univalence.uaβ (twistEquivalence translation) rigidMarkedPoint)
  Cubical.∙
  higherTranslation-zero-input translation

twistLoopSplitEmbedding :
  Split.SplitEmbedding
    Higher.HigherType
    (Iterated.Loop
      (Position.PointedType lzero)
      RigidPointedType)
twistLoopSplitEmbedding =
  Split.split-embedding
    twistPointedPath
    recoverHigher
    recover-twistPointedPath

------------------------------------------------------------------------
-- The zero translation gives refl

twistZeroFunctionPath :
    Equiv.equivFun (twistEquivalence Higher.higherTypePoint)
      Cubical.≡
    (λ point → point)
twistZeroFunctionPath interval (false , whole) = false , whole
twistZeroFunctionPath interval (true , whole) =
  true
  ,
  (λ height →
    EMGroup.rUnitₖ
      {G = IntegerAbGroup.ℤAbGroup}
      height
      (whole height)
      interval)

twistZeroEquivalencePath :
    twistEquivalence Higher.higherTypePoint
      Cubical.≡ Equiv.idEquiv RigidCarrier
twistZeroEquivalencePath = Equiv.equivEq twistZeroFunctionPath

twistZeroPointedEquivalencePath :
    twistPointedEquivalence Higher.higherTypePoint
      Cubical.≡ Pointed.idEquiv∙ RigidPointedType
twistZeroPointedEquivalencePath interval =
  twistZeroEquivalencePath interval Cubical., Cubical.refl

twistPointedPath-zero :
    twistPointedPath Higher.higherTypePoint Cubical.≡ Cubical.refl
twistPointedPath-zero =
  Cubical.cong
    (PointedStructure.pointed-sip
      RigidPointedType RigidPointedType)
    twistZeroPointedEquivalencePath
  Cubical.∙
  PointedStructure.pointed-sip-idEquiv∙ RigidPointedType

twistLoopPointedSplitEmbedding :
  Iterated.PointedSplitEmbedding
    Higher.HigherType
    Higher.higherTypePoint
    (Iterated.Loop
      (Position.PointedType lzero)
      RigidPointedType)
    Cubical.refl
twistLoopPointedSplitEmbedding =
  Iterated.pointed-split-embedding
    twistLoopSplitEmbedding
    twistPointedPath-zero

------------------------------------------------------------------------
-- Cells in the pointed universe

-- pointedUniverseCell(n) : L(n+1, PointedType 0, RigidPointedType) is not
-- refl, for every n.

higherEmbedding :
    (height : Nat.ℕ)
  → Iterated.PointedSplitEmbedding
      (Iterated.IteratedLoop height
        Higher.HigherType Higher.higherTypePoint)
      (Iterated.iteratedLoopPoint height
        Higher.HigherType Higher.higherTypePoint)
      (Iterated.IteratedLoop (Nat.suc height)
        (Position.PointedType lzero)
        RigidPointedType)
      (Iterated.iteratedLoopPoint (Nat.suc height)
        (Position.PointedType lzero)
        RigidPointedType)
higherEmbedding height =
  Iterated.iteratePointedSplitEmbedding height
    twistLoopPointedSplitEmbedding

pointedUniverseCell :
    (height : Nat.ℕ)
  → Iterated.IteratedLoop (Nat.suc height)
      (Position.PointedType lzero)
      RigidPointedType
pointedUniverseCell height =
  Split.include
    (Iterated.splitEmbedding
      (higherEmbedding height))
    (Higher.higherCell height)

pointedUniverseCell-nontrivial :
    (height : Nat.ℕ)
  → pointedUniverseCell height Cubical.≡
      Iterated.iteratedLoopPoint (Nat.suc height)
        (Position.PointedType lzero)
        RigidPointedType
  → ⊥
pointedUniverseCell-nontrivial height =
  Iterated.preserves-nonbase
    (higherEmbedding height)
    (Higher.higherCell height)
    (Higher.higherCell-nontrivial height)
