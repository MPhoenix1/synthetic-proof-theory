{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Bridge where

-- The bridge from Cubical well-ordered sets to the ordinals of
-- TypeTopology's `Ordinals.Type`: carrier and strict relation are kept, and
-- only the laws, which mention equality and accessibility, are converted
-- between the two libraries.

open import Agda.Primitive using (Level; lsuc)
open import Level using (Lift; lift; lower)

import Agda.Builtin.Equality as AgdaEquality
import Cubical.Data.Equality.Conversion as EqualityConversion
import Cubical.Foundations.Equiv as CubicalEquiv
import Cubical.Foundations.Prelude as Cubical
import Cubical.Induction.WellFounded as CubicalWellFounded
import Cubical.Relation.Binary.Extensionality as CubicalExtensionality
import Cubical.Relation.Binary.Order.Woset.Base as Woset

import SPT.Cubical.TypeTopology.MLTT.Identity-Type as TypeTopologyIdentity
import SPT.Cubical.TypeTopology.MLTT.Sigma-Type as TypeTopologySigma
import SPT.Cubical.TypeTopology.Ordinals.Notions as TypeTopologyNotions
import SPT.Cubical.TypeTopology.Ordinals.Type as TypeTopologyOrdinal
import SPT.Cubical.TypeTopology.UF.Subsingletons as TypeTopologyPropositions

private
  variable
    ℓ ℓ-carrier ℓ-relation : Level
    A : Set ℓ-carrier
    _<_ : A → A → Set ℓ-relation
    x y : A

------------------------------------------------------------------------
-- Equality and accessibility

-- Conversions between Agda's ≡, TypeTopology's identity type ＝ and Cubical
-- paths, each by induction, with the round trips that are needed.

≡→＝ :
    {x y : A}
  → AgdaEquality._≡_ x y
  → TypeTopologyIdentity._＝_ x y
≡→＝ AgdaEquality.refl =
  TypeTopologyIdentity.refl

＝→≡ :
    {x y : A}
  → TypeTopologyIdentity._＝_ x y
  → AgdaEquality._≡_ x y
＝→≡ TypeTopologyIdentity.refl =
  AgdaEquality.refl

≡→＝→≡ :
    {x y : A}
    (identification : AgdaEquality._≡_ x y)
  → AgdaEquality._≡_
      (＝→≡
        (≡→＝ identification))
      identification
≡→＝→≡
    AgdaEquality.refl = AgdaEquality.refl

path→＝ :
    {x y : A}
  → x Cubical.≡ y
  → TypeTopologyIdentity._＝_ x y
path→＝ path =
  ≡→＝
    (EqualityConversion.pathToEq path)

＝→path :
    {x y : A}
  → TypeTopologyIdentity._＝_ x y
  → x Cubical.≡ y
＝→path identification =
  EqualityConversion.eqToPath
    (＝→≡ identification)

path→＝→path :
    {x y : A}
    (path : x Cubical.≡ y)
  → ＝→path
      (path→＝ path)
      Cubical.≡ path
path→＝→path {x = x} =
  λ path →
    Cubical.cong EqualityConversion.eqToPath
      (EqualityConversion.eqToPath
        (≡→＝→≡
          (EqualityConversion.pathToEq path)))
    Cubical.∙
    EqualityConversion.eqToPath-pathToEq path

isProp→is-prop :
    (P : Set ℓ)
  → Cubical.isProp P
  → TypeTopologyPropositions.is-prop P
isProp→is-prop P proposition left right =
  path→＝ (proposition left right)

-- Cubical accessibility gives TypeTopology accessibility, by recursion on the
-- accessibility proof.

acc→is-accessible :
    {x : A}
  → CubicalWellFounded.Acc _<_ x
  → TypeTopologyNotions.is-accessible _<_ x
acc→is-accessible
    (CubicalWellFounded.acc predecessors) =
  TypeTopologyNotions.acc
    (λ predecessor relation →
      acc→is-accessible
        (predecessors predecessor relation))

wf→is-well-founded :
    CubicalWellFounded.WellFounded _<_
  → TypeTopologyNotions.is-well-founded _<_
wf→is-well-founded well-founded point =
  acc→is-accessible (well-founded point)

------------------------------------------------------------------------
-- The TypeTopology ordinal of a well-order

-- The carrier and the strict relation of a well-order.

wosetCarrier : Woset.Woset ℓ-carrier ℓ-relation → Set ℓ-carrier
wosetCarrier order = Cubical.fst order

wosetRelation :
    (order : Woset.Woset ℓ-carrier ℓ-relation)
  → wosetCarrier order
  → wosetCarrier order
  → Set ℓ-relation
wosetRelation order =
  Woset.WosetStr._≺_ (Cubical.snd order)

-- toOrdinal : Woset ℓ ℓ → Ordinal ℓ, with the same carrier and relation.
-- Extensionality goes through a Cubical path, then converts it to ＝.

toOrdinal :
  Woset.Woset ℓ ℓ → TypeTopologyOrdinal.Ordinal ℓ
toOrdinal order =
  TypeTopologySigma._,_
    (wosetCarrier order)
    (TypeTopologySigma._,_
      (wosetRelation order)
      (TypeTopologySigma._,_
        proposition-valued
        (TypeTopologySigma._,_
          well-founded
          (TypeTopologySigma._,_ extensional transitive))))
  where
  structure : Woset.IsWoset (wosetRelation order)
  structure = Woset.WosetStr.isWoset (Cubical.snd order)

  proposition-valued :
    TypeTopologyNotions.is-prop-valued (wosetRelation order)
  proposition-valued left right =
    isProp→is-prop
      (wosetRelation order left right)
      (Woset.IsWoset.is-prop-valued structure left right)

  well-founded :
    TypeTopologyNotions.is-well-founded (wosetRelation order)
  well-founded =
    wf→is-well-founded
      (Woset.IsWoset.is-well-founded structure)

  extensional :
    TypeTopologyNotions.is-extensional (wosetRelation order)
  extensional left right left-below-right right-below-left =
    path→＝
      (CubicalExtensionality.isWeaklyExtensional→≺Equiv→≡
        (wosetRelation order)
        (Woset.IsWoset.is-weakly-extensional structure)
        left right
        (λ predecessor →
          CubicalEquiv.propBiimpl→Equiv
            (Woset.IsWoset.is-prop-valued structure predecessor left)
            (Woset.IsWoset.is-prop-valued structure predecessor right)
            (left-below-right predecessor)
            (right-below-left predecessor)))

  transitive :
    TypeTopologyNotions.is-transitive (wosetRelation order)
  transitive = Woset.IsWoset.is-trans structure

------------------------------------------------------------------------
-- Well-orders with a large carrier and a small relation

liftedSmallWosetRelation :
    (order : Woset.Woset (lsuc ℓ) ℓ)
  → wosetCarrier order
  → wosetCarrier order
  → Set (lsuc ℓ)
liftedSmallWosetRelation {ℓ} order left right =
  Lift (lsuc ℓ) (wosetRelation order left right)

acc→lifted-accessible :
    (order : Woset.Woset (lsuc ℓ) ℓ)
    {point : wosetCarrier order}
  → CubicalWellFounded.Acc (wosetRelation order) point
  → TypeTopologyNotions.is-accessible
      (liftedSmallWosetRelation order) point
acc→lifted-accessible order
    (CubicalWellFounded.acc predecessors) =
  TypeTopologyNotions.acc
    (λ predecessor lifted-relation →
      acc→lifted-accessible order
        (predecessors predecessor (lower lifted-relation)))

-- smallToOrdinal : Woset (lsuc ℓ) ℓ → Ordinal (lsuc ℓ), lifting the
-- relation with Lift, since an ordinal of TypeTopology has carrier and
-- relation in one universe.  It applies to every ω₁ᴳ(G).

smallToOrdinal :
  Woset.Woset (lsuc ℓ) ℓ → TypeTopologyOrdinal.Ordinal (lsuc ℓ)
smallToOrdinal {ℓ} order =
  TypeTopologySigma._,_
    (wosetCarrier order)
    (TypeTopologySigma._,_
      (liftedSmallWosetRelation order)
      (TypeTopologySigma._,_
        proposition-valued
        (TypeTopologySigma._,_
          well-founded
          (TypeTopologySigma._,_ extensional transitive))))
  where
  structure : Woset.IsWoset (wosetRelation order)
  structure = Woset.WosetStr.isWoset (Cubical.snd order)

  lifted-relation-is-proposition :
    (left right : wosetCarrier order) →
    Cubical.isProp (liftedSmallWosetRelation order left right)
  lifted-relation-is-proposition left right first second =
    Cubical.cong lift
      (Woset.IsWoset.is-prop-valued structure left right
        (lower first) (lower second))

  proposition-valued :
    TypeTopologyNotions.is-prop-valued
      (liftedSmallWosetRelation order)
  proposition-valued left right =
    isProp→is-prop
      (liftedSmallWosetRelation order left right)
      (lifted-relation-is-proposition left right)

  well-founded :
    TypeTopologyNotions.is-well-founded
      (liftedSmallWosetRelation order)
  well-founded point =
    acc→lifted-accessible order
      (Woset.IsWoset.is-well-founded structure point)

  extensional :
    TypeTopologyNotions.is-extensional
      (liftedSmallWosetRelation order)
  extensional left right left-below-right right-below-left =
    path→＝
      (CubicalExtensionality.isWeaklyExtensional→≺Equiv→≡
        (wosetRelation order)
        (Woset.IsWoset.is-weakly-extensional structure)
        left right
        (λ predecessor →
          CubicalEquiv.propBiimpl→Equiv
            (Woset.IsWoset.is-prop-valued structure predecessor left)
            (Woset.IsWoset.is-prop-valued structure predecessor right)
            (λ relation →
              lower (left-below-right predecessor (lift relation)))
            (λ relation →
              lower (right-below-left predecessor (lift relation)))))

  transitive :
    TypeTopologyNotions.is-transitive
      (liftedSmallWosetRelation order)
  transitive left middle right left<middle middle<right =
    lift
      (Woset.IsWoset.is-trans structure left middle right
        (lower left<middle) (lower middle<right))
