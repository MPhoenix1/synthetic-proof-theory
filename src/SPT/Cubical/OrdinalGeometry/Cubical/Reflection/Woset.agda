{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Woset where

-- Presentations of well-ordered sets: a Cubical well-order with strict
-- trichotomy and a partial enumeration is the order type of a presentation
-- on its own carrier.  Decidability of the strict order gives trichotomy.

open import Agda.Primitive using (Level)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Properties as MaybeProperties
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Relation.Binary.PropositionalEquality as InductiveEquality

import SPT.Cubical.Core.WellFounded as Accessibility
import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Countability
  as Countability
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType as Reflection

import Cubical.Data.Empty as CubicalEmpty
import Cubical.Data.Equality.Conversion as EqualityConversion
import Cubical.Data.Nat.Order.Recursive as NatOrder
import Cubical.Foundations.Equiv as CubicalEquiv
import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Isomorphism as CubicalIso
import Cubical.Foundations.Prelude as Cubical
import Cubical.HITs.SetQuotients as Quotient
import Cubical.Induction.WellFounded as CubicalAcc
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Extensionality as Extensionality
import Cubical.Relation.Nullary as Nullary

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- Trichotomy and decidability

WosetCarrier : Woset.Woset ℓ ℓ → Set ℓ
WosetCarrier order = Cubical.fst order

WosetStrict :
    (order : Woset.Woset ℓ ℓ)
  → WosetCarrier order → WosetCarrier order → Set ℓ
WosetStrict order = Woset.WosetStr._≺_ (Cubical.snd order)

-- Strict trichotomy, Π x y. x < y + (x = y + y < x), as a hypothesis on a
-- well-order; constructively it does not follow from the well-order laws.

StrictTrichotomy : (order : Woset.Woset ℓ ℓ) → Set ℓ
StrictTrichotomy order =
  (x y : WosetCarrier order) →
  WosetStrict order x y
    ⊎ (x Cubical.≡ y ⊎ WosetStrict order y x)

-- Decidability of the strict order, Π x y. Dec(x < y), as a hypothesis.

WosetStrictDecidable : (order : Woset.Woset ℓ ℓ) → Set ℓ
WosetStrictDecidable order =
  (x y : WosetCarrier order) →
  Nullary.Dec (WosetStrict order x y)

-- Decidability gives trichotomy: if neither x < y nor y < x, induction
-- shows that x and y have the same predecessors, and extensionality makes
-- them equal.

decidable→trichotomy :
    (order : Woset.Woset ℓ ℓ)
  → WosetStrictDecidable order
  → StrictTrichotomy order
decidable→trichotomy {ℓ} order decide =
  CubicalAcc.WFI.induction well
    (λ x smaller-x →
      CubicalAcc.WFI.induction well
        (λ y smaller-y → compare x smaller-x y smaller-y))
  where
    A : Set ℓ
    A = WosetCarrier order

    _<_ : A → A → Set ℓ
    _<_ = WosetStrict order

    wos : Woset.IsWoset _<_
    wos = Woset.WosetStr.isWoset (Cubical.snd order)

    well : CubicalAcc.WellFounded _<_
    well = Woset.IsWoset.is-well-founded wos

    prop-valued : (x y : A) → Cubical.isProp (x < y)
    prop-valued = Woset.IsWoset.is-prop-valued wos

    transitive : (x y z : A) → x < y → y < z → x < z
    transitive = Woset.IsWoset.is-trans wos

    Tri : A → A → Set ℓ
    Tri x y = x < y ⊎ (x Cubical.≡ y ⊎ y < x)

    lower-forward :
        (x : A)
      → ((z : A) → z < x → (y : A) → Tri z y)
      → (y : A)
      → (x < y → CubicalEmpty.⊥)
      → (y < x → CubicalEmpty.⊥)
      → (z : A)
      → z < x
      → z < y
    lower-forward x smaller-x y x≮y y≮x z z<x
        with smaller-x z z<x y
    ... | inj₁ z<y = z<y
    ... | inj₂ (inj₁ z=y) =
      CubicalEmpty.rec
        (y≮x (Cubical.subst (λ point → point < x) z=y z<x))
    ... | inj₂ (inj₂ y<z) =
      CubicalEmpty.rec (y≮x (transitive y z x y<z z<x))

    lower-backward :
        (x : A)
      → (y : A)
      → ((z : A) → z < y → Tri x z)
      → (x < y → CubicalEmpty.⊥)
      → (y < x → CubicalEmpty.⊥)
      → (z : A)
      → z < y
      → z < x
    lower-backward x y smaller-y x≮y y≮x z z<y
        with smaller-y z z<y
    ... | inj₁ x<z =
      CubicalEmpty.rec (x≮y (transitive x z y x<z z<y))
    ... | inj₂ (inj₁ x=z) =
      CubicalEmpty.rec
        (x≮y
          (Cubical.subst (λ point → point < y)
            (Cubical.sym x=z) z<y))
    ... | inj₂ (inj₂ z<x) = z<x

    compare :
        (x : A)
      → ((z : A) → z < x → (y : A) → Tri z y)
      → (y : A)
      → ((z : A) → z < y → Tri x z)
      → Tri x y
    compare x smaller-x y smaller-y with decide x y
    ... | Nullary.yes x<y = inj₁ x<y
    ... | Nullary.no x≮y with decide y x
    ... | Nullary.yes y<x = inj₂ (inj₂ y<x)
    ... | Nullary.no y≮x =
      inj₂
        (inj₁
          (Extensionality.isWeaklyExtensional→≺Equiv→≡
            _<_
            (Woset.IsWoset.is-weakly-extensional wos)
            x y
            (λ z →
              CubicalEquiv.propBiimpl→Equiv
                (prop-valued z x)
                (prop-valued z y)
                (lower-forward x smaller-x y x≮y y≮x z)
                (lower-backward x y smaller-y x≮y y≮x z))))

------------------------------------------------------------------------
-- Accessibility and discreteness

cubicalAcc→Acc :
    ∀ {ℓA ℓR : Level}
      {A : Set ℓA}
      {R : A → A → Set ℓR}
      {x : A}
  → CubicalAcc.Acc R x
  → Accessibility.Acc R x
cubicalAcc→Acc (CubicalAcc.acc smaller) =
  Accessibility.acc
    (λ y y<x → cubicalAcc→Acc (smaller y y<x))

discreteMaybe :
    ∀ {ℓA : Level} {A : Set ℓA}
  → Nullary.Discrete A
  → Nullary.Discrete (Maybe A)
discreteMaybe discreteA nothing nothing =
  Nullary.yes Cubical.refl
discreteMaybe discreteA (just x) nothing =
  Nullary.no
    (λ path → just≠nothing (EqualityConversion.pathToEq path))
  where
    just≠nothing :
      (just x InductiveEquality.≡ nothing) → CubicalEmpty.⊥
    just≠nothing ()
discreteMaybe discreteA nothing (just y) =
  Nullary.no
    (λ path → nothing≠just (EqualityConversion.pathToEq path))
  where
    nothing≠just :
      (nothing InductiveEquality.≡ just y) → CubicalEmpty.⊥
    nothing≠just ()
discreteMaybe discreteA (just x) (just y)
    with discreteA x y
... | Nullary.yes x=y =
  Nullary.yes (Cubical.cong just x=y)
... | Nullary.no x≠y =
  Nullary.no
    (λ just-x=just-y →
      x≠y
        (EqualityConversion.eqToPath
          (MaybeProperties.just-injective
            (EqualityConversion.pathToEq just-x=just-y))))

wosetCarrier-discrete :
    (order : Woset.Woset ℓ ℓ)
  → StrictTrichotomy order
  → Nullary.Discrete (WosetCarrier order)
wosetCarrier-discrete order trichotomy x y
    with trichotomy x y
... | inj₁ x<y =
  Nullary.no
    (CubicalAcc.wf→x<y→x≢y
      (Woset.IsWoset.is-well-founded
        (Woset.WosetStr.isWoset (Cubical.snd order)))
      x<y)
... | inj₂ (inj₁ x=y) = Nullary.yes x=y
... | inj₂ (inj₂ y<x) =
  Nullary.no
    (λ x=y →
      CubicalAcc.wf→x<y→x≢y
        (Woset.IsWoset.is-well-founded
          (Woset.WosetStr.isWoset (Cubical.snd order)))
        y<x
        (Cubical.sym x=y))

------------------------------------------------------------------------
-- The least index of a point

enumerationHit :
    (order : Woset.Woset ℓ ℓ)
  → (trichotomy : StrictTrichotomy order)
  → (enumeration : Countability.PartialEnumeration (WosetCarrier order))
  → (point : WosetCarrier order)
  → Σ ℕ (λ index →
      Countability.sequence enumeration index Cubical.≡ just point)
enumerationHit order trichotomy enumeration point =
  Nullary.Collapsible→SplitSupport
    (NatOrder.Decidable→Collapsible
      (λ index →
        Nullary.Discrete→isSet
          (discreteMaybe
            (wosetCarrier-discrete order trichotomy))
          (Countability.sequence enumeration index)
          (just point))
      (λ index →
        discreteMaybe
          (wosetCarrier-discrete order trichotomy)
          (Countability.sequence enumeration index)
          (just point)))
    (Countability.covers enumeration point)

------------------------------------------------------------------------
-- The presentation of a well-order

-- A well-order A with trichotomy and a partial enumeration of its carrier
-- is presented on |A| itself: equality as ≈, the order of A, and Cubical
-- accessibility converted to Acc.  Trichotomy makes the carrier discrete,
-- so the least index at which a point is enumerated can be computed, with
-- no choice.

toPresentation :
    (order : Woset.Woset ℓ ℓ)
  → StrictTrichotomy order
  → Countability.PartialEnumeration (WosetCarrier order)
  → Presented.CountableOrdinal𝒫 ℓ
toPresentation order trichotomy enumeration = record
  { X = WosetCarrier order
  ; _≈_ = Cubical._≡_
  ; _<_ = WosetStrict order
  ; ≈-refl = λ _ → Cubical.refl
  ; ≈-sym = Cubical.sym
  ; ≈-trans = Cubical._∙_
  ; <-trans =
      λ {x} {y} {z} →
        Woset.IsWoset.is-trans
          (Woset.WosetStr.isWoset (Cubical.snd order))
          x y z
  ; <-respˡ-≈ =
      λ {x} {x′} {y} x=x′ x<y →
        Cubical.subst (λ point → WosetStrict order point y) x=x′ x<y
  ; <-respʳ-≈ =
      λ {x} {y} {y′} y=y′ x<y →
        Cubical.subst (WosetStrict order x) y=y′ x<y
  ; <-wf =
      λ point →
        cubicalAcc→Acc
          (Woset.IsWoset.is-well-founded
            (Woset.WosetStr.isWoset (Cubical.snd order))
            point)
  ; compare = trichotomy
  ; enum = Countability.sequence enumeration
  ; covers =
      λ point →
        let hit = enumerationHit
                    order trichotomy enumeration point
        in Cubical.fst hit
         , point
         , EqualityConversion.pathToEq (Cubical.snd hit)
         , Cubical.refl
  }

------------------------------------------------------------------------
-- Its order type is A

carrierIso :
    (order : Woset.Woset ℓ ℓ)
  → (trichotomy : StrictTrichotomy order)
  → (enumeration : Countability.PartialEnumeration (WosetCarrier order))
  → CubicalIso.Iso
      (Reflection.Class
        (toPresentation
          order trichotomy enumeration))
      (WosetCarrier order)
carrierIso order trichotomy enumeration = record
  { fun =
      Quotient.rec
        (Woset.IsWoset.is-set
          (Woset.WosetStr.isWoset (Cubical.snd order)))
        (λ point → point)
        (λ _ _ point-path → point-path)
  ; inv = λ point → Quotient.[ point ]
  ; rightInv = λ _ → Cubical.refl
  ; leftInv =
      Quotient.elimProp
        (λ quotient-point → Quotient.squash/ _ quotient-point)
        (λ _ → Cubical.refl)
  }

carrierEquiv :
    (order : Woset.Woset ℓ ℓ)
  → (trichotomy : StrictTrichotomy order)
  → (enumeration : Countability.PartialEnumeration (WosetCarrier order))
  → Reflection.Class
      (toPresentation
        order trichotomy enumeration)
      CubicalEquiv.≃
      WosetCarrier order
carrierEquiv order trichotomy enumeration =
  CubicalIso.isoToEquiv
    (carrierIso order trichotomy enumeration)

-- ord(toPresentation A) = A, as well-orders.

toPresentation-orderType :
    (order : Woset.Woset ℓ ℓ)
  → (trichotomy : StrictTrichotomy order)
  → (enumeration : Countability.PartialEnumeration (WosetCarrier order))
  → Reflection.orderType
      (toPresentation
        order trichotomy enumeration)
      Cubical.≡ order
toPresentation-orderType {ℓ} order trichotomy enumeration =
  CubicalEquiv.equivFun
    (Woset.WosetPath _ _)
    ( carrierEquivalence
    , Woset.makeIsWosetEquiv
        carrierEquivalence
        relation-forward
        relation-backward
    )
  where
    presentation : Presented.CountableOrdinal𝒫 ℓ
    presentation =
      toPresentation
        order trichotomy enumeration

    carrierEquivalence :
      Reflection.Class presentation
        CubicalEquiv.≃ WosetCarrier order
    carrierEquivalence =
      carrierEquiv order trichotomy enumeration

    relation-forward :
        (left right : Reflection.Class presentation)
      → Reflection.Less presentation left right
      → WosetStrict order
          (CubicalEquiv.equivFun carrierEquivalence left)
          (CubicalEquiv.equivFun carrierEquivalence right)
    relation-forward =
      Quotient.elimProp2
        (λ left right →
          HLevels.isPropΠ λ _ →
            Woset.IsWoset.is-prop-valued
              (Woset.WosetStr.isWoset (Cubical.snd order))
              (CubicalEquiv.equivFun carrierEquivalence left)
              (CubicalEquiv.equivFun carrierEquivalence right))
        (λ left right →
          Reflection.Less-witness presentation)

    relation-backward :
        (left right : WosetCarrier order)
      → WosetStrict order left right
      → Reflection.Less presentation
          (CubicalEquiv.invEq carrierEquivalence left)
          (CubicalEquiv.invEq carrierEquivalence right)
    relation-backward left right =
      Reflection.Less-intro presentation
