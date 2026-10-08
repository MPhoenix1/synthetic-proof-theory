{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType where

-- The order type of a presentation: the set quotient of its carrier by
-- ≈, with the strict order truncated to a proposition,
--
--   ord(P) = (X_P / ≈ₚ ,  [x] < [y] := ‖x <ₚ y‖),
--
-- is a Cubical well-ordered set.  An equivalence of presentations P ≃𝒫 Q
-- gives an equivalence of order types, hence a path ord(P) = ord(Q).

open import Agda.Primitive using (Level)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)

import SPT.Cubical.Core.WellFounded as Accessibility
import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented

import Cubical.Foundations.Prelude as Cubical
import Cubical.Foundations.Equiv as CubicalEquiv
import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Isomorphism as CubicalIso
import Cubical.Foundations.Univalence as Univalence
import Cubical.Data.Sigma.Base as CubicalSigma
import Cubical.Data.Sigma.Properties as SigmaProperties
import Cubical.HITs.PropositionalTruncation as Truncation
import Cubical.HITs.SetQuotients as Quotient
import Cubical.Induction.WellFounded as CubicalAcc
import Cubical.Relation.Binary.Base as BinaryRelation
import Cubical.Relation.Binary.Extensionality as Extensionality
import Cubical.Relation.Binary.Order.Woset.Base as Woset

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- The quotient and its order

-- The points of ord(P): the classes X_P / ≈ₚ.

Class :
  Presented.CountableOrdinal𝒫 ℓ → Set ℓ
Class presentation =
  Quotient._/_
    (Presented.CountableOrdinal𝒫.X presentation)
    (Presented.CountableOrdinal𝒫._≈_ presentation)

Class-isSet :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
  → Cubical.isSet (Class presentation)
Class-isSet presentation =
  Quotient.squash/
    {A = Presented.CountableOrdinal𝒫.X presentation}
    {R = Presented.CountableOrdinal𝒫._≈_ presentation}

≈-isEquivRel :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
  → BinaryRelation.BinaryRelation.isEquivRel
      (Presented.CountableOrdinal𝒫._≈_ presentation)
≈-isEquivRel presentation =
  BinaryRelation.BinaryRelation.equivRel
    (Presented.CountableOrdinal𝒫.≈-refl presentation)
    (λ _ _ → Presented.CountableOrdinal𝒫.≈-sym presentation)
    (λ _ _ _ → Presented.CountableOrdinal𝒫.≈-trans presentation)

-- [x] < [y] is the truncation ‖x <ₚ y‖; it is well defined because <ₚ
-- respects ≈ₚ.

abstract
  private
    LessRightProp :
        (presentation : Presented.CountableOrdinal𝒫 ℓ)
        (left : Presented.CountableOrdinal𝒫.X presentation)
      → Class presentation
      → HLevels.hProp ℓ
    LessRightProp presentation left =
      Quotient.rec
        HLevels.isSetHProp
        (λ right →
          Cubical._,_
            (Truncation.∥
              Presented.CountableOrdinal𝒫._<_ presentation left right ∥₁)
            Truncation.isPropPropTrunc)
        (λ right right′ right≈right′ →
          SigmaProperties.Σ≡Prop
            (λ _ → Cubical.isPropIsProp)
            (Univalence.hPropExt
              Truncation.isPropPropTrunc
              Truncation.isPropPropTrunc
              (Truncation.map
                (Presented.CountableOrdinal𝒫.<-respʳ-≈
                  presentation right≈right′))
              (Truncation.map
                (Presented.CountableOrdinal𝒫.<-respʳ-≈ presentation
                  (Presented.CountableOrdinal𝒫.≈-sym presentation
                    right≈right′)))))

    LessProp :
        (presentation : Presented.CountableOrdinal𝒫 ℓ)
      → Class presentation
      → Class presentation
      → HLevels.hProp ℓ
    LessProp presentation =
      Quotient.rec
        (HLevels.isSetΠ λ _ → HLevels.isSetHProp)
        (LessRightProp presentation)
        (λ left left′ left≈left′ →
          Cubical.funExt λ quotient-right →
            Quotient.elimProp
              (λ right →
                HLevels.isSetHProp
                  (LessRightProp presentation left right)
                  (LessRightProp presentation left′ right))
              (λ right →
                SigmaProperties.Σ≡Prop
                  (λ _ → Cubical.isPropIsProp)
                  (Univalence.hPropExt
                    Truncation.isPropPropTrunc
                    Truncation.isPropPropTrunc
                    (Truncation.map
                      (Presented.CountableOrdinal𝒫.<-respˡ-≈ presentation
                        left≈left′))
                    (Truncation.map
                      (Presented.CountableOrdinal𝒫.<-respˡ-≈ presentation
                        (Presented.CountableOrdinal𝒫.≈-sym presentation
                          left≈left′)))))
              quotient-right)

  Less :
      (presentation : Presented.CountableOrdinal𝒫 ℓ)
    → Class presentation
    → Class presentation
    → Set ℓ
  Less presentation left right =
    Cubical.fst (LessProp presentation left right)

  Less-isProp :
      (presentation : Presented.CountableOrdinal𝒫 ℓ)
      (x y : Class presentation)
    → Cubical.isProp (Less presentation x y)
  Less-isProp presentation x y =
    Cubical.snd (LessProp presentation x y)

  Less-[] :
      (presentation : Presented.CountableOrdinal𝒫 ℓ)
      (x y : Presented.CountableOrdinal𝒫.X presentation)
    → Less presentation (Quotient.[ x ]) (Quotient.[ y ])
        Cubical.≡
      Truncation.∥ Presented.CountableOrdinal𝒫._<_ presentation x y ∥₁
  Less-[] presentation x y = Cubical.refl

Less-intro :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
    {x y : Presented.CountableOrdinal𝒫.X presentation}
  → Presented.CountableOrdinal𝒫._<_ presentation x y
  → Less presentation (Quotient.[ x ]) (Quotient.[ y ])
Less-intro presentation {x} {y} strict =
  Cubical.transport
    (Cubical.sym (Less-[] presentation x y))
    (Truncation.∣ strict ∣₁)

Less-elim :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
    {x y : Presented.CountableOrdinal𝒫.X presentation}
  → Less presentation (Quotient.[ x ]) (Quotient.[ y ])
  → Truncation.∥ Presented.CountableOrdinal𝒫._<_ presentation x y ∥₁
Less-elim presentation {x} {y} =
  Cubical.transport (Less-[] presentation x y)

private
  ordinary-empty-is-prop : Cubical.isProp ⊥
  ordinary-empty-is-prop ()

-- Between two given representatives, comparison recovers an untruncated
-- witness of x <ₚ y from [x] < [y].

Less-witness :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
    {x y : Presented.CountableOrdinal𝒫.X presentation}
  → Less presentation (Quotient.[ x ]) (Quotient.[ y ])
  → Presented.CountableOrdinal𝒫._<_ presentation x y
Less-witness presentation {x} {y} strict
    with Presented.CountableOrdinal𝒫.compare presentation x y
... | inj₁ x<y = x<y
... | inj₂ (inj₁ x≈y) =
  ⊥-elim
    (Truncation.rec
      ordinary-empty-is-prop
      (Presented.Presentation.≈↛< presentation x≈y)
      (Less-elim presentation strict))
... | inj₂ (inj₂ y<x) =
  ⊥-elim
    (Truncation.rec
      ordinary-empty-is-prop
      (λ x<y → Presented.Presentation.<-asym presentation x<y y<x)
      (Less-elim presentation strict))

Less-trans :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
    (x y z : Class presentation)
  → Less presentation x y
  → Less presentation y z
  → Less presentation x z
Less-trans presentation =
  Quotient.elimProp3
    (λ x y z →
      HLevels.isPropΠ2 λ _ _ →
        Less-isProp presentation x z)
    (λ x y z x<y y<z →
      Truncation.rec
        (Less-isProp presentation
          (Quotient.[ x ]) (Quotient.[ z ]))
        (λ strict-x<y →
          Truncation.rec
            (Less-isProp presentation
              (Quotient.[ x ]) (Quotient.[ z ]))
            (λ strict-y<z →
              Less-intro presentation
                (Presented.CountableOrdinal𝒫.<-trans
                  presentation strict-x<y strict-y<z))
            (Less-elim presentation y<z))
        (Less-elim presentation x<y))

------------------------------------------------------------------------
-- Well-foundedness

Less-acc :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
    {point : Presented.CountableOrdinal𝒫.X presentation}
  → Accessibility.Acc (Presented.CountableOrdinal𝒫._<_ presentation) point
  → CubicalAcc.Acc
      (Less presentation)
      (Quotient.[ point ])
Less-acc presentation (Accessibility.acc smaller) =
  CubicalAcc.acc
    (Quotient.elimProp
      (λ quotient-point →
        HLevels.isPropΠ λ _ →
          CubicalAcc.isPropAcc quotient-point)
      (λ predecessor predecessor<point →
        Truncation.rec
          (CubicalAcc.isPropAcc (Quotient.[ predecessor ]))
          (λ strict-predecessor →
            Less-acc presentation
              (smaller predecessor strict-predecessor))
          (Less-elim presentation
            predecessor<point)))

Less-wf :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
  → CubicalAcc.WellFounded (Less presentation)
Less-wf presentation =
  Quotient.elimProp
    CubicalAcc.isPropAcc
    (λ point →
      Less-acc presentation
        (Presented.CountableOrdinal𝒫.<-wf presentation point))

------------------------------------------------------------------------
-- Extensionality

private
  representatives-extensional :
      (presentation : Presented.CountableOrdinal𝒫 ℓ)
      (x y : Presented.CountableOrdinal𝒫.X presentation)
    → ((z : Class presentation) →
        CubicalSigma._×_
          (Less presentation z (Quotient.[ x ])
            → Less presentation z (Quotient.[ y ]))
          (Less presentation z (Quotient.[ y ])
            → Less presentation z (Quotient.[ x ])))
    → Quotient.[ x ] Cubical.≡ Quotient.[ y ]
  representatives-extensional presentation x y lower-cones
      with Presented.CountableOrdinal𝒫.compare presentation x y
  ... | inj₁ x<y =
    ⊥-elim
      (Truncation.rec
        ordinary-empty-is-prop
        (Presented.Presentation.<-irrefl presentation x)
        (Less-elim presentation
          (Cubical.snd (lower-cones (Quotient.[ x ]))
            (Less-intro presentation x<y))))
  ... | inj₂ (inj₁ x≈y) =
    Quotient.eq/
      {R = Presented.CountableOrdinal𝒫._≈_ presentation}
      x y x≈y
  ... | inj₂ (inj₂ y<x) =
    ⊥-elim
      (Truncation.rec
        ordinary-empty-is-prop
        (Presented.Presentation.<-irrefl presentation y)
        (Less-elim presentation
          (Cubical.fst (lower-cones (Quotient.[ y ]))
            (Less-intro presentation y<x))))

Less-extensional :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
  → Extensionality.isWeaklyExtensional
      (Less presentation)
Less-extensional presentation =
  Extensionality.≺×→≡→isWeaklyExtensional
    (Less presentation)
    (Class-isSet presentation)
    (Less-isProp presentation)
    (Quotient.elimProp2
      (λ x y → HLevels.isPropΠ λ _ →
        Class-isSet presentation x y)
      (representatives-extensional presentation))

------------------------------------------------------------------------
-- The order type

-- ord(P) as a Cubical well-ordered set: the order is proposition-valued,
-- transitive, well founded and extensional (by `≈↓→≈`).

orderType :
  Presented.CountableOrdinal𝒫 ℓ → Woset.Woset ℓ ℓ
orderType presentation =
  Cubical._,_
    (Class presentation)
    (Woset.wosetstr
      (Less presentation)
      (Woset.iswoset
        Quotient.squash/
        (Less-isProp presentation)
        (Less-wf presentation)
        (Less-extensional presentation)
        (Less-trans presentation)))

------------------------------------------------------------------------
-- Equivalent presentations have equal order types

equivalence-to :
    {left right : Presented.CountableOrdinal𝒫 ℓ}
  → left Presented.≃𝒫 right
  → Class left
  → Class right
equivalence-to equivalence =
  Quotient.rec
    Quotient.squash/
    (λ point →
      Quotient.[ Presented.to equivalence point ])
    (λ x y x≈y →
      Quotient.eq/ _ _
        (Presented.to-≈
          equivalence x≈y))

equivalence-from :
    {left right : Presented.CountableOrdinal𝒫 ℓ}
  → left Presented.≃𝒫 right
  → Class right
  → Class left
equivalence-from equivalence =
  Quotient.rec
    Quotient.squash/
    (λ point →
      Quotient.[ Presented.from equivalence point ])
    (λ x y x≈y →
      Quotient.eq/ _ _
        (Presented.from-≈
          equivalence x≈y))

equivalence-to-from :
    {left right : Presented.CountableOrdinal𝒫 ℓ}
    (equivalence : left Presented.≃𝒫 right)
    (point : Class right)
  → equivalence-to equivalence
      (equivalence-from equivalence point)
      Cubical.≡ point
equivalence-to-from equivalence =
  Quotient.elimProp
    (λ _ → Quotient.squash/ _ _)
    (λ point →
      Quotient.eq/ _ _
        (Presented.to-from-≈
          equivalence point))

equivalence-from-to :
    {left right : Presented.CountableOrdinal𝒫 ℓ}
    (equivalence : left Presented.≃𝒫 right)
    (point : Class left)
  → equivalence-from equivalence
      (equivalence-to equivalence point)
      Cubical.≡ point
equivalence-from-to equivalence =
  Quotient.elimProp
    (λ _ → Quotient.squash/ _ _)
    (λ point →
      Quotient.eq/ _ _
        (Presented.from-to-≈
          equivalence point))

Class-equivalence :
    {left right : Presented.CountableOrdinal𝒫 ℓ}
  → left Presented.≃𝒫 right
  → CubicalEquiv._≃_
      (Class left)
      (Class right)
Class-equivalence equivalence =
  CubicalIso.isoToEquiv
    (CubicalIso.iso
      (equivalence-to equivalence)
      (equivalence-from equivalence)
      (equivalence-to-from equivalence)
      (equivalence-from-to equivalence))

equivalence-to-Less :
    {left right : Presented.CountableOrdinal𝒫 ℓ}
    (equivalence : left Presented.≃𝒫 right)
    (x y : Class left)
  → Less left x y
  → Less right
      (equivalence-to equivalence x)
      (equivalence-to equivalence y)
equivalence-to-Less equivalence =
  Quotient.elimProp2
    (λ x y → HLevels.isPropΠ λ _ →
      Less-isProp _
        (equivalence-to equivalence x)
        (equivalence-to equivalence y))
    (λ x y strict →
      Truncation.rec
        (Less-isProp _ _ _)
        (λ strict-x<y →
          Less-intro _
            (Presented.to-<
              equivalence strict-x<y))
        (Less-elim _ strict))

equivalence-from-Less :
    {left right : Presented.CountableOrdinal𝒫 ℓ}
    (equivalence : left Presented.≃𝒫 right)
    (x y : Class right)
  → Less right x y
  → Less left
      (equivalence-from equivalence x)
      (equivalence-from equivalence y)
equivalence-from-Less equivalence =
  Quotient.elimProp2
    (λ x y → HLevels.isPropΠ λ _ →
      Less-isProp _
        (equivalence-from equivalence x)
        (equivalence-from equivalence y))
    (λ x y strict →
      Truncation.rec
        (Less-isProp _ _ _)
        (λ strict-x<y →
          Less-intro _
            (Presented.from-<
              equivalence strict-x<y))
        (Less-elim _ strict))

orderType-equivalence :
    {left right : Presented.CountableOrdinal𝒫 ℓ}
  → left Presented.≃𝒫 right
  → Woset.WosetEquiv
      (orderType left)
      (orderType right)
orderType-equivalence equivalence =
  Cubical._,_
    (Class-equivalence equivalence)
    (Woset.makeIsWosetEquiv
      (Class-equivalence equivalence)
      (equivalence-to-Less equivalence)
      (equivalence-from-Less equivalence))

-- P ≃𝒫 Q gives ord(P) = ord(Q).  The converse direction, from a path of
-- order types back to maps of presentations, is in Simulation.Converse.

orderType-path :
    {left right : Presented.CountableOrdinal𝒫 ℓ}
  → left Presented.≃𝒫 right
  → orderType left Cubical.≡ orderType right
orderType-path {left = left} {right = right}
    equivalence =
  CubicalEquiv.equivFun
    (Woset.WosetPath (orderType left) (orderType right))
    (orderType-equivalence equivalence)
