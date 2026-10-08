{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Reflection.LowerCone where

-- Lower cones commute with reflection: the order type of the lower cone of
-- b in P is the principal segment of ord(P) below [b].  Hence every
-- principal segment of ord(P) is merely presented (`segment-presented`).

open import Agda.Primitive using (Level)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
import SPT.Cubical.OrdinalGeometry.Presentation.LowerCone as Lower
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType as Reflection

import Cubical.Data.Sigma.Properties as SigmaProperties
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Isomorphism as Isomorphism
import Cubical.Foundations.Prelude as Cubical
import Cubical.Functions.Embedding as Embedding
import Cubical.Functions.Surjection as Surjection
import Cubical.HITs.PropositionalTruncation as Truncation
import Cubical.HITs.SetQuotients as Quotient
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- The lower cone and the principal segment

LowerPresentation :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
  → Presented.CountableOrdinal𝒫.X presentation
  → Presented.CountableOrdinal𝒫 ℓ
LowerPresentation = Lower.cone

LowerOrderType :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
  → Presented.CountableOrdinal𝒫.X presentation
  → Woset.Woset ℓ ℓ
LowerOrderType presentation bound =
  Reflection.orderType (LowerPresentation presentation bound)

PrincipalSegment :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
  → Presented.CountableOrdinal𝒫.X presentation
  → Woset.Woset ℓ ℓ
PrincipalSegment presentation bound =
  Simulation._↓_
    (Reflection.orderType presentation)
    (Quotient.[ bound ])

------------------------------------------------------------------------
-- The map from the lower cone to the segment

private
  segment-isSet :
      (presentation : Presented.CountableOrdinal𝒫 ℓ)
      (bound : Presented.CountableOrdinal𝒫.X presentation)
    → Cubical.isSet (Cubical.fst (PrincipalSegment presentation bound))
  segment-isSet presentation bound =
    HLevels.isSetΣ
      (Reflection.Class-isSet presentation)
      (λ point →
        Cubical.isProp→isSet
          (Reflection.Less-isProp presentation
            point (Quotient.[ bound ])))

  toSegment₀ :
      (presentation : Presented.CountableOrdinal𝒫 ℓ)
      (bound : Presented.CountableOrdinal𝒫.X presentation)
    → Presented.CountableOrdinal𝒫.X (LowerPresentation presentation bound)
    → Cubical.fst (PrincipalSegment presentation bound)
  toSegment₀ presentation bound occurrence =
    Cubical._,_
      (Quotient.[ Lower.value
        presentation bound occurrence ])
      (Reflection.Less-intro presentation
        (Lower.value-strict
          presentation bound occurrence))

toSegment :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
    (bound : Presented.CountableOrdinal𝒫.X presentation)
  → Reflection.Class (LowerPresentation presentation bound)
  → Cubical.fst (PrincipalSegment presentation bound)
toSegment presentation bound =
  Quotient.rec
    (segment-isSet presentation bound)
    (toSegment₀ presentation bound)
    (λ left right left≈right →
      SigmaProperties.Σ≡Prop
        (λ point →
          Reflection.Less-isProp
            presentation point (Quotient.[ bound ]))
        (Quotient.eq/
          {R = Presented.CountableOrdinal𝒫._≈_ presentation}
          (Lower.value presentation bound left)
          (Lower.value presentation bound right)
          left≈right))

------------------------------------------------------------------------
-- Injectivity and surjectivity

private
  toSegment-injective :
      (presentation : Presented.CountableOrdinal𝒫 ℓ)
      (bound : Presented.CountableOrdinal𝒫.X presentation)
      {left right :
        Reflection.Class (LowerPresentation presentation bound)}
    → toSegment presentation bound left
        Cubical.≡ toSegment presentation bound right
    → left Cubical.≡ right
  toSegment-injective presentation bound {left} {right}
      forward-equality =
    Quotient.elimProp2
      {P = λ quotient-left quotient-right →
        toSegment presentation bound quotient-left Cubical.≡
          toSegment presentation bound quotient-right
        → quotient-left Cubical.≡ quotient-right}
      (λ quotient-left quotient-right → HLevels.isPropΠ λ _ →
        Reflection.Class-isSet
          (LowerPresentation presentation bound)
          quotient-left quotient-right)
      (λ representative-left representative-right equality →
        Truncation.rec
          (Reflection.Class-isSet
            (LowerPresentation presentation bound)
            (Quotient.[ representative-left ])
            (Quotient.[ representative-right ]))
          (λ left≈right →
            Quotient.eq/
              {R = Lower.Equivalent presentation bound}
              representative-left representative-right left≈right)
          (Isomorphism.Iso.fun
            (Quotient.isEquivRel→TruncIso
              (Reflection.≈-isEquivRel
                presentation)
              (Lower.value
                presentation bound representative-left)
              (Lower.value
                presentation bound representative-right))
            (Cubical.cong Cubical.fst equality)))
      left right forward-equality

  toSegment-isEmbedding :
      (presentation : Presented.CountableOrdinal𝒫 ℓ)
      (bound : Presented.CountableOrdinal𝒫.X presentation)
    → Embedding.isEmbedding (toSegment presentation bound)
  toSegment-isEmbedding presentation bound =
    Embedding.injEmbedding
      (segment-isSet presentation bound)
      (toSegment-injective presentation bound)

  toSegment-surjective₀ :
      (presentation : Presented.CountableOrdinal𝒫 ℓ)
      (bound point : Presented.CountableOrdinal𝒫.X presentation)
      (point<bound :
        Reflection.Less presentation
          (Quotient.[ point ]) (Quotient.[ bound ]))
    → Truncation.∥
        Equiv.fiber
          (toSegment presentation bound)
          (Cubical._,_ (Quotient.[ point ]) point<bound)
      ∥₁
  toSegment-surjective₀
      presentation bound point point<bound =
    Truncation.∣
      Cubical._,_
        (Quotient.[ occurrence ])
        (SigmaProperties.Σ≡Prop
          (λ quotient-point →
            Reflection.Less-isProp
              presentation quotient-point (Quotient.[ bound ]))
          (Quotient.eq/
            {R = Presented.CountableOrdinal𝒫._≈_ presentation}
            (Lower.value presentation bound occurrence)
            point occurrence≈point))
    ∣₁
    where
      strict-point<bound :
        Presented.CountableOrdinal𝒫._<_ presentation point bound
      strict-point<bound =
        Reflection.Less-witness
          presentation point<bound

      occurrence-with-cell :
        Cubical.Σ
          (Lower.Carrier presentation bound)
          (λ selected-occurrence →
            Presented.CountableOrdinal𝒫._≈_ presentation
              (Lower.value
                presentation bound selected-occurrence)
              point)
      occurrence-with-cell =
        Lower.represent
          presentation bound point strict-point<bound

      occurrence : Lower.Carrier presentation bound
      occurrence = Cubical.fst occurrence-with-cell

      occurrence≈point :
        Presented.CountableOrdinal𝒫._≈_ presentation
          (Lower.value presentation bound occurrence)
          point
      occurrence≈point = Cubical.snd occurrence-with-cell

  toSegment-isSurjective :
      (presentation : Presented.CountableOrdinal𝒫 ℓ)
      (bound : Presented.CountableOrdinal𝒫.X presentation)
    → Surjection.isSurjection (toSegment presentation bound)
  toSegment-isSurjective presentation bound
      (Cubical._,_ quotient-point point<bound) =
    Quotient.elimProp
      {P = λ point →
        (strict : Reflection.Less
          presentation point (Quotient.[ bound ])) →
        Truncation.∥
          Equiv.fiber
            (toSegment presentation bound)
            (Cubical._,_ point strict)
        ∥₁}
      (λ point → HLevels.isPropΠ λ _ →
        Truncation.isPropPropTrunc)
      (toSegment-surjective₀ presentation bound)
      quotient-point point<bound

carrier-equivalence :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
    (bound : Presented.CountableOrdinal𝒫.X presentation)
  → Equiv._≃_
      (Reflection.Class (LowerPresentation presentation bound))
      (Cubical.fst (PrincipalSegment presentation bound))
carrier-equivalence presentation bound =
  Cubical._,_
    (toSegment presentation bound)
    (Surjection.isEmbedding×isSurjection→isEquiv
      (Cubical._,_
        (toSegment-isEmbedding presentation bound)
        (toSegment-isSurjective presentation bound)))

------------------------------------------------------------------------
-- Preservation and reflection of the order

toSegment-preserves :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
    (bound : Presented.CountableOrdinal𝒫.X presentation)
    (left right :
      Reflection.Class (LowerPresentation presentation bound))
  → Reflection.Less
      (LowerPresentation presentation bound) left right
  → Woset.WosetStr._≺_
      (Cubical.snd (PrincipalSegment presentation bound))
      (toSegment presentation bound left)
      (toSegment presentation bound right)
toSegment-preserves presentation bound =
  Quotient.elimProp2
    (λ left right → HLevels.isPropΠ λ _ →
      Reflection.Less-isProp presentation
        (Cubical.fst (toSegment presentation bound left))
        (Cubical.fst (toSegment presentation bound right)))
    (λ left right strict →
      Reflection.Less-intro presentation
        (Reflection.Less-witness
          (LowerPresentation presentation bound) strict))

toSegment-reflects :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
    (bound : Presented.CountableOrdinal𝒫.X presentation)
    (left right :
      Reflection.Class (LowerPresentation presentation bound))
  → Woset.WosetStr._≺_
      (Cubical.snd (PrincipalSegment presentation bound))
      (toSegment presentation bound left)
      (toSegment presentation bound right)
  → Reflection.Less
      (LowerPresentation presentation bound) left right
toSegment-reflects presentation bound =
  Quotient.elimProp2
    (λ left right → HLevels.isPropΠ λ _ →
      Reflection.Less-isProp
        (LowerPresentation presentation bound) left right)
    (λ left right strict →
      Reflection.Less-intro
        (LowerPresentation presentation bound)
        (Reflection.Less-witness
          presentation strict))

private
  fromSegment-preserves :
      (presentation : Presented.CountableOrdinal𝒫 ℓ)
      (bound : Presented.CountableOrdinal𝒫.X presentation)
      (left right : Cubical.fst (PrincipalSegment presentation bound))
    → Woset.WosetStr._≺_
        (Cubical.snd (PrincipalSegment presentation bound))
        left right
    → Reflection.Less
        (LowerPresentation presentation bound)
        (Equiv.invEq (carrier-equivalence presentation bound) left)
        (Equiv.invEq (carrier-equivalence presentation bound) right)
  fromSegment-preserves presentation bound left right strict =
    toSegment-reflects presentation bound
      (Equiv.invEq (carrier-equivalence presentation bound) left)
      (Equiv.invEq (carrier-equivalence presentation bound) right)
      (Cubical.transport
        (λ interval →
          Woset.WosetStr._≺_
            (Cubical.snd (PrincipalSegment presentation bound))
            (Equiv.secEq
              (carrier-equivalence presentation bound) left
              (Cubical.~ interval))
            (Equiv.secEq
              (carrier-equivalence presentation bound) right
              (Cubical.~ interval)))
        strict)

-- ord(Lower(P,b)) ≃ ord(P) ↓ [b], as well-ordered sets, and the path.

equivalence :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
    (bound : Presented.CountableOrdinal𝒫.X presentation)
  → Woset.WosetEquiv
      (LowerOrderType presentation bound)
      (PrincipalSegment presentation bound)
equivalence presentation bound =
  Cubical._,_
    (carrier-equivalence presentation bound)
    (Woset.makeIsWosetEquiv
      (carrier-equivalence presentation bound)
      (toSegment-preserves presentation bound)
      (fromSegment-preserves presentation bound))

path :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
    (bound : Presented.CountableOrdinal𝒫.X presentation)
  → LowerOrderType presentation bound Cubical.≡
      PrincipalSegment presentation bound
path presentation bound =
  Equiv.equivFun
    (Woset.WosetPath
      (LowerOrderType presentation bound)
      (PrincipalSegment presentation bound))
    (equivalence presentation bound)

------------------------------------------------------------------------
-- Principal segments are presented

-- α ≺ ord(P) → ‖Σ Q. ord(Q) ≃ α‖.  The point bounding α is a class;
-- since the conclusion is a proposition, the quotient may be eliminated,
-- and at a representative b the lower cone of b presents α.

segment-presented :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
    (ordinal : Woset.Woset ℓ ℓ)
  → Simulation._≺_ ordinal (Reflection.orderType presentation)
  → Truncation.∥
      Cubical.Σ
        (Presented.CountableOrdinal𝒫 ℓ)
        (λ lower-presentation →
          Woset.WosetEquiv
            (Reflection.orderType lower-presentation)
            ordinal)
    ∥₁
segment-presented {ℓ} presentation ordinal strict =
  Quotient.elimProp
    {P = λ quotient-bound →
      Woset.WosetEquiv
        (Simulation._↓_
          (Reflection.orderType presentation)
          quotient-bound)
        ordinal
      → Truncation.∥
          Cubical.Σ
            (Presented.CountableOrdinal𝒫 ℓ)
            (λ lower-presentation →
              Woset.WosetEquiv
                (Reflection.orderType lower-presentation)
                ordinal)
        ∥₁}
    (λ quotient-bound → HLevels.isPropΠ λ _ →
      Truncation.isPropPropTrunc)
    (λ bound segment-equivalence →
      Truncation.∣
        Cubical._,_
          (LowerPresentation presentation bound)
          (Woset.compWosetEquiv
            (equivalence presentation bound)
            segment-equivalence)
      ∣₁)
    (Cubical.fst strict)
    (Cubical.snd strict)
