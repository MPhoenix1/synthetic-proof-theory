{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Successor where

-- Successors commute with reflection: P is equivalent to the lower cone of
-- the new top of P + 1, so ord(P) is the principal segment of ord(P + 1)
-- below the top, and ord(P) ≺ ord(P + 1).

open import Agda.Primitive using (Level)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
import SPT.Cubical.OrdinalGeometry.Presentation.LowerCone as Lower
import SPT.Cubical.OrdinalGeometry.Presentation.Successor as Successor
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.LowerCone
  as LowerCubical
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType as Reflection

import Cubical.Foundations.Prelude as Cubical
import Cubical.HITs.SetQuotients as Quotient
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- The lower cone at the top of P + 1 is P

private
  Next :
      Presented.CountableOrdinal𝒫 ℓ
    → Presented.CountableOrdinal𝒫 ℓ
  Next = Successor.successor

  LowerNext :
      (presentation : Presented.CountableOrdinal𝒫 ℓ)
    → Presented.CountableOrdinal𝒫 ℓ
  LowerNext presentation =
    Lower.cone
      (Next presentation)
      (Successor.ceiling presentation)

  predecessor :
      (presentation : Presented.CountableOrdinal𝒫 ℓ)
      (entry : Successor.Carrier presentation)
    → Successor.Strict presentation entry
        (Successor.ceiling presentation)
    → Presented.CountableOrdinal𝒫.X presentation
  predecessor presentation
      (Presented.Diagonal.Successor.point point)
      Presented.Diagonal.Successor.point<top = point

  predecessor-agrees :
      (presentation : Presented.CountableOrdinal𝒫 ℓ)
      (entry : Successor.Carrier presentation)
      (entry<ceiling :
        Successor.Strict presentation entry
          (Successor.ceiling presentation))
    → Successor.Equivalent presentation entry
        (Successor.embed presentation
          (predecessor presentation entry entry<ceiling))
  predecessor-agrees presentation
      (Presented.Diagonal.Successor.point point)
      Presented.Diagonal.Successor.point<top =
    Presented.Diagonal.Successor.point≈
      (Presented.CountableOrdinal𝒫.≈-refl presentation point)

  ≈-reflects :
      (presentation : Presented.CountableOrdinal𝒫 ℓ)
      {left right : Presented.CountableOrdinal𝒫.X presentation}
    → Successor.Equivalent presentation
        (Successor.embed presentation left)
        (Successor.embed presentation right)
    → Presented.CountableOrdinal𝒫._≈_ presentation left right
  ≈-reflects presentation
      (Presented.Diagonal.Successor.point≈ left≈right) = left≈right

  <-reflects :
      (presentation : Presented.CountableOrdinal𝒫 ℓ)
      {left right : Presented.CountableOrdinal𝒫.X presentation}
    → Successor.Strict presentation
        (Successor.embed presentation left)
        (Successor.embed presentation right)
    → Presented.CountableOrdinal𝒫._<_ presentation left right
  <-reflects presentation
      (Presented.Diagonal.Successor.point< left<right) = left<right

  occurrence :
      (presentation : Presented.CountableOrdinal𝒫 ℓ)
    → Presented.CountableOrdinal𝒫.X presentation
    → Presented.CountableOrdinal𝒫.X (LowerNext presentation)
  occurrence presentation point =
    Cubical.fst
      (Lower.represent
        (Next presentation)
        (Successor.ceiling presentation)
        (Successor.embed presentation point)
        (Successor.below-ceiling presentation point))

  occurrence-agrees :
      (presentation : Presented.CountableOrdinal𝒫 ℓ)
      (point : Presented.CountableOrdinal𝒫.X presentation)
    → Presented.CountableOrdinal𝒫._≈_ (Next presentation)
        (Lower.value
          (Next presentation)
          (Successor.ceiling presentation)
          (occurrence presentation point))
        (Successor.embed presentation point)
  occurrence-agrees presentation point =
    Cubical.snd
      (Lower.represent
        (Next presentation)
        (Successor.ceiling presentation)
        (Successor.embed presentation point)
        (Successor.below-ceiling presentation point))

  value :
      (presentation : Presented.CountableOrdinal𝒫 ℓ)
    → Presented.CountableOrdinal𝒫.X (LowerNext presentation)
    → Successor.Carrier presentation
  value presentation =
    Lower.value
      (Next presentation)
      (Successor.ceiling presentation)

  value-strict :
      (presentation : Presented.CountableOrdinal𝒫 ℓ)
      (occurrence : Presented.CountableOrdinal𝒫.X
        (LowerNext presentation))
    → Successor.Strict presentation
        (value presentation occurrence)
        (Successor.ceiling presentation)
  value-strict presentation =
    Lower.value-strict
      (Next presentation)
      (Successor.ceiling presentation)

  backward :
      (presentation : Presented.CountableOrdinal𝒫 ℓ)
    → Presented.CountableOrdinal𝒫.X (LowerNext presentation)
    → Presented.CountableOrdinal𝒫.X presentation
  backward presentation occurrence =
    predecessor presentation
      (value presentation occurrence)
      (value-strict presentation occurrence)

  value-agrees :
      (presentation : Presented.CountableOrdinal𝒫 ℓ)
      (occurrence : Presented.CountableOrdinal𝒫.X
        (LowerNext presentation))
    → Presented.CountableOrdinal𝒫._≈_ (Next presentation)
        (value presentation occurrence)
        (Successor.embed presentation
          (backward presentation occurrence))
  value-agrees presentation occurrence =
    predecessor-agrees presentation
      (value presentation occurrence)
      (value-strict presentation occurrence)

-- P ≃𝒫 Lower(P + 1, top).  The forward map finds each point of P in the
-- enumeration of the cone; the backward map reads it off an entry, which
-- lies below the top.

lowerCone-top :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
  → presentation
      Presented.≃𝒫 LowerNext presentation
lowerCone-top presentation = record
  { to = occurrence presentation
  ; from = backward presentation
  ; to-≈ =
      λ {left} {right} left≈right →
        Presented.CountableOrdinal𝒫.≈-trans
          (Next presentation)
          (occurrence-agrees presentation left)
          (Presented.CountableOrdinal𝒫.≈-trans
            (Next presentation)
            (Presented.Diagonal.Successor.point≈ left≈right)
            (Presented.CountableOrdinal𝒫.≈-sym
              (Next presentation)
              (occurrence-agrees presentation right)))
  ; from-≈ =
      λ {left} {right} left≈right →
        ≈-reflects presentation
          (Presented.CountableOrdinal𝒫.≈-trans
            (Next presentation)
            (Presented.CountableOrdinal𝒫.≈-sym
              (Next presentation)
              (value-agrees presentation left))
            (Presented.CountableOrdinal𝒫.≈-trans
              (Next presentation)
              left≈right
              (value-agrees presentation right)))
  ; to-< =
      λ {left} {right} left<right →
        Presented.CountableOrdinal𝒫.<-respʳ-≈
          (Next presentation)
          (Presented.CountableOrdinal𝒫.≈-sym
            (Next presentation)
            (occurrence-agrees presentation right))
          (Presented.CountableOrdinal𝒫.<-respˡ-≈
            (Next presentation)
            (Presented.CountableOrdinal𝒫.≈-sym
              (Next presentation)
              (occurrence-agrees presentation left))
            (Presented.Diagonal.Successor.point< left<right))
  ; from-< =
      λ {left} {right} left<right →
        <-reflects presentation
          (Presented.CountableOrdinal𝒫.<-respʳ-≈
            (Next presentation)
            (value-agrees presentation right)
            (Presented.CountableOrdinal𝒫.<-respˡ-≈
              (Next presentation)
              (value-agrees presentation left)
              left<right))
  ; from-to-≈ =
      λ point →
        ≈-reflects presentation
          (Presented.CountableOrdinal𝒫.≈-trans
            (Next presentation)
            (Presented.CountableOrdinal𝒫.≈-sym
              (Next presentation)
              (value-agrees presentation
                (occurrence presentation point)))
            (occurrence-agrees presentation point))
  ; to-from-≈ =
      λ occurrence →
        Presented.CountableOrdinal𝒫.≈-trans
          (Next presentation)
          (occurrence-agrees presentation
            (backward presentation occurrence))
          (Presented.CountableOrdinal𝒫.≈-sym
            (Next presentation)
            (value-agrees presentation occurrence))
  }

------------------------------------------------------------------------
-- ord(P) ≺ ord(P + 1)

private
  TopSegment :
      (presentation : Presented.CountableOrdinal𝒫 ℓ)
    → Woset.Woset ℓ ℓ
  TopSegment presentation =
    Simulation._↓_
      (Reflection.orderType (Next presentation))
      (Quotient.[ Successor.ceiling presentation ])

segment-top :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
  → Woset.WosetEquiv
      (Reflection.orderType presentation)
      (TopSegment presentation)
segment-top presentation =
  Woset.compWosetEquiv
    (Reflection.orderType-equivalence
      (lowerCone-top presentation))
    (LowerCubical.equivalence
      (Next presentation)
      (Successor.ceiling presentation))

-- ord(P) ≺ ord(P + 1): the bounding point is the class of the top, and
-- ord(P) is equivalent to the whole principal segment below it.

successor-strict :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
  → Simulation._≺_
      (Reflection.orderType presentation)
      (Reflection.orderType (Next presentation))
successor-strict presentation =
  Cubical._,_
    (Quotient.[ Successor.ceiling presentation ])
    (Woset.invWosetEquiv
      (segment-top presentation))
