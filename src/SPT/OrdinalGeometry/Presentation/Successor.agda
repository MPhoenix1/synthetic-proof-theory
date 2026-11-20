{-# OPTIONS --safe --without-K #-}

module SPT.OrdinalGeometry.Presentation.Successor where

-- The successor P + 1 of a countable ordinal presentation
-- (`presentation-successor`): the points of P with one new top above them
-- all, with the order of P and its enumeration shifted by one. It is the
-- diagonal successor block of CountableOrdinal at the constant family of P
-- (`constant-presentation-family`):
--
--   Presentation-Successor-Carrier P = Carrier P + {top},
--
-- with P's equivalence and order on embedded points and every embedded
-- point strictly below the new top. No quotient or choice is used.

open import SPT.Base
open import SPT.OrdinalGeometry.Presentation.CountableOrdinal using
  (Countable-Ordinal𝒫; module Diagonal)

module _ {ℓ : Level} where

  constant-presentation-family :
    Countable-Ordinal𝒫 ℓ → ℕ → Countable-Ordinal𝒫 ℓ
  constant-presentation-family presentation index = presentation

  Presentation-Successor-Carrier : Countable-Ordinal𝒫 ℓ → Set ℓ
  Presentation-Successor-Carrier presentation =
    Diagonal.Successor.Entry (constant-presentation-family presentation) zero

  embed-presentation-successor : (presentation : Countable-Ordinal𝒫 ℓ) →
    Countable-Ordinal𝒫.X presentation →
    Presentation-Successor-Carrier presentation
  embed-presentation-successor presentation = Diagonal.Successor.point

  presentation-successor-ceiling : (presentation : Countable-Ordinal𝒫 ℓ) →
    Presentation-Successor-Carrier presentation
  presentation-successor-ceiling presentation = Diagonal.Successor.top

  presentation-successor-sequence : (presentation : Countable-Ordinal𝒫 ℓ) →
    ℕ → Maybe (Presentation-Successor-Carrier presentation)
  presentation-successor-sequence presentation zero =
    just (presentation-successor-ceiling presentation)
  presentation-successor-sequence presentation (suc index) =
    maybe-map (embed-presentation-successor presentation)
      (Countable-Ordinal𝒫.enum presentation index)

  presentation-successor-sequence-covers :
    (presentation : Countable-Ordinal𝒫 ℓ)
    (entry : Presentation-Successor-Carrier presentation) →
    Σ ℕ (λ index →
      Σ (Presentation-Successor-Carrier presentation) (λ representative →
        (presentation-successor-sequence presentation index ＝
          just representative) ×
        Diagonal.Successor._≈_ (constant-presentation-family presentation)
          zero representative entry))
  presentation-successor-sequence-covers presentation
    (Diagonal.Successor.point point)
    with Countable-Ordinal𝒫.covers presentation point
  ... | index , representative , selected , representative≈point =
    suc index ,
    embed-presentation-successor presentation representative ,
    ap (maybe-map (embed-presentation-successor presentation)) selected ,
    Diagonal.Successor.point≈ representative≈point
  presentation-successor-sequence-covers presentation
    Diagonal.Successor.top =
    zero , presentation-successor-ceiling presentation , refl ,
    Diagonal.Successor.top≈

  -- P + 1. The top and the embedded points determine every law and the
  -- exact partial enumeration.

  presentation-successor : Countable-Ordinal𝒫 ℓ → Countable-Ordinal𝒫 ℓ
  presentation-successor presentation = record
    { X = Presentation-Successor-Carrier presentation
    ; _≈_ = λ x y →
        Diagonal.Successor._≈_ (constant-presentation-family presentation)
          zero x y
    ; _<_ = λ x y →
        Diagonal.Successor._<_ (constant-presentation-family presentation)
          zero x y
    ; ≈-refl =
        Diagonal.Successor.≈-refl
          (constant-presentation-family presentation) zero
    ; ≈-sym =
        Diagonal.Successor.≈-sym
          (constant-presentation-family presentation) zero
    ; ≈-trans =
        Diagonal.Successor.≈-trans
          (constant-presentation-family presentation) zero
    ; <-trans =
        Diagonal.Successor.<-trans
          (constant-presentation-family presentation) zero
    ; <-respˡ-≈ =
        Diagonal.Successor.<-respˡ-≈
          (constant-presentation-family presentation) zero
    ; <-respʳ-≈ =
        Diagonal.Successor.<-respʳ-≈
          (constant-presentation-family presentation) zero
    ; <-wf =
        Diagonal.Successor.<-wf
          (constant-presentation-family presentation) zero
    ; compare =
        Diagonal.Successor.compare
          (constant-presentation-family presentation) zero
    ; enum = presentation-successor-sequence presentation
    ; covers = presentation-successor-sequence-covers presentation
    }
