{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Presentation.LowerCone where

-- The strict lower cone of a point b of a presentation, as a presentation:
-- its points are the occurrences of the enumeration filtered below b
-- (entries and occurrences as in Presentation.Enumeration), ordered as in
-- the ambient presentation.  LowerCone.Comparison shows it equivalent to
-- the cone Σ y. y < b of CountablyPresented.LowerCone.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.WellFounded.Pullback using
  ( pullback-is-well-founded )

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
import SPT.Cubical.OrdinalGeometry.Presentation.CountablyPresented
  as CountablyPresented
import SPT.Cubical.OrdinalGeometry.Presentation.Enumeration as Enumeration

private
  variable
    ℓ : Level

  module Entries = Enumeration.Entry
  module Occurrences = Enumeration.Occurrence

------------------------------------------------------------------------
-- The lower cone

-- The carrier is the occurrences of the enumeration filtered below b,
-- compared through their values:
--
--   Carrier(P,b) = Σ(n : ℕ). Entry(enum↓(P,b,n)),
--   u ≈ v = value(u) ≈ₚ value(v),   u < v = value(u) <ₚ value(v).

Carrier :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
  → Presented.CountableOrdinal𝒫.X presentation
  → Set ℓ
Carrier presentation bound =
  Occurrences.T (CountablyPresented.From𝒫.enum↓ presentation bound)

value :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
    (bound : Presented.CountableOrdinal𝒫.X presentation)
  → Carrier presentation bound
  → Presented.CountableOrdinal𝒫.X presentation
value presentation bound occurrence =
  Occurrences.value occurrence

value-strict :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
    (bound : Presented.CountableOrdinal𝒫.X presentation)
    (occurrence : Carrier presentation bound)
  → Presented.CountableOrdinal𝒫._<_ presentation
      (value presentation bound occurrence)
      bound
value-strict presentation bound (index , selected) =
  CountablyPresented.From𝒫.enum↓-sound
    presentation bound index (Entries.value selected)
    (Entries.selects selected)

-- Every predecessor of b is equivalent to the value of some occurrence.

represent :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
    (bound predecessor : Presented.CountableOrdinal𝒫.X presentation)
  → Presented.CountableOrdinal𝒫._<_ presentation predecessor bound
  → Σ (Carrier presentation bound) (λ occurrence →
      Presented.CountableOrdinal𝒫._≈_ presentation
        (value presentation bound occurrence)
        predecessor)
represent
    presentation bound predecessor predecessor<bound
    with CountablyPresented.From𝒫.enum↓-covers
      presentation bound predecessor predecessor<bound
... | index , representative , selected , representative≈predecessor =
  (index , Entries.fromSelection selected)
  , transport
      (λ point →
        Presented.CountableOrdinal𝒫._≈_ presentation point predecessor)
      (Entries.value-fromSelection selected ⁻¹)
      representative≈predecessor

Equivalent :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
    (bound : Presented.CountableOrdinal𝒫.X presentation)
  → Carrier presentation bound
  → Carrier presentation bound
  → Set ℓ
Equivalent presentation bound left right =
  Presented.CountableOrdinal𝒫._≈_ presentation
    (value presentation bound left)
    (value presentation bound right)

Strict :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
    (bound : Presented.CountableOrdinal𝒫.X presentation)
  → Carrier presentation bound
  → Carrier presentation bound
  → Set ℓ
Strict presentation bound left right =
  Presented.CountableOrdinal𝒫._<_ presentation
    (value presentation bound left)
    (value presentation bound right)

enumeration :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
    (bound : Presented.CountableOrdinal𝒫.X presentation)
  → ℕ → Maybe (Carrier presentation bound)
enumeration presentation bound index =
  Occurrences.enum
    (CountablyPresented.From𝒫.enum↓ presentation bound)
    index

enumeration-covers :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
    (bound : Presented.CountableOrdinal𝒫.X presentation)
    (predecessor : Carrier presentation bound)
  → Σ ℕ (λ index →
      Σ (Carrier presentation bound)
        (λ representative →
          (enumeration presentation bound index
            ＝ just representative)
          × Equivalent
              presentation bound representative predecessor))
enumeration-covers
    presentation bound occurrence
    with Occurrences.covers
      (CountablyPresented.From𝒫.enum↓ presentation bound)
      occurrence
... | index , selected =
  index
  , occurrence
  , selected
  , Presented.CountableOrdinal𝒫.≈-refl presentation
      (value presentation bound occurrence)

-- The lower cone of b as a presentation; every law is inherited from P.

cone :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
  → Presented.CountableOrdinal𝒫.X presentation
  → Presented.CountableOrdinal𝒫 ℓ
cone presentation bound = record
  { X = Carrier presentation bound
  ; _≈_ = Equivalent presentation bound
  ; _<_ = Strict presentation bound
  ; ≈-refl =
      λ point →
        Presented.CountableOrdinal𝒫.≈-refl presentation
          (value presentation bound point)
  ; ≈-sym =
      Presented.CountableOrdinal𝒫.≈-sym presentation
  ; ≈-trans =
      Presented.CountableOrdinal𝒫.≈-trans presentation
  ; <-trans =
      Presented.CountableOrdinal𝒫.<-trans presentation
  ; <-respˡ-≈ =
      Presented.CountableOrdinal𝒫.<-respˡ-≈ presentation
  ; <-respʳ-≈ =
      Presented.CountableOrdinal𝒫.<-respʳ-≈ presentation
  ; <-wf =
      pullback-is-well-founded (value presentation bound)
        (Presented.CountableOrdinal𝒫._<_ presentation)
        (Presented.CountableOrdinal𝒫.<-wf presentation)
  ; compare =
      λ left right →
        Presented.CountableOrdinal𝒫.compare presentation
          (value presentation bound left)
          (value presentation bound right)
  ; enum =
      enumeration presentation bound
  ; covers =
      enumeration-covers presentation bound
  }
