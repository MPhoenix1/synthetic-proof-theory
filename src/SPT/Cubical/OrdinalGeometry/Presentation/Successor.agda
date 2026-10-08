{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Presentation.Successor where

-- The successor P + 1 of a presentation: P with one new point, the
-- ceiling, above all of it.

open import Agda.Primitive using (Level)
open import Data.Maybe using (Maybe; just)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented

private
  variable
    ℓ : Level

constant :
    Presented.CountableOrdinal𝒫 ℓ
  → ℕ → Presented.CountableOrdinal𝒫 ℓ
constant presentation index = presentation

-- The carrier of P + 1 is |P| + {ceiling}; the old points keep their
-- relations and lie below the ceiling.  It is the successor block of
-- `Presented.Diagonal` at a constant family.

Carrier :
  Presented.CountableOrdinal𝒫 ℓ → Set ℓ
Carrier presentation =
  Presented.Diagonal.Successor.Entry (constant presentation) zero

Equivalent :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
  → Carrier presentation
  → Carrier presentation
  → Set ℓ
Equivalent presentation =
  Presented.Diagonal.Successor._≈_
    (constant presentation) zero

Strict :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
  → Carrier presentation
  → Carrier presentation
  → Set ℓ
Strict presentation =
  Presented.Diagonal.Successor._<_
    (constant presentation) zero

embed :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
  → Presented.CountableOrdinal𝒫.X presentation
  → Carrier presentation
embed presentation = Presented.Diagonal.Successor.point

ceiling :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
  → Carrier presentation
ceiling presentation = Presented.Diagonal.Successor.top

below-ceiling :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
    (point : Presented.CountableOrdinal𝒫.X presentation)
  → Strict presentation
      (embed presentation point)
      (ceiling presentation)
below-ceiling presentation point =
  Presented.Diagonal.Successor.point<top

enumeration :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
  → ℕ → Maybe (Carrier presentation)
enumeration presentation zero =
  just (ceiling presentation)
enumeration presentation (suc index) =
  Maybe.map
    (embed presentation)
    (Presented.CountableOrdinal𝒫.enum presentation index)

enumeration-covers :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
    (entry : Carrier presentation)
  → Σ ℕ (λ index →
      Σ (Carrier presentation) (λ representative →
        (enumeration presentation index
          ≡ just representative)
        × Equivalent
            presentation representative entry))
enumeration-covers presentation
    (Presented.Diagonal.Successor.point point)
    with Presented.CountableOrdinal𝒫.covers presentation point
... | index , representative , selected , representative≈point =
  suc index
  , embed presentation representative
  , cong
      (Maybe.map (embed presentation))
      selected
  , Presented.Diagonal.Successor.point≈ representative≈point
enumeration-covers presentation Presented.Diagonal.Successor.top =
  zero
  , ceiling presentation
  , refl
  , Presented.Diagonal.Successor.top≈

-- The presentation P + 1.

successor :
  Presented.CountableOrdinal𝒫 ℓ
  → Presented.CountableOrdinal𝒫 ℓ
successor presentation = record
  { X = Carrier presentation
  ; _≈_ = Equivalent presentation
  ; _<_ = Strict presentation
  ; ≈-refl =
      Presented.Diagonal.Successor.≈-refl
        (constant presentation) zero
  ; ≈-sym =
      Presented.Diagonal.Successor.≈-sym
        (constant presentation) zero
  ; ≈-trans =
      Presented.Diagonal.Successor.≈-trans
        (constant presentation) zero
  ; <-trans =
      Presented.Diagonal.Successor.<-trans
        (constant presentation) zero
  ; <-respˡ-≈ =
      Presented.Diagonal.Successor.<-respˡ-≈
        (constant presentation) zero
  ; <-respʳ-≈ =
      Presented.Diagonal.Successor.<-respʳ-≈
        (constant presentation) zero
  ; <-wf =
      Presented.Diagonal.Successor.<-wf
        (constant presentation) zero
  ; compare =
      Presented.Diagonal.Successor.compare
        (constant presentation) zero
  ; enum = enumeration presentation
  ; covers = enumeration-covers presentation
  }

