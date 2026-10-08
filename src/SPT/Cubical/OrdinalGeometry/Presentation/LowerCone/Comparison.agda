{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Presentation.LowerCone.Comparison where

-- The two lower cones of a point b of a presentation P are equivalent
-- presentations:
--
--   Lower.cone P b ≃𝒫 Predecessors.𝒫 (from𝒫 P) b.
--
-- The points of the first are the occurrences of the enumeration filtered
-- below b; the points of the second are the predecessors Σ y. y < b.  An
-- occurrence goes to its value with the proof that it lies below b, which
-- is how the second cone enumerates its points; a predecessor goes to an
-- occurrence whose value is equivalent to it.

open import Agda.Primitive using (Level)
open import Data.Product using (_,_; proj₁; proj₂)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
open import SPT.Cubical.OrdinalGeometry.Presentation.CountablyPresented
  using (from𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.CountablyPresented.LowerCone
  as Predecessors
import SPT.Cubical.OrdinalGeometry.Presentation.LowerCone as Lower

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- The two maps

-- An occurrence goes to its value, with the proof that it lies below b.

to : (P : 𝒫 ℓ) (b : 𝒫.X P)
  → Lower.Carrier P b → Predecessors.T (from𝒫 P) b
to P b = Predecessors.fromOccurrence (from𝒫 P) b

-- A predecessor goes to an occurrence with an equivalent value.

from : (P : 𝒫 ℓ) (b : 𝒫.X P)
  → Predecessors.T (from𝒫 P) b → Lower.Carrier P b
from P b (x , x<b) = proj₁ (Lower.represent P b x x<b)

from-value : (P : 𝒫 ℓ) (b : 𝒫.X P) (z : Predecessors.T (from𝒫 P) b)
  → 𝒫._≈_ P (Lower.value P b (from P b z)) (proj₁ z)
from-value P b (x , x<b) = proj₂ (Lower.represent P b x x<b)

------------------------------------------------------------------------
-- The equivalence

equivalence : (P : 𝒫 ℓ) (b : 𝒫.X P)
  → Lower.cone P b Presented.≃𝒫 Predecessors.𝒫 (from𝒫 P) b
equivalence P b = record
  { to = to P b
  ; from = from P b
  ; to-≈ = λ x≈y → x≈y
  ; from-≈ = λ {z} {w} z≈w →
      𝒫.≈-trans P (from-value P b z)
        (𝒫.≈-trans P z≈w (𝒫.≈-sym P (from-value P b w)))
  ; to-< = λ x<y → x<y
  ; from-< = λ {z} {w} z<w →
      𝒫.<-respʳ-≈ P (𝒫.≈-sym P (from-value P b w))
        (𝒫.<-respˡ-≈ P (𝒫.≈-sym P (from-value P b z)) z<w)
  ; from-to-≈ = λ u → from-value P b (to P b u)
  ; to-from-≈ = from-value P b
  }
