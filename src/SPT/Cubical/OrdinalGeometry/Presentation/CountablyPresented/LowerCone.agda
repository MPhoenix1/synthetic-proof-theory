{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

open import Agda.Primitive using (Level)
import SPT.Cubical.OrdinalGeometry.Presentation.CountablyPresented as 𝒫𝒢

module SPT.Cubical.OrdinalGeometry.Presentation.CountablyPresented.LowerCone
  {ℓ : Level} (𝒢 : 𝒫𝒢.Geometry ℓ) where

-- The strict lower cone Σ x. x < b of a point b of a countably presented
-- geometry, as a presentation.  Equivalence and order are those of the
-- geometry on first components; the enumeration lists the successful
-- entries of the geometry's enumeration below b, and comparison is the
-- geometry's comparison below b.

open import Data.Maybe using (Maybe; just)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; subst; cong; sym)

open import SPT.Cubical.Core.WellFounded.Pullback using (pullback-wf)
import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
import SPT.Cubical.OrdinalGeometry.Presentation.Enumeration as Enumeration

private
  module Geometry = 𝒫𝒢.Geometry 𝒢
  module Occurrences = Enumeration.Occurrence
  module Entries = Enumeration.Entry

T : Geometry.X → Set ℓ
T b =
  Σ Geometry.X λ x → Geometry._<_ x b

infix 4 _≈_ _≺_

_≈_ :
    ∀ {b}
  → T b → T b → Set ℓ
_≈_ {b} x y =
  Geometry._≈_ (proj₁ x) (proj₁ y)

_≺_ :
    ∀ {b}
  → T b → T b → Set ℓ
_≺_ {b} x y =
  Geometry._<_ (proj₁ x) (proj₁ y)

Sequence : Geometry.X → ℕ → Maybe Geometry.X
Sequence = Geometry.enum↓

Occurrence : Geometry.X → Set ℓ
Occurrence b = Occurrences.T (Sequence b)

fromOccurrence :
    (b : Geometry.X)
  → Occurrence b
  → T b
fromOccurrence b occurrence =
  Occurrences.value occurrence
  , Geometry.enum↓-sound
      b
      (proj₁ occurrence)
      (Occurrences.value occurrence)
      (Occurrences.selects occurrence)

enum :
    (b : Geometry.X)
  → ℕ → Maybe (T b)
enum b n =
  Maybe.map
    (fromOccurrence b)
    (Occurrences.enum (Sequence b) n)

covers :
    (b : Geometry.X)
    (x : T b)
  → Σ ℕ λ n →
      Σ (T b) λ r →
        (enum b n ≡ just r)
        × r ≈ x
covers b (x , x<b) with Geometry.enum↓-covers b x x<b
... | n , r , selected , r≈x =
  proj₁ listed
  , fromOccurrence b occurrence
  , cong (Maybe.map (fromOccurrence b)) (proj₂ listed)
  , subst
      (λ y → Geometry._≈_ y x)
      (sym (Entries.value-fromSelection selected))
      r≈x
  where
    occurrence : Occurrence b
    occurrence = n , Entries.fromSelection selected

    listed :
      Σ ℕ λ m → Occurrences.enum (Sequence b) m ≡ just occurrence
    listed = Occurrences.covers (Sequence b) occurrence

-- The lower cone of b as a presentation.  It is constructed for every
-- point b; it does not make independently given points comparable.

𝒫 :
    Geometry.X
  → Presented.CountableOrdinal𝒫 ℓ
𝒫 b = record
  { X = T b
  ; _≈_ = _≈_
  ; _<_ = _≺_
  ; ≈-refl = λ x → Geometry.≈-refl (proj₁ x)
  ; ≈-sym = Geometry.≈-sym
  ; ≈-trans = Geometry.≈-trans
  ; <-trans = Geometry.<-trans
  ; <-respˡ-≈ = Geometry.<-respˡ-≈
  ; <-respʳ-≈ = Geometry.<-respʳ-≈
  ; <-wf = pullback-wf Geometry.<-wf
  ; compare =
      λ x y →
        Geometry.compare↓ b
          (proj₁ x) (proj₁ y)
          (proj₂ x) (proj₂ y)
  ; enum = enum b
  ; covers = covers b
  }
