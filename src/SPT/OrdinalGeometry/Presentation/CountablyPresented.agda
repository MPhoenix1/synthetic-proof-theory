{-# OPTIONS --safe --without-K #-}

module SPT.OrdinalGeometry.Presentation.CountablyPresented where

-- A notation-independent ordinal geometry whose points keep enough local
-- countable presentation data for exact predecessor recursion (`Geometry`):
-- the comparison and the order are global, but every bound exposes one
-- literal partial ℕ-enumeration of exactly its strict predecessor cone, and
-- trichotomy is asked only of pairs below one bound. Writing eₓ for
-- `enum↓ x`:
--
--   Geometry ℓ ≃ Σ X. Σ ≈ <. Equivalence ≈ × Transitive < × Respects < ≈ ×
--     WellFounded < × (Π x a b. a < x → b < x → Trichotomy ≈ < a b) ×
--     Π x. Σ eₓ : ℕ → Maybe X. Soundₓ eₓ × Coverₓ eₓ,
--   Soundₓ eₓ = Π n a. eₓ n ＝ just a → a < x,
--   Coverₓ eₓ = Π a < x. Σ n r. (eₓ n ＝ just r) × (r ≈ a).
--
-- A successful entry keeps only its exact representative; `enum↓-sound`
-- derives the strict comparison from the identification of the selected
-- entry. Every presentation gives a geometry at its level (`from𝒫`), by
-- filtering its enumeration below the bound (`From𝒫.filter`). The record
-- asks for no global trichotomy, antisymmetry, quotient, uniqueness of
-- indices or representatives, least upper bounds or notation.

open import SPT.Base
open import SPT.Foundation.Accessibility using (is-well-founded)
open import SPT.OrdinalGeometry.Presentation.CountableOrdinal using
  (Countable-Ordinal𝒫; module Presentation)

------------------------------------------------------------------------
-- Countably presented ordinal geometry

record Geometry (ℓ : Level) : Set (lsuc ℓ) where
  infix 6 _≈_
  infix 30 _<_
  field
    X : Set ℓ
    _≈_ : X → X → Set ℓ
    _<_ : X → X → Set ℓ
    ≈-refl : (x : X) → x ≈ x
    ≈-sym : {x y : X} → x ≈ y → y ≈ x
    ≈-trans : {x y z : X} → x ≈ y → y ≈ z → x ≈ z
    <-trans : {x y z : X} → x < y → y < z → x < z
    <-respˡ-≈ : {x x′ y : X} → x ≈ x′ → x < y → x′ < y
    <-respʳ-≈ : {x y y′ : X} → y ≈ y′ → x < y → x < y′
    <-wf : is-well-founded _<_
    compare↓ : (b x y : X) → x < b → y < b → Trichotomy _≈_ _<_ x y
    enum↓ : X → ℕ → Maybe X
    enum↓-sound : (b : X) (n : ℕ) (x : X) → enum↓ b n ＝ just x → x < b
    enum↓-covers : (b x : X) → x < b →
      Σ ℕ (λ n → Σ X (λ r → (enum↓ b n ＝ just r) × (r ≈ x)))

------------------------------------------------------------------------
-- Exact filtering of one presentation

module From𝒫 {ℓ : Level} (P : Countable-Ordinal𝒫 ℓ) where

  open Countable-Ordinal𝒫 P

  filter : X → Maybe X → Maybe X
  filter b nothing = nothing
  filter b (just x) with compare x b
  ... | inl x<b = just x
  ... | inr _ = nothing

  filter-sound : (b : X) (entry : Maybe X) (x : X) →
    filter b entry ＝ just x → x < b
  filter-sound b nothing x selected = 𝟘-elim (nothing-is-not-just selected)
  filter-sound b (just y) x selected with compare y b
  ... | inl y<b = transport (λ z → z < b) (just-is-injective selected) y<b
  ... | inr _ = 𝟘-elim (nothing-is-not-just selected)

  filter-< : (b : X) (entry : Maybe X) (x : X) → entry ＝ just x → x < b →
    filter b entry ＝ just x
  filter-< b nothing x selected x<b = 𝟘-elim (nothing-is-not-just selected)
  filter-< b (just .x) x refl x<b with compare x b
  ... | inl x<b′ = refl
  ... | inr (inl x≈b) = 𝟘-elim (Presentation.≈↛< P x≈b x<b)
  ... | inr (inr b<x) = 𝟘-elim (Presentation.<-asym P x<b b<x)

  enum↓ : X → ℕ → Maybe X
  enum↓ b n = filter b (enum n)

  enum↓-sound : (b : X) (n : ℕ) (x : X) → enum↓ b n ＝ just x → x < b
  enum↓-sound b n x = filter-sound b (enum n) x

  enum↓-covers : (b x : X) → x < b →
    Σ ℕ (λ n → Σ X (λ r → (enum↓ b n ＝ just r) × (r ≈ x)))
  enum↓-covers b x x<b with covers x
  ... | n , r , selected , r≈x =
    n , r , filter-< b (enum n) r selected (<-respˡ-≈ (≈-sym r≈x) x<b) ,
    r≈x

------------------------------------------------------------------------
-- Every presentation supplies the geometry

from𝒫 : {ℓ : Level} → Countable-Ordinal𝒫 ℓ → Geometry ℓ
from𝒫 P = record
  { X = Countable-Ordinal𝒫.X P
  ; _≈_ = Countable-Ordinal𝒫._≈_ P
  ; _<_ = Countable-Ordinal𝒫._<_ P
  ; ≈-refl = Countable-Ordinal𝒫.≈-refl P
  ; ≈-sym = Countable-Ordinal𝒫.≈-sym P
  ; ≈-trans = Countable-Ordinal𝒫.≈-trans P
  ; <-trans = Countable-Ordinal𝒫.<-trans P
  ; <-respˡ-≈ = Countable-Ordinal𝒫.<-respˡ-≈ P
  ; <-respʳ-≈ = Countable-Ordinal𝒫.<-respʳ-≈ P
  ; <-wf = Countable-Ordinal𝒫.<-wf P
  ; compare↓ = λ b x y x<b y<b → Countable-Ordinal𝒫.compare P x y
  ; enum↓ = From𝒫.enum↓ P
  ; enum↓-sound = From𝒫.enum↓-sound P
  ; enum↓-covers = From𝒫.enum↓-covers P
  }
