{-# OPTIONS --safe --without-K #-}

module SPT.OrdinalGeometry.Presentation.CountablyPresented.LowerCone where

-- The strict lower cone Σ x. x < b of a point b of a countably presented
-- geometry, as a countable presentation (`𝒫`):
--
--   Cone b = Σ x : X. x < b,
--
-- with the geometry's equivalence and order on first projections; the
-- strict witness stays literal and is ignored by both relations. The
-- enumeration keeps the successful occurrences of the geometry's lower-cone
-- sequence at b, and comparison is the geometry's local trichotomy below b.
-- It does not assert that independently given points are comparable.

open import SPT.Base
open import SPT.Foundation.WellFounded.Pullback using
  (pullback-is-well-founded)
open import SPT.OrdinalGeometry.Presentation.CountableOrdinal using
  (Countable-Ordinal𝒫)
open import SPT.OrdinalGeometry.Presentation.CountablyPresented using
  (Geometry)
open import SPT.OrdinalGeometry.Presentation.Enumeration using
  ( Entry; present; Occurrence; occurrence-value; occurrence-selects
  ; enumerate-occurrences; occurrences-are-covered )

module _ {ℓ : Level} (𝒢 : Geometry ℓ) where

  open Geometry 𝒢

  Cone : X → Set ℓ
  Cone b = Σ X (λ x → x < b)

  from-occurrence : (b : X) → Occurrence (enum↓ b) → Cone b
  from-occurrence b occurrence =
    occurrence-value (enum↓ b) occurrence ,
    enum↓-sound b (pr₁ occurrence) (occurrence-value (enum↓ b) occurrence)
      (occurrence-selects (enum↓ b) occurrence)

  enum : (b : X) → ℕ → Maybe (Cone b)
  enum b n =
    maybe-map (from-occurrence b) (enumerate-occurrences (enum↓ b) n)

  covers : (b : X) (x : Cone b) →
    Σ ℕ (λ n →
      Σ (Cone b) (λ r → (enum b n ＝ just r) × (pr₁ r ≈ pr₁ x)))
  covers b (x , x<b) with enum↓-covers b x x<b
  ... | n , r , selected , r≈x =
    let occurrence = n , transport Entry (selected ⁻¹) present
    in pr₁ (occurrences-are-covered (enum↓ b) occurrence) ,
       from-occurrence b occurrence ,
       ap (maybe-map (from-occurrence b))
         (pr₂ (occurrences-are-covered (enum↓ b) occurrence)) ,
       transport (λ y → y ≈ x)
         (just-is-injective
           (selected ⁻¹ ∙ occurrence-selects (enum↓ b) occurrence))
         r≈x

  -- The presentation of the strict lower cone of b.
  𝒫 : X → Countable-Ordinal𝒫 ℓ
  𝒫 b = record
    { X = Cone b
    ; _≈_ = λ x y → pr₁ x ≈ pr₁ y
    ; _<_ = λ x y → pr₁ x < pr₁ y
    ; ≈-refl = λ x → ≈-refl (pr₁ x)
    ; ≈-sym = ≈-sym
    ; ≈-trans = ≈-trans
    ; <-trans = <-trans
    ; <-respˡ-≈ = <-respˡ-≈
    ; <-respʳ-≈ = <-respʳ-≈
    ; <-wf = pullback-is-well-founded pr₁ _<_ <-wf
    ; compare = λ x y → compare↓ b (pr₁ x) (pr₁ y) (pr₂ x) (pr₂ y)
    ; enum = enum b
    ; covers = covers b
    }
