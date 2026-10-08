{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Presentation.CountablyPresented where

-- Countably presented geometries: a well-founded order modulo an
-- equivalence in which comparison is required only below a common bound,
-- and every point b comes with a partial enumeration of its strict lower
-- cone.  Every presentation gives one, by filtering its enumeration below
-- b (`from𝒫`).

open import Agda.Primitive using (Level; lsuc)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst)

open import SPT.Cubical.Core.WellFounded using (WellFounded)
import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as 𝒫

------------------------------------------------------------------------
-- Countably presented geometries

-- A countably presented geometry at level ℓ:
--
--   Geometry(ℓ) ≃ Σ(X : Set ℓ). Σ(≈ < : X → X → Set ℓ).
--       Equivalence(≈) × Transitive(<) × Respects₂(<,≈) × WellFounded(<)
--     × (Π b x y. x < b → y < b → x < y + (x ≈ y + y < x))
--     × Π b. Σ(e_b : ℕ → Maybe X). Sound_b(e_b) × Covers_b(e_b),
--
-- where Sound_b(e) says every entry of e lies below b and Covers_b(e) says
-- every x < b is equivalent to some entry.  Unlike a presentation, two
-- points need not be comparable unless they lie below a common bound.

record Geometry (ℓ : Level) : Set (lsuc ℓ) where

  field

    X : Set ℓ

    _≈_ : X → X → Set ℓ

    _<_ : X → X → Set ℓ

    ≈-refl :
      (x : X) → x ≈ x

    ≈-sym :
      ∀ {x y}
      → x ≈ y
      → y ≈ x

    ≈-trans :
      ∀ {x y z}
      → x ≈ y
      → y ≈ z
      → x ≈ z

    <-trans :
      ∀ {x y z}
      → x < y
      → y < z
      → x < z

    <-respˡ-≈ :
      ∀ {x x′ y}
      → x ≈ x′
      → x < y
      → x′ < y

    <-respʳ-≈ :
      ∀ {x y y′}
      → y ≈ y′
      → x < y
      → x < y′

    <-wf :
      WellFounded _<_

    compare↓ :
        (b x y : X)
      → x < b
      → y < b
      → x < y ⊎ (x ≈ y ⊎ y < x)

    enum↓ :
      X → ℕ → Maybe X

    enum↓-sound :
        (b : X)
      → (n : ℕ)
      → (x : X)
      → enum↓ b n ≡ just x
      → x < b

    enum↓-covers :
        (b x : X)
      → x < b
      → Σ ℕ λ n →
          Σ X λ r →
            (enum↓ b n ≡ just r)
            × (r ≈ x)

------------------------------------------------------------------------
-- Filtering a presentation below a bound

private
  nothing≢just :
      ∀ {ℓ} {A : Set ℓ} {x : A}
    → nothing ≢ just x
  nothing≢just ()

module From𝒫 {ℓ : Level} (P : 𝒫.CountableOrdinal𝒫 ℓ) where

  open 𝒫.CountableOrdinal𝒫 P

  filter :
      X
    → Maybe X
    → Maybe X
  filter b nothing =
    nothing
  filter b (just x) with compare x b
  ... | inj₁ x<b =
    just x
  ... | inj₂ _ =
    nothing

  filter-sound :
      (b : X)
    → (entry : Maybe X)
    → (x : X)
    → filter b entry ≡ just x
    → x < b
  filter-sound b nothing x selected =
    ⊥-elim (nothing≢just selected)
  filter-sound b (just y) x selected with compare y b
  ... | inj₁ y<b =
    subst
      (λ z → z < b)
      (just-injective selected)
      y<b
  ... | inj₂ _ =
    ⊥-elim (nothing≢just selected)

  filter-< :
      (b : X)
    → (entry : Maybe X)
    → (x : X)
    → entry ≡ just x
    → x < b
    → filter b entry ≡ just x
  filter-< b nothing x selected x<b =
    ⊥-elim (nothing≢just selected)
  filter-< b (just .x) x refl x<b with compare x b
  ... | inj₁ x<b′ =
    refl
  ... | inj₂ (inj₁ x≈b) =
    ⊥-elim (𝒫.Presentation.≈↛< P x≈b x<b)
  ... | inj₂ (inj₂ b<x) =
    ⊥-elim (𝒫.Presentation.<-asym P x<b b<x)

  enum↓ :
      X
    → ℕ
    → Maybe X
  enum↓ b n =
    filter b (enum n)

  enum↓-sound :
      (b : X)
    → (n : ℕ)
    → (x : X)
    → enum↓ b n ≡ just x
    → x < b
  enum↓-sound b n x =
    filter-sound b (enum n) x

  enum↓-covers :
      (b x : X)
    → x < b
    → Σ ℕ λ n →
        Σ X λ r →
          (enum↓ b n ≡ just r)
          × (r ≈ x)
  enum↓-covers b x x<b with covers x
  ... | n , r , selected , r≈x =
    n
    , r
    , filter-< b (enum n) r selected r<b
    , r≈x
    where
      r<b : r < b
      r<b =
        <-respˡ-≈ (≈-sym r≈x) x<b

  geometry : Geometry ℓ
  geometry = record
    { X = X
    ; _≈_ = _≈_
    ; _<_ = _<_
    ; ≈-refl = ≈-refl
    ; ≈-sym = ≈-sym
    ; ≈-trans = ≈-trans
    ; <-trans = <-trans
    ; <-respˡ-≈ = <-respˡ-≈
    ; <-respʳ-≈ = <-respʳ-≈
    ; <-wf = <-wf
    ; compare↓ = λ b x y x<b y<b → compare x y
    ; enum↓ = enum↓
    ; enum↓-sound = enum↓-sound
    ; enum↓-covers = enum↓-covers
    }

------------------------------------------------------------------------
-- Every presentation gives a countably presented geometry

from𝒫 :
    ∀ {ℓ}
  → 𝒫.CountableOrdinal𝒫 ℓ
  → Geometry ℓ
from𝒫 P =
  From𝒫.geometry P
