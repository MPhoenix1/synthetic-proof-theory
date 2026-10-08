{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Representative where

-- Canonical representatives of the classes of a presentation.
--
-- The quotient order type of a presentation is trichotomous, since
-- comparison of representatives decides strictness, so its carrier is
-- discrete. The enumeration of the presentation then selects, for every
-- class, the least index at which a member of the class is enumerated.
-- This is a section of the quotient map without any choice principle.
-- Classes are effective: equal classes have equivalent representatives.

open import Agda.Primitive using (Level)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType using
  ( Class; Less; orderType
  ; Less-isProp
  ; Less-intro
  ; Less-witness
  )
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Countability using
  (classEnumeration)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Woset using
  ( StrictTrichotomy; WosetStrictDecidable
  ; decidable→trichotomy; enumerationHit
  )

import Cubical.Foundations.Prelude as Cubical
import Cubical.HITs.SetQuotients as Quotient
import Cubical.Relation.Nullary as Nullary

private
  variable
    ℓ : Level

-- Strictness of classes is decided on representatives.
decide : (P : 𝒫 ℓ) → WosetStrictDecidable (orderType P)
decide P =
  Quotient.elimProp2
    (λ a b → Nullary.isPropDec (Less-isProp P a b))
    (λ x y → step x y (𝒫.compare P x y))
  where
  step : (x y : 𝒫.X P)
    → 𝒫._<_ P x y ⊎ (𝒫._≈_ P x y ⊎ 𝒫._<_ P y x)
    → Nullary.Dec (Less P Quotient.[ x ] Quotient.[ y ])
  step x y (inj₁ x<y) =
    Nullary.yes (Less-intro P x<y)
  step x y (inj₂ (inj₁ x≈y)) =
    Nullary.no λ s → ⊥-elim
      (Presented.Presentation.≈↛< P x≈y
        (Less-witness P s))
  step x y (inj₂ (inj₂ y<x)) =
    Nullary.no λ s → ⊥-elim
      (Presented.Presentation.<-asym P
        (Less-witness P s) y<x)

trichotomy : (P : 𝒫 ℓ) → StrictTrichotomy (orderType P)
trichotomy P = decidable→trichotomy (orderType P)
  (decide P)

-- Equal classes have equivalent representatives: a strict comparison
-- between the representatives would become a strict self-comparison.
effective : (P : 𝒫 ℓ) {x y : 𝒫.X P}
  → Quotient.[ x ] Cubical.≡ Quotient.[ y ] → 𝒫._≈_ P x y
effective P {x} {y} p with 𝒫.compare P x y
... | inj₁ x<y =
  ⊥-elim (Presented.Presentation.<-irrefl P y
    (Less-witness P
      (Cubical.subst (λ a → Less P a Quotient.[ y ]) p
        (Less-intro P x<y))))
... | inj₂ (inj₁ x≈y) = x≈y
... | inj₂ (inj₂ y<x) =
  ⊥-elim (Presented.Presentation.<-irrefl P y
    (Less-witness P
      (Cubical.subst (Less P Quotient.[ y ]) p
        (Less-intro P y<x))))

private
  -- An enumerated entry whose class is a, read off from the entry.
  entry : (P : 𝒫 ℓ) (a : Class P) (m : Maybe (𝒫.X P))
    → Maybe.map (λ x → Quotient.[ x ]) m Cubical.≡ just a
    → Σ (𝒫.X P) (λ x → Quotient.[ x ] Cubical.≡ a)
  entry P a nothing p =
    ⊥-elim (Cubical.subst (λ { nothing → ⊤ ; (just _) → ⊥ }) p tt)
  entry P a (just x) p = x , Cubical.cong (Maybe.fromMaybe a) p

  -- The member enumerated at the least index of the class.
  chosen : (P : 𝒫 ℓ) (a : Class P)
    → Σ (𝒫.X P) (λ x → Quotient.[ x ] Cubical.≡ a)
  chosen P a =
    let hit = enumerationHit (orderType P)
          (trichotomy P) (classEnumeration P) a
    in entry P a (𝒫.enum P (proj₁ hit)) (proj₂ hit)

-- Mathematical shape: a section of the quotient map,
--
--   representative : |P|/≈ → |P|,   [representative a] = a.
--
-- Nonclaim: the section is canonical for the enumeration of P; another
-- enumeration of the same order may select other representatives.
representative : (P : 𝒫 ℓ) → Class P → 𝒫.X P
representative P a = proj₁ (chosen P a)

class : (P : 𝒫 ℓ) (a : Class P)
  → Quotient.[ representative P a ] Cubical.≡ a
class P a = proj₂ (chosen P a)

-- The representative of a class is a member of it.
member : (P : 𝒫 ℓ) (x : 𝒫.X P)
  → 𝒫._≈_ P (representative P Quotient.[ x ]) x
member P x = effective P (class P Quotient.[ x ])
