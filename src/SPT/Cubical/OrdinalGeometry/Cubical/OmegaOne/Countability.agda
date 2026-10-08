{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Countability where

-- The cut of ω₁ in terms of countability: for small well-orders with
-- strict trichotomy, α ≺ ω₁ ⇔ IsCountable(|α|); under excluded middle,
-- for all small well-orders, both with IsCountable and with ‖|α| ↪ ℕ‖.

open import Agda.Primitive using (Level)

import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Countability
  as Countability
import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Countability
  as NatCountability
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType as Reflection
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Base as Omega
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Cut as Cut
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Woset as Converse

import Cubical.Data.Sigma.Base as Sigma
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.Prelude as Cubical
import Cubical.HITs.PropositionalTruncation as Truncation
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- Presented and countable well-orders

-- MerelyPresented(α) → IsCountable(|α|), by the enumeration of P.

presented→countable :
    (ordinal : Woset.Woset ℓ ℓ)
  → Cut.MerelyPresented ordinal
  → Countability.IsCountable (Cubical.fst ordinal)
presented→countable ordinal =
  Truncation.rec
    Countability.isPropIsCountable
    (λ represented →
      Countability.isCountable-respects-equivalence
        (Cubical.fst (Cubical.snd represented))
        (Countability.orderType-countable
          (Cubical.fst represented)))

-- StrictTrichotomy(α) → IsCountable(|α|) → MerelyPresented(α), through the
-- presentation of α on its own carrier (Reflection.Woset).

countable→presented :
    (ordinal : Woset.Woset ℓ ℓ)
  → Converse.StrictTrichotomy ordinal
  → Countability.IsCountable (Cubical.fst ordinal)
  → Cut.MerelyPresented ordinal
countable→presented ordinal trichotomy =
  Truncation.rec
    (Cut.isPropMerelyPresented ordinal)
    (λ enumeration →
      let
        presentation =
          Converse.toPresentation
            ordinal trichotomy enumeration

        reflected-equality =
          Converse.toPresentation-orderType
            ordinal trichotomy enumeration
      in
      Truncation.∣
        Cubical._,_
          presentation
          (Equiv.invEq
            (Woset.WosetPath
              (Reflection.orderType presentation)
              ordinal)
            reflected-equality)
      ∣₁)

------------------------------------------------------------------------
-- The countability cut

strict→countable :
    (ordinal : Woset.Woset ℓ ℓ)
  → Simulation._≺_ ordinal (Omega.ω₁ ℓ)
  → Countability.IsCountable (Cubical.fst ordinal)
strict→countable ordinal strict =
  presented→countable ordinal
    (Cut.strict→presented ordinal strict)

countable→strict :
    (ordinal : Woset.Woset ℓ ℓ)
  → Converse.StrictTrichotomy ordinal
  → Countability.IsCountable (Cubical.fst ordinal)
  → Simulation._≺_ ordinal (Omega.ω₁ ℓ)
countable→strict ordinal trichotomy =
  Cut.presented→strict ordinal
    ∘ countable→presented ordinal trichotomy
  where
    _∘_ :
        ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
      → (B → C) → (A → B) → A → C
    (forward ∘ backward) input = forward (backward input)

-- StrictTrichotomy(α) → (α ≺ ω₁(ℓ) ⇔ IsCountable(|α|)).  The forward
-- direction holds without trichotomy.

countability-cut :
    (ordinal : Woset.Woset ℓ ℓ)
  → Converse.StrictTrichotomy ordinal
  → (Simulation._≺_ ordinal (Omega.ω₁ ℓ)
      → Countability.IsCountable (Cubical.fst ordinal))
    Sigma.×
    (Countability.IsCountable (Cubical.fst ordinal)
      → Simulation._≺_ ordinal (Omega.ω₁ ℓ))
countability-cut ordinal trichotomy =
  Sigma._,_
    (strict→countable ordinal)
    (countable→strict
      ordinal trichotomy)

decidable-countability-cut :
    (ordinal : Woset.Woset ℓ ℓ)
  → Converse.WosetStrictDecidable ordinal
  → (Simulation._≺_ ordinal (Omega.ω₁ ℓ)
      → Countability.IsCountable (Cubical.fst ordinal))
    Sigma.×
    (Countability.IsCountable (Cubical.fst ordinal)
      → Simulation._≺_ ordinal (Omega.ω₁ ℓ))
decidable-countability-cut ordinal decide =
  countability-cut ordinal
    (Converse.decidable→trichotomy ordinal decide)

------------------------------------------------------------------------
-- Under excluded middle

-- Excluded middle at ℓ (from Hartogs.Countability), which decides the strict
-- order of a small well-order.

open NatCountability using (ExcludedMiddle) public

excludedMiddle→decidable :
    ExcludedMiddle ℓ
  → (ordinal : Woset.Woset ℓ ℓ)
  → Converse.WosetStrictDecidable ordinal
excludedMiddle→decidable excluded-middle ordinal left right =
  excluded-middle
    (Converse.WosetStrict ordinal left right)
    (Woset.IsWoset.is-prop-valued
      (Woset.WosetStr.isWoset (Cubical.snd ordinal))
      left right)

-- ExcludedMiddle(ℓ) → (α ≺ ω₁(ℓ) ⇔ IsCountable(|α|)), for every small
-- well-order α: ω₁ is the boundary between countable and uncountable small
-- well-orders.  No countable choice or resizing is used.

classical-countability-cut :
    ExcludedMiddle ℓ
  → (ordinal : Woset.Woset ℓ ℓ)
  → (Simulation._≺_ ordinal (Omega.ω₁ ℓ)
      → Countability.IsCountable (Cubical.fst ordinal))
    Sigma.×
    (Countability.IsCountable (Cubical.fst ordinal)
      → Simulation._≺_ ordinal (Omega.ω₁ ℓ))
classical-countability-cut excluded-middle ordinal =
  decidable-countability-cut ordinal
    (excludedMiddle→decidable excluded-middle ordinal)

------------------------------------------------------------------------
-- In terms of embeddings into ℕ

-- ExcludedMiddle(ℓ) → (α ≺ ω₁(ℓ) ⇔ ‖|α| ↪ ℕ‖); the two directions and
-- `classical-embedding-cut`.

strict→embeds :
    ExcludedMiddle ℓ
  → (ordinal : Woset.Woset ℓ ℓ)
  → Simulation._≺_ ordinal (Omega.ω₁ ℓ)
  → NatCountability.MerelyEmbedsInNat (Cubical.fst ordinal)
strict→embeds
    excluded-middle ordinal strict =
  NatCountability.countable→embeds
    excluded-middle
    carrier-is-set
    (strict→countable ordinal strict)
  where
    carrier-is-set : Cubical.isSet (Cubical.fst ordinal)
    carrier-is-set =
      Woset.IsWoset.is-set
        (Woset.WosetStr.isWoset (Cubical.snd ordinal))

embeds→strict :
    ExcludedMiddle ℓ
  → (ordinal : Woset.Woset ℓ ℓ)
  → NatCountability.MerelyEmbedsInNat (Cubical.fst ordinal)
  → Simulation._≺_ ordinal (Omega.ω₁ ℓ)
embeds→strict
    excluded-middle ordinal embeds =
  countable→strict
    ordinal
    (Converse.decidable→trichotomy
      ordinal
      (excludedMiddle→decidable excluded-middle ordinal))
    (NatCountability.embeds→countable
      excluded-middle embeds)

classical-embedding-cut :
    ExcludedMiddle ℓ
  → (ordinal : Woset.Woset ℓ ℓ)
  → (Simulation._≺_ ordinal (Omega.ω₁ ℓ)
      → NatCountability.MerelyEmbedsInNat (Cubical.fst ordinal))
    Sigma.×
    (NatCountability.MerelyEmbedsInNat (Cubical.fst ordinal)
      → Simulation._≺_ ordinal (Omega.ω₁ ℓ))
classical-embedding-cut
    excluded-middle ordinal =
  Sigma._,_
    (strict→embeds
      excluded-middle ordinal)
    (embeds→strict
      excluded-middle ordinal)
