{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Universe where

-- The Hartogs well-order of a small family of types D : C → Set ℓ, such
-- as the types named by the codes of a universe:
--
--   H(D) = Σ (α : Woset ℓ ℓ). ‖Σ (c : C). |α| ↪ D c‖,
--
-- the well-orders whose carrier merely embeds into some D c, ordered by ≺
-- (Reflection.Ordinals.Lower).  Its cut
--
--   α ≺ H(D) ⇔ ‖Σ c. |α| ↪ D c‖                           (cut)
--
-- and its equivalence with every small well-order meeting the same cut
-- (unique) are constructive.  For the one type ℕ this is H_ℕ.

open import Agda.Primitive using (Level; lsuc)

import Cubical.Data.Sigma.Base as Sigma
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.Prelude as Cubical
import Cubical.Functions.Embedding as Embedding
import Cubical.HITs.PropositionalTruncation as Truncation
open Truncation using (∥_∥₁)
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Ordinals.Lower
  as Lower

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- Embedding into a member of the family

-- Mathematical shape: Embeds D A = ‖Σ (c : C). A ↪ D c‖.
Embeds : {C : Set ℓ} (D : C → Set ℓ) → Set ℓ → Set ℓ
Embeds {C = C} D A = ∥ Cubical.Σ C (λ c → A Embedding.↪ D c) ∥₁

-- α ≺ β → Embeds D |β| → Embeds D |α|: α is a principal segment of β,
-- which includes into |β|.
embeds-below : {C : Set ℓ} (D : C → Set ℓ) (α β : Woset.Woset ℓ ℓ)
  → Simulation._≺_ α β
  → Embeds D (Cubical.fst β) → Embeds D (Cubical.fst α)
embeds-below D α β strict =
  Truncation.map λ found →
    Cubical.fst found Cubical.,
    Embedding.compEmbedding (Cubical.snd found)
      (Embedding.compEmbedding
        (Embedding.EmbeddingΣProp λ x →
          Woset.IsWoset.is-prop-valued
            (Woset.WosetStr.isWoset (Cubical.snd β)) x (Cubical.fst strict))
        (Embedding.Equiv→Embedding
          (Equiv.invEquiv (Cubical.fst (Cubical.snd strict)))))

-- Embeds D (|α|), as a lower property of small well-orders.
lower : {C : Set ℓ} (D : C → Set ℓ) → Lower.Lower ℓ ℓ
lower D = record
  { holds = λ α → Embeds D (Cubical.fst α)
  ; holds-prop = λ _ → Truncation.squash₁
  ; holds-below = embeds-below D
  }

------------------------------------------------------------------------
-- The Hartogs well-order and its cut

-- Mathematical shape: H(D) = Σ (α : Woset ℓ ℓ). Embeds D |α|, under ≺.
Hartogs : {C : Set ℓ} (D : C → Set ℓ) → Woset.Woset (lsuc ℓ) ℓ
Hartogs D = Lower.segment (lower D)

-- The cut of a small well-order κ by D: α ≺ κ ⇔ Embeds D |α|.
Cut : {C : Set ℓ} (D : C → Set ℓ) → Woset.Woset ℓ ℓ → Set (lsuc ℓ)
Cut {ℓ} D κ =
  (α : Woset.Woset ℓ ℓ)
  → (Simulation._≺_ α κ → Embeds D (Cubical.fst α))
    Sigma.× (Embeds D (Cubical.fst α) → Simulation._≺_ α κ)

-- The statements of Lower are carried to Hartogs D along refl: checking
-- them against Hartogs D directly would unfold the whole order structure.
private
  same : {C : Set ℓ} (D : C → Set ℓ)
    → Lower.segment (lower D) Cubical.≡ Hartogs D
  same D = Cubical.refl

cut : {C : Set ℓ} (D : C → Set ℓ) (α : Woset.Woset ℓ ℓ)
  → (Simulation._≺_ α (Hartogs D) → Embeds D (Cubical.fst α))
    Sigma.× (Embeds D (Cubical.fst α) → Simulation._≺_ α (Hartogs D))
cut D α =
  Cubical.subst
    (λ X → (Simulation._≺_ α X → Embeds D (Cubical.fst α))
      Sigma.× (Embeds D (Cubical.fst α) → Simulation._≺_ α X))
    (same D) (Lower.cut (lower D) α)

-- Mathematical shape: Cut D κ → κ ≃ H(D).
unique : {C : Set ℓ} (D : C → Set ℓ) (κ : Woset.Woset ℓ ℓ)
  → Cut D κ → Woset.WosetEquiv κ (Hartogs D)
unique D κ κ-cut =
  Cubical.subst (Woset.WosetEquiv κ) (same D) (Lower.unique (lower D) κ κ-cut)
