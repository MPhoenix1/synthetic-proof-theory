{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Cardinal where

-- Classical large-cardinal notions, for small well-orders κ read in the
-- universe of level ℓ:
--
--   Cardinal κ      no α ≺ κ receives an embedding of |κ|;
--   Uncountable κ   every γ with |γ| ↪ ℕ lies below κ;
--   Regular κ       for α ≺ κ, every family of members of κ indexed by
--                   |α| lies below some γ ≺ κ;
--   StrongLimit κ   for α ≺ κ, every γ with |γ| ↪ (|α| → 𝟐) lies below κ;
--   Inaccessible κ  all four;
--
-- and MahloOrdinals ℓ: every f : Ord ℓ → Ord ℓ has inaccessible closure
-- points above every β.
--
-- Under excluded middle |α| → 𝟐 is the power set of |α|, and Regular is
-- the statement that cofinal families have size κ.  Choice is stated for
-- set-indexed families.  For a universe (C , D) with formers and decoding
-- laws (Core.Mahlo.Decoding), a small κ with the Hartogs cut
-- α ≺ κ ⇔ ‖Σ c. |α| ↪ D c‖ is an uncountable cardinal, and under excluded
-- middle a strong limit.  Regularity is proved for the ranks of
-- reflections, in Height.Hartogs.

open import Agda.Primitive using (Level; lsuc)
open import Data.Empty using (⊥)

import Cubical.Data.Bool as Bool
open Bool using (Bool)
import Cubical.Data.Sigma.Base as Sigma
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.Prelude as Cubical
import Cubical.Functions.Embedding as Embedding
import Cubical.HITs.PropositionalTruncation as Truncation
open Truncation using (∥_∥₁)
import Cubical.Induction.WellFounded as WellFounded
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

open import SPT.Cubical.Core.Mahlo.Specification using (Formers)
open import SPT.Cubical.Core.Mahlo.Decoding using (DecodingLaws)
open import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Countability using
  (ExcludedMiddle; MerelyEmbedsInNat)
open import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Universe using
  (Embeds; Cut)
open import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.PowerSet using
  (extend)
open import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Formers using
  (natural-≃; power; power-≃)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- The notions

Cardinal : Woset.Woset ℓ ℓ → Set (lsuc ℓ)
Cardinal {ℓ} κ =
  (α : Woset.Woset ℓ ℓ) → Simulation._≺_ α κ
  → ∥ Cubical.fst κ Embedding.↪ Cubical.fst α ∥₁ → ⊥

Uncountable : Woset.Woset ℓ ℓ → Set (lsuc ℓ)
Uncountable {ℓ} κ =
  (γ : Woset.Woset ℓ ℓ) → MerelyEmbedsInNat (Cubical.fst γ)
  → Simulation._≺_ γ κ

Regular : Woset.Woset ℓ ℓ → Set (lsuc ℓ)
Regular {ℓ} κ =
  (α : Woset.Woset ℓ ℓ) → Simulation._≺_ α κ
  → (F : Cubical.fst α → Woset.Woset ℓ ℓ)
  → ((a : Cubical.fst α) → Simulation._≺_ (F a) κ)
  → ∥ Cubical.Σ (Woset.Woset ℓ ℓ) (λ γ →
      Simulation._≺_ γ κ
      Sigma.× ((a : Cubical.fst α) → Simulation._≺_ (F a) γ)) ∥₁

StrongLimit : Woset.Woset ℓ ℓ → Set (lsuc ℓ)
StrongLimit {ℓ} κ =
  (α : Woset.Woset ℓ ℓ) → Simulation._≺_ α κ
  → (γ : Woset.Woset ℓ ℓ)
  → ∥ Cubical.fst γ Embedding.↪ (Cubical.fst α → Bool) ∥₁
  → Simulation._≺_ γ κ

record Inaccessible (κ : Woset.Woset ℓ ℓ) : Set (lsuc ℓ) where
  field
    cardinal : Cardinal κ
    uncountable : Uncountable κ
    regular : Regular κ
    strong-limit : StrongLimit κ

-- Ord(ℓ) is Mahlo in the function form: every f : Ord ℓ → Ord ℓ has
-- inaccessible closure points above every β.  Classically this
-- characterizes the Mahlo cardinals among the regular ones: the closure
-- points of f form a club, and every club contains those of some f.
MahloOrdinals : (ℓ : Level) → Set (lsuc ℓ)
MahloOrdinals ℓ =
  (f : Woset.Woset ℓ ℓ → Woset.Woset ℓ ℓ) (β : Woset.Woset ℓ ℓ)
  → Cubical.Σ (Woset.Woset ℓ ℓ) λ κ →
      Simulation._≺_ β κ
      Sigma.× Inaccessible κ
      Sigma.× ((α : Woset.Woset ℓ ℓ)
        → Simulation._≺_ α κ → Simulation._≺_ (f α) κ)

-- Choice for set-indexed families of types of level ℓ.
Choice : (ℓ : Level) → Set (lsuc ℓ)
Choice ℓ =
  (I : Set ℓ) (P : I → Set ℓ) → Cubical.isSet I
  → ((i : I) → ∥ P i ∥₁) → ∥ ((i : I) → P i) ∥₁

-- No small well-order lies below itself.
irreflexive : (κ : Woset.Woset ℓ ℓ) → Simulation._≺_ κ κ → ⊥
irreflexive {ℓ} κ = loop κ (Simulation.isWellFounded≺ κ)
  where
    loop : (x : Woset.Woset ℓ ℓ) → WellFounded.Acc Simulation._≺_ x
      → Simulation._≺_ x x → ⊥
    loop x (WellFounded.acc smaller) p = loop x (smaller x p) p

------------------------------------------------------------------------
-- Well-orders with a Hartogs cut

-- An embedding of |κ| into a member α would put κ below itself.
cardinal : {C : Set ℓ} (D : C → Set ℓ) (κ : Woset.Woset ℓ ℓ)
  → Cut D κ → Cardinal κ
cardinal D κ κ-cut α α<κ into =
  irreflexive κ
    (Cubical.snd (κ-cut κ)
      (Truncation.map2
        (λ found e →
          Cubical.fst found Cubical.,
          Embedding.compEmbedding (Cubical.snd found) e)
        (Cubical.fst (κ-cut α) α<κ) into))

module _ {C : Set ℓ} {D : C → Set ℓ} (Q : Formers C D)
  (laws : DecodingLaws Q) (κ : Woset.Woset ℓ ℓ) (κ-cut : Cut D κ) where

  -- ℕ is named by the natural code.
  uncountable : Uncountable κ
  uncountable γ countable =
    Cubical.snd (κ-cut γ)
      (Truncation.map
        (λ e →
          Formers.natural Q Cubical.,
          Embedding.compEmbedding
            (Embedding.Equiv→Embedding (Equiv.invEquiv (natural-≃ Q laws)))
            e)
        countable)

  -- (|α| → 𝟐) embeds into the power code of a code that |α| embeds into.
  strong-limit : ExcludedMiddle ℓ → StrongLimit κ
  strong-limit lem α α<κ γ small =
    Cubical.snd (κ-cut γ)
      (Truncation.map2
        (λ found e →
          power Q laws (Cubical.fst found) Cubical.,
          Embedding.compEmbedding
            (Embedding.Equiv→Embedding
              (Equiv.invEquiv (power-≃ Q laws (Cubical.fst found))))
            (Embedding.compEmbedding (extend lem (Cubical.snd found)) e))
        (Cubical.fst (κ-cut α) α<κ) small)
