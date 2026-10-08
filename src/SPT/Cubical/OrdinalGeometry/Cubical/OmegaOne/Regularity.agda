{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Regularity where

-- Regularity of the presented ω₁: every ℕ-sequence of points has a strict
-- upper bound (Regular). Stated for every H satisfying the cut
-- specification of ω₁ (Specification.IsOmegaOneCut:
-- principal segments merely presented, every presentation strictly below),
-- so for the presented ω₁ of every geometry and for ω₁
-- (omega-one, omega-one-choice). Its strength:
-- - Regular gives LPO (lpo). The points of possible s + 1 and of 1 already
--   need a common strict bound; that bound is merely presented, and a
--   common initial bound of the two presentations decides s
--   (Ambient.Discriminator.common). No choice is used: these points come
--   with their presentations.
-- - LPO and presentations of the segments below the points of a sequence
--   give the bound (regular): the successor of the supremum of the
--   presentations (Arithmetic.Comparison.bound), placed in H.
-- - Countable choice supplies those presentations, since each principal
--   segment is merely presented: LPO and countable choice give Regular
--   (choice).
-- For sequences given by presentations the bound is exactly LPO
-- (Arithmetic.Comparison.Strength.bound). Presentations is the datum
-- between the points and their presentations; whether Regular needs it
-- beyond LPO is not settled here.

open import Agda.Primitive using (Level; lzero; lsuc)
open import Data.Bool using (Bool)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; proj₁; proj₂)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Limit.Discriminator as Stream
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Ambient.Discriminator using
  (common; family)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Comparison as Comparison
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType using
  (orderType)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Simulation using
  (segment)
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Simulation.Converse
  as Converse
open import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Base using
  (ω₁)
open import
  SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Supremum.Discriminator
  using (Decision; Settled; settled; settle; unsettle)
open import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Specification
  using
  ( IsOmegaOneCut
  ; principal-segment-presented
  ; all-presentations-strict
  ; isOmegaOneCut
  )

import Cubical.Foundations.Prelude as Cubical
import Cubical.HITs.PropositionalTruncation as Truncation
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

private
  variable
    ℓ : Level

-- Mathematical shape: ∃ b. Π n. f n < b, in H.
Bounded : (H : Woset.Woset (lsuc ℓ) ℓ) → (ℕ → Cubical.fst H) → Set (lsuc ℓ)
Bounded H f = Truncation.∥ Cubical.Σ (Cubical.fst H)
  (λ b → (n : ℕ) → Woset.WosetStr._≺_ (Cubical.snd H) (f n) b) ∥₁

-- Mathematical shape: Π f : ℕ → H. ∃ b. Π n. f n < b.
Regular : (H : Woset.Woset (lsuc ℓ) ℓ) → Set (lsuc ℓ)
Regular H = (f : ℕ → Cubical.fst H) → Bounded H f

-- Mathematical shape: Π n. Σ P. P′ ≃ H ↓ f n.
Presentations : (H : Woset.Woset (lsuc ℓ) ℓ) → (ℕ → Cubical.fst H)
  → Set (lsuc ℓ)
Presentations {ℓ} H f = (n : ℕ) → Cubical.Σ (𝒫 ℓ) (λ P →
  Woset.WosetEquiv (orderType P) (Simulation._↓_ H (f n)))

-- Mathematical shape: Π A : ℕ → Set. (Π n. ‖A n‖) → ‖Π n. A n‖.
CountableChoice : (κ : Level) → Set (lsuc κ)
CountableChoice κ = (A : ℕ → Set κ) → ((n : ℕ) → Truncation.∥ A n ∥₁)
  → Truncation.∥ ((n : ℕ) → A n) ∥₁

-- Mathematical shape: LPO → ‖Presentations f‖ → ∃ b. Π n. f n < b.
regular : Stream.LPO → (H : Woset.Woset (lsuc ℓ) ℓ)
  → IsOmegaOneCut H
  → (f : ℕ → Cubical.fst H) → Truncation.∥ Presentations H f ∥₁
  → Bounded H f
regular {ℓ} lpo H cut f = Truncation.map bounded
  where
  bounded : Presentations H f → Cubical.Σ (Cubical.fst H)
    (λ b → (n : ℕ) → Woset.WosetStr._≺_ (Cubical.snd H) (f n) b)
  bounded g = Cubical._,_ (Cubical.fst placed) λ n →
    Simulation.↓Respects≺⁻ H (f n) (Cubical.fst placed)
      (Simulation.≺RespectsEquiv (Cubical.snd (g n))
        (Woset.invWosetEquiv (Cubical.snd placed))
        (segment {P = Cubical.fst (g n)} {Q = proj₁ strict}
          (proj₂ strict n)))
    where
    strict : Σ (𝒫 ℓ) (λ S → (n : ℕ) → Maps.Segment (Cubical.fst (g n)) S)
    strict = Comparison.bound lpo (λ n → Cubical.fst (g n))

    placed : orderType (proj₁ strict) Simulation.≺ H
    placed = all-presentations-strict cut (proj₁ strict)

-- Mathematical shape: LPO → AC_ω → Regular H.
choice : Stream.LPO → CountableChoice (lsuc ℓ)
  → (H : Woset.Woset (lsuc ℓ) ℓ) → IsOmegaOneCut H
  → Regular H
choice {ℓ} lpo select H cut f =
  regular lpo H cut f
    (select (λ n → Cubical.Σ (𝒫 ℓ) (λ P →
        Woset.WosetEquiv (orderType P) (Simulation._↓_ H (f n))))
      (λ n → principal-segment-presented cut (f n)))

private
  -- A presentation S of the segment below a strict bound b of the members
  -- of the family, placed in H, is a common strict bound of the members,
  -- which decides s.
  decide : (H : Woset.Woset (lsuc lzero) lzero)
    (cut : IsOmegaOneCut H)
    (s : ℕ → Bool) (b : Cubical.fst H)
    → ((n : ℕ) → Woset.WosetStr._≺_ (Cubical.snd H)
        (Cubical.fst (all-presentations-strict cut (family s n))) b)
    → (S : 𝒫 lzero)
    → Woset.WosetEquiv (orderType S) (Simulation._↓_ H b)
    → Decision s
  decide H cut s b below S e =
    common s S (Maps.inclusion (into zero))
      (Maps.inclusion (into (suc zero)))
    where
    into : (n : ℕ) → Maps.Segment (family s n) S
    into n =
      Converse.segment {P = family s n} {Q = S}
        (Simulation.≺RespectsEquiv
          (Cubical.snd (all-presentations-strict cut (family s n)))
          (Woset.invWosetEquiv e)
          (Simulation.↓Respects≺ H
            (Cubical.fst (all-presentations-strict cut (family s n))) b
            (below n)))

-- Mathematical shape: Regular H → LPO.
lpo : (H : Woset.Woset (lsuc lzero) lzero)
  → IsOmegaOneCut H → Regular H → Stream.LPO
lpo H cut regularity s =
  unsettle s
    (Truncation.rec (settled s) bounded
      (regularity λ n →
        Cubical.fst (all-presentations-strict cut (family s n))))
  where
  bounded : Cubical.Σ (Cubical.fst H) (λ b → (n : ℕ)
      → Woset.WosetStr._≺_ (Cubical.snd H)
          (Cubical.fst (all-presentations-strict cut (family s n))) b)
    → Settled s
  bounded (Cubical._,_ b below) =
    Truncation.rec (settled s)
      (λ represented → settle s
        (decide H cut s b below (Cubical.fst represented)
          (Cubical.snd represented)))
      (principal-segment-presented cut b)

-- The presented ω₁: Regular gives LPO, and LPO with countable choice gives
-- Regular.
-- The levels are given, so that ω₁ is never unfolded.
omega-one : Regular (ω₁ lzero) → Stream.LPO
omega-one = lpo (ω₁ lzero)
  (isOmegaOneCut {lzero})

omega-one-choice : Stream.LPO → CountableChoice (lsuc ℓ)
  → Regular (ω₁ ℓ)
omega-one-choice {ℓ} lpo select =
  choice {ℓ} lpo select (ω₁ ℓ)
    (isOmegaOneCut {ℓ})
