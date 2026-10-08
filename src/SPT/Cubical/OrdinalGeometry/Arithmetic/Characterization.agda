{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization where

-- Zero, successors and suprema of presented ordinals, characterized by
-- initial maps (≤) and proper segments (<), as in the axiomatic framework
-- of Kraus, Nordvall Forsberg and Xu. Each characterization determines its
-- presentation up to ≃𝒫 and has an inhabitant: the empty presentation,
-- P + 1, and the completion of a chain. The successor P + 1 is strong:
-- every proper segment of P + 1 includes initially into P. A strictly
-- increasing sequence is a sequence of proper segments; its completion is
-- its limit. Also: an order embedding reaching every point is an
-- equivalence, and ≤ followed by < gives a strict bound, and a proper
-- segment when ≤ is split into < or ≃𝒫.

open import Agda.Primitive using (Level; lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (lower)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Successor as Adjoin
import SPT.Cubical.OrdinalGeometry.Presentation.Limit as Limit
import SPT.Cubical.OrdinalGeometry.Operation.Base as Operation
import SPT.Cubical.OrdinalGeometry.Operation.Normal as Normal

private
  variable
    ℓ : Level
    P Q R S S′ Z : 𝒫 ℓ

------------------------------------------------------------------------
-- Equivalences from surjective embeddings

-- An order embedding that reaches every point up to ≈ is an equivalence.
bijection : (f : Maps.Embedding P Q)
  → ((y : 𝒫.X Q) → Σ (𝒫.X P) (λ x → 𝒫._≈_ Q (Maps.Embedding.map f x) y))
  → P Presented.≃𝒫 Q
bijection f covers = Maps.onto initial covers
  where
  initial : Maps.Initial _ _
  initial = record
    { map = Maps.Embedding.map f ; resp = Maps.Embedding.resp f
    ; strict = Maps.Embedding.strict f ; lower = λ _ y _ → covers y
    }

------------------------------------------------------------------------
-- ≤ followed by <

-- An initial map followed by a proper segment is a strict bound.
strictly : Maps.Initial P Q → Maps.Segment Q R → P Presented.≺𝒫 R
strictly {P = P} {R = R} f s = record
  { to = λ x → Bound.to (F.map x)
  ; to-≈ = λ p → Bound.to-≈ (F.resp p)
  ; to-< = λ p → Bound.to-< (F.strict p)
  ; reflects-< = λ p → F.reflect (Bound.reflects-< p)
  ; ceiling = Bound.ceiling
  ; below = λ x → Bound.below (F.map x)
  }
  where
  module F = Maps.Initial f
  module Bound = Presented._≺𝒫_ (Maps.Segment.bound s)

-- A split ≤, a proper segment or an equivalence, followed by a proper
-- segment is a proper segment.
segment : Maps.Segment P Q ⊎ P Presented.≃𝒫 Q → Maps.Segment Q R
  → Maps.Segment P R
segment (inj₁ s) t = Maps.along s (Maps.inclusion t)
segment (inj₂ e) t = Normal.precompose e t

------------------------------------------------------------------------
-- Zero

-- Mathematical shape: is-zero Z := Π Q. Z ≤ Q.
Zero : 𝒫 ℓ → Set (lsuc ℓ)
Zero {ℓ} Z = (Q : 𝒫 ℓ) → Maps.Initial Z Q

-- A zero has no points, and a presentation without points is a zero.
empty : Zero Z → 𝒫.X Z → ⊥
empty z x = lower (Maps.Initial.map (z Operation.empty) x)

pointless : (𝒫.X Z → ⊥) → Zero Z
pointless none Q = record
  { map = λ x → ⊥-elim (none x)
  ; resp = λ {x} → ⊥-elim (none x)
  ; strict = λ {x} → ⊥-elim (none x)
  ; lower = λ x → ⊥-elim (none x)
  }

-- The empty presentation is a zero.
nothing : Zero (Operation.empty {ℓ})
nothing = Operation.from-empty

module Zeros where

  unique : Zero P → Zero Q → P Presented.≃𝒫 Q
  unique {P = P} {Q = Q} z z′ =
    Maps.antisymmetry (z Q) (z′ P)

------------------------------------------------------------------------
-- Successors

-- Mathematical shape: S is-suc-of P := P < S × Π Q. P < Q → S ≤ Q.
record Successor (P S : 𝒫 ℓ) : Set (lsuc ℓ) where
  field
    above : Maps.Segment P S
    least : (Q : 𝒫 ℓ) → Maps.Segment P Q → Maps.Initial S Q

-- A strong successor: moreover every R < S satisfies R ≤ P.
record Strong (P S : 𝒫 ℓ) : Set (lsuc ℓ) where
  field
    successor : Successor P S
    below : (R : 𝒫 ℓ) → Maps.Segment R S → Maps.Initial R P

module Successors where

  unique : Successor P S → Successor P S′ → S Presented.≃𝒫 S′
  unique {S = S} {S′ = S′} s s′ = Maps.antisymmetry
    (Successor.least s S′ (Successor.above s′))
    (Successor.least s′ S (Successor.above s))

  -- P + 1 is the strong successor of P. A proper segment of P + 1 lands
  -- below its ceiling, hence on old points, and returns to P there.
  next : (P : 𝒫 ℓ) → Strong P (Maps.Successor.next P)
  next {ℓ} P = record
    { successor = record
        { above = Maps.successor P
        ; least = λ _ s → Maps.Segment.closed s
        }
    ; below = below
    }
    where
    module P = 𝒫 P
    module Entry = Presented.Diagonal.Successor
      (Adjoin.constant P) zero

    below : (R : 𝒫 ℓ) → Maps.Segment R (Maps.Successor.next P)
      → Maps.Initial R P
    below R σ = record
      { map = λ r → old (Bound.to r) (Bound.below r)
      ; resp = λ {r} {r′} p →
          old-resp (Bound.below r) (Bound.below r′) (Bound.to-≈ p)
      ; strict = λ {r} {r′} p →
          old-strict (Bound.below r) (Bound.below r′) (Bound.to-< p)
      ; lower = λ r z p →
          let r′ , q = Maps.Segment.covers σ (Entry.point z)
                (Entry.<-trans (raise (Bound.below r) p) (Bound.below r))
          in r′ , old-point (Bound.below r′) q
      }
      where
      module Bound = Presented._≺𝒫_ (Maps.Segment.bound σ)

      c : Entry.Entry
      c = Bound.ceiling

      -- Below the ceiling only old points occur.
      old : (u : Entry.Entry) → u Entry.< c → P.X
      old (Entry.point x) _ = x
      old Entry.top ()

      old-resp : {u v : Entry.Entry} (p : u Entry.< c) (q : v Entry.< c)
        → u Entry.≈ v → old u p P.≈ old v q
      old-resp {Entry.point x} {Entry.point y} _ _ (Entry.point≈ e) = e
      old-resp {Entry.top} () _ _
      old-resp {Entry.point x} {Entry.top} _ () _

      old-strict : {u v : Entry.Entry} (p : u Entry.< c) (q : v Entry.< c)
        → u Entry.< v → old u p P.< old v q
      old-strict {Entry.point x} {Entry.point y} _ _ (Entry.point< e) = e
      old-strict {Entry.top} () _ _
      old-strict {Entry.point x} {Entry.top} _ () _

      raise : {u : Entry.Entry} (p : u Entry.< c) {z : P.X}
        → z P.< old u p → Entry.point z Entry.< u
      raise {Entry.point x} _ q = Entry.point< q
      raise {Entry.top} ()

      old-point : {u : Entry.Entry} (p : u Entry.< c) {z : P.X}
        → u Entry.≈ Entry.point z → old u p P.≈ z
      old-point {Entry.point x} _ (Entry.point≈ e) = e
      old-point {Entry.top} ()

  -- Every successor of P is equivalent to P + 1.
  equivalent : Successor P S → S Presented.≃𝒫 Maps.Successor.next P
  equivalent {P = P} s = unique s (Strong.successor (next P))

------------------------------------------------------------------------
-- Suprema and limits

-- Mathematical shape: S is-sup-of F := (Π n. F n ≤ S)
--   × Π Q. (Π n. F n ≤ Q) → S ≤ Q.
record Supremum (F : ℕ → 𝒫 ℓ) (S : 𝒫 ℓ) : Set (lsuc ℓ) where
  field
    member : (n : ℕ) → Maps.Initial (F n) S
    least : (Q : 𝒫 ℓ) → ((n : ℕ) → Maps.Initial (F n) Q)
      → Maps.Initial S Q

module Suprema where

  unique : {F : ℕ → 𝒫 ℓ} → Supremum F S → Supremum F S′
    → S Presented.≃𝒫 S′
  unique {S = S} {S′ = S′} s s′ = Maps.antisymmetry
    (Supremum.least s S′ (Supremum.member s′))
    (Supremum.least s′ S (Supremum.member s))

  -- The completion of a chain of initial maps is the supremum of its
  -- stages; no compatibility of competing maps is required.
  completion : (C : Limit.Chain ℓ)
    → Supremum (Limit.Chain.stage C) (Limit.completion C)
  completion C = record
    { member = Limit.stage C
    ; least = Limit.least C
    }

-- A strictly increasing sequence: a proper segment from each member to
-- the next. Its limit is the completion of the chain of inclusions.
record Increasing (ℓ : Level) : Set (lsuc ℓ) where
  field
    stage : ℕ → 𝒫 ℓ
    step : (n : ℕ) → Maps.Segment (stage n) (stage (suc n))

  chain : Limit.Chain ℓ
  chain = Limit.principal stage step

  limit : 𝒫 ℓ
  limit = Limit.completion chain

  supremum : Supremum stage limit
  supremum = Suprema.completion chain

  -- Every member lies strictly below the limit.
  strict : (n : ℕ) → Maps.Segment (stage n) limit
  strict = Limit.segment stage step
