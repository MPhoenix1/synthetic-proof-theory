{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Classification.Pointwise where

-- Classification of the ordinals inside an ambient: W is pointwise
-- classified when the domain ∂x of every point x of W is classified.
-- Initial maps carry domains, so pointwise classification passes along
-- equivalences, to the domain of an initial map, and from the stages of a
-- chain to its completion. With the cone lemmas it is closed under the
-- formers: ∅; P + 1, whose top has the domain P; P + Q, where ∂(inr y) ≃
-- P + ∂y; and D · V, where ∂(v, d) ≃ D · ∂v + ∂d. ω is pointwise
-- classified: ∂0 is zero, and ∂(n + 1) is the strong successor of ∂n,
-- since n is the greatest point below n + 1.

open import SPT.Cubical.Base hiding (_+_)
open import SPT.Cubical.Foundation.Nat.Arithmetic using (≤ℕˢ-pred; ≤ℕˢ-split)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Principal as Principal
import SPT.Cubical.OrdinalGeometry.Presentation.Successor as Adjoin
open import SPT.Cubical.OrdinalGeometry.Presentation.Sum using (_+_; ∂)
import SPT.Cubical.OrdinalGeometry.Presentation.Limit as Limit
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization as Normal
import SPT.Cubical.OrdinalGeometry.Operation.Base as Operation
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization using
  (bijection; pointless; Increasing)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Multiplication using
  (_·_; point)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Multiplication as Multiplication
import SPT.Cubical.OrdinalGeometry.Arithmetic.Cone as Cone
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Exponential using (omega)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Classification using
  (Classified; respect; next; sum; product)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Classification as Classification

private
  variable
    ℓ : Level
    P Q : 𝒫 ℓ

-- Mathematical shape: Π x : W. Classified (∂x).
Pointwise : 𝒫 ℓ → Set (lsuc ℓ)
Pointwise W = (x : 𝒫.X W) → Classified (∂ W x)

------------------------------------------------------------------------
-- Domains along initial maps

-- An initial map carries the domain of a point to the domain of its
-- image: the predecessors of f x are images of predecessors of x.
carried : (f : Maps.Initial P Q) (x : 𝒫.X P)
  → ∂ P x Presented.≃𝒫 ∂ Q (Maps.Initial.map f x)
carried {P = P} {Q = Q} f x = bijection embedding covers
  where
  module F = Maps.Initial f

  embedding : Maps.Embedding (∂ P x) (∂ Q (F.map x))
  embedding = record
    { map = λ u → F.map (pr₁ u) , F.strict (pr₂ u)
    ; resp = F.resp
    ; strict = F.strict
    }

  covers : (v : 𝒫.X (∂ Q (F.map x))) → Σ (𝒫.X (∂ P x)) (λ u →
    𝒫._≈_ Q (F.map (pr₁ u)) (pr₁ v))
  covers (z , q) with F.lower x z q
  ... | y , e = (y , F.reflect (𝒫.<-respˡ-≈ Q (𝒫.≈-sym Q e) q)) , e

-- Pointwise classification passes to the domain of an initial map.
pullback : Maps.Initial P Q → Pointwise Q → Pointwise P
pullback f pQ x = respect (Presented.≃𝒫-sym (carried f x))
  (pQ (Maps.Initial.map f x))

-- … and along an equivalence.
transfer : P Presented.≃𝒫 Q → Pointwise P → Pointwise Q
transfer e = pullback (Maps.equivalence (Presented.≃𝒫-sym e))

-- A completion is pointwise classified when its stages are: every point
-- of the completion is the image of a point of a stage.
completion : (C : Limit.Chain ℓ)
  → ((n : ℕ) → Pointwise (Limit.Chain.stage C n))
  → Pointwise (Limit.completion C)
completion C pC y with Limit.coverage C y
... | k , x , p = transport (λ w → Classified (∂ (Limit.completion C) w)) p
  (respect (carried (Limit.stage C k) x) (pC k x))

-- In particular the limit of an increasing sequence.
limit : (s : Increasing ℓ)
  → ((n : ℕ) → Pointwise (Increasing.stage s n))
  → Pointwise (Increasing.limit s)
limit s = completion (Increasing.chain s)

------------------------------------------------------------------------
-- The formers

vacant : Pointwise (Operation.empty {ℓ})
vacant x = 𝟘-elim (lower x)

-- P + 1: an old point keeps its domain, and the top has the domain P.
successor : Classified P → Pointwise P
  → Pointwise (Maps.Successor.next P)
successor {P = P} cP pP (Presented.Diagonal.Successor.point x) =
  respect (Principal.Successor.Below.presentation P x) (pP x)
successor {P = P} cP pP Presented.Diagonal.Successor.top =
  respect (Principal.Successor.Top.presentation P) cP

-- P + Q: below a left point lies its domain in P, below a right point y
-- lies P + ∂y.
plus : Classified P → Pointwise P → Pointwise Q → Pointwise (P + Q)
plus {P = P} {Q = Q} cP pP pQ (inl x) =
  respect (Presented.≃𝒫-sym (Cone.left P Q x)) (pP x)
plus {P = P} {Q = Q} cP pP pQ (inr y) =
  respect (Presented.≃𝒫-sym (Cone.right P Q y)) (sum P (pQ y) (λ _ → cP))

-- D · V: below the point (v, d) lies D · ∂v + ∂d.
times : {D V : 𝒫 ℓ} → Classified D → Pointwise D → Pointwise V
  → Pointwise (D · V)
times {D = D} {V = V} cD pD pV u = at u (Multiplication.view D V u)
  where
  at : (u : 𝒫.X (D · V))
    → Σ (Normal.Point V) (λ v → Σ (Normal.Point D) (λ d →
        u ＝ point D V v d))
    → Classified (∂ (D · V) u)
  at .(point D V v d) (v , d , refl) = respect (Cone.product D V v d)
    (sum (D · Cone.domain V v) (pD (Normal.representative D d))
      (λ _ → product cD (pV (Normal.representative V v))))

------------------------------------------------------------------------
-- ω

-- n is the greatest point below n + 1, so ∂(n + 1) ≃ ∂n + 1.
private
  step : (n : ℕ)
    → Maps.Successor.next (∂ (omega {ℓ}) (lift n))
      Presented.≃𝒫 ∂ omega (lift (suc n))
  step {ℓ} n = bijection embedding covers
    where
    module Entry = Presented.Diagonal.Successor
      (Adjoin.constant (∂ (omega {ℓ}) (lift n))) zero

    map : Entry.Entry → 𝒫.X (∂ omega (lift (suc n)))
    map (Entry.point (m , p)) =
      m , lift (<ℕˢ-trans (lower p) (≤ℕˢ-refl (suc n)))
    map Entry.top = lift n , lift (≤ℕˢ-refl (suc n))

    resp : ∀ {u v} → u Entry.≈ v
      → 𝒫._≈_ (∂ omega (lift (suc n))) (map u) (map v)
    resp (Entry.point≈ e) = e
    resp Entry.top≈ = lift refl

    strict : ∀ {u v} → u Entry.< v
      → 𝒫._<_ (∂ omega (lift (suc n))) (map u) (map v)
    strict (Entry.point< p) = p
    strict (Entry.point<top {x = m , p}) = p

    embedding : Maps.Embedding (Maps.Successor.next (∂ omega (lift n)))
      (∂ omega (lift (suc n)))
    embedding = record
      { map = map
      ; resp = λ {u} {v} → resp {u} {v}
      ; strict = λ {u} {v} → strict {u} {v}
      }

    -- A point below n + 1 lies below n or is n.
    covers : (w : 𝒫.X (∂ omega (lift (suc n))))
      → Σ Entry.Entry (λ u → 𝒫._≈_ (∂ omega (lift (suc n))) (map u) w)
    covers (lift m , lift q)
      with ≤ℕˢ-split m n (≤ℕˢ-pred q)
    ... | inl r = Entry.point (lift m , lift r) , lift refl
    ... | inr refl = Entry.top , lift refl

-- ω is pointwise classified.
naturals : Pointwise (omega {ℓ})
naturals (lift zero) = Classification.zero (pointless λ { (_ , lift ()) })
naturals (lift (suc n)) =
  respect (step n) (next (∂ omega (lift n)))
