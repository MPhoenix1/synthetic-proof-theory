{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Successor where

-- Monotonicity of the successor P ↦ P + 1, row 5 of the KNFX table (Kraus,
-- Nordvall Forsberg and Xu, Lemma 6 and Corollary 40).
-- - P < Q exactly when P + 1 ≤ Q: a proper segment extends to the
--   successor by its ceiling (Maps.Segment.closed), and an initial map of
--   P + 1 is a proper segment of P bounded by the image of the top.
-- - The successor respects ≃𝒫, and it is monotone for strict bounds ≺𝒫,
--   the top going to the ceiling.
-- Over all presentations it is not monotone for ≤ nor for proper
-- segments: each gives LPO (Successor.Discriminator).

open import Agda.Primitive using (Level)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (zero)
open import Data.Product using (Σ; _,_)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Successor as Adjoin
import SPT.Cubical.OrdinalGeometry.Operation.Normal as Normal
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization using
  (Successor; Strong; module Successors)

private
  variable
    ℓ : Level
    P P′ Q S : 𝒫 ℓ

-- A successor of P is a successor of every P′ ≃𝒫 P.
successor-respect : P Presented.≃𝒫 P′ → Successor P S → Successor P′ S
successor-respect e s = record
  { above = Normal.precompose (Presented.≃𝒫-sym e) (Successor.above s)
  ; least = λ Q σ → Successor.least s Q (Normal.precompose e σ)
  }

-- Mathematical shape: P ≃ P′ → P + 1 ≃ P′ + 1.
respect : P Presented.≃𝒫 P′
  → Maps.Successor.next P Presented.≃𝒫 Maps.Successor.next P′
respect {P = P} {P′ = P′} e =
  Successors.unique
    (successor-respect e (Strong.successor (Successors.next P)))
    (Strong.successor (Successors.next P′))

-- Mathematical shape: P + 1 ≤ Q → P < Q, with ceiling the image of the
-- top. With Maps.Segment.closed this is Lemma 6: P < Q ⇔ P + 1 ≤ Q.
segment : Maps.Initial (Maps.Successor.next P) Q → Maps.Segment P Q
segment {P = P} {Q = Q} f = record
  { bound = record
      { to = λ x → F.map (E.point x)
      ; to-≈ = λ p → F.resp (E.point≈ p)
      ; to-< = λ p → F.strict (E.point< p)
      ; reflects-< = λ p → unpoint (F.reflect p)
      ; ceiling = F.map E.top
      ; below = λ x → F.strict (E.point<top {x = x})
      }
  ; covers = λ y p → covered y p (F.lower E.top y p)
  }
  where
  module F = Maps.Initial f
  module E = Presented.Diagonal.Successor
    (Adjoin.constant P) zero

  unpoint : {x y : 𝒫.X P} → E.point x E.< E.point y → 𝒫._<_ P x y
  unpoint (E.point< p) = p

  covered : (y : 𝒫.X Q) → 𝒫._<_ Q y (F.map E.top)
    → Σ E.Entry (λ z → 𝒫._≈_ Q (F.map z) y)
    → Σ (𝒫.X P) (λ x → 𝒫._≈_ Q (F.map (E.point x)) y)
  covered y _ (E.point x , q) = x , q
  covered y p (E.top , q) =
    ⊥-elim (Presented.Presentation.≈↛< Q (𝒫.≈-sym Q q) p)

-- Mathematical shape: P ≺ Q → P + 1 ≺ Q + 1, the top to the ceiling and
-- the new ceiling the top.
bounded : P Presented.≺𝒫 Q
  → Maps.Successor.next P Presented.≺𝒫 Maps.Successor.next Q
bounded {P = P} {Q = Q} b = record
  { to = to
  ; to-≈ = to-≈
  ; to-< = to-<
  ; reflects-< = reflects
  ; ceiling = T.top
  ; below = below
  }
  where
  module B = Presented._≺𝒫_ b
  module E = Presented.Diagonal.Successor
    (Adjoin.constant P) zero
  module T = Presented.Diagonal.Successor
    (Adjoin.constant Q) zero

  to : E.Entry → T.Entry
  to (E.point x) = T.point (B.to x)
  to E.top = T.point B.ceiling

  to-≈ : {x y : E.Entry} → x E.≈ y → to x T.≈ to y
  to-≈ (E.point≈ p) = T.point≈ (B.to-≈ p)
  to-≈ E.top≈ = T.point≈ (𝒫.≈-refl Q B.ceiling)

  to-< : {x y : E.Entry} → x E.< y → to x T.< to y
  to-< (E.point< p) = T.point< (B.to-< p)
  to-< (E.point<top {x = x}) = T.point< (B.below x)

  reflects : {x y : E.Entry} → to x T.< to y → x E.< y
  reflects {E.point x} {E.point y} (T.point< p) = E.point< (B.reflects-< p)
  reflects {E.point x} {E.top} _ = E.point<top
  reflects {E.top} {E.point y} (T.point< p) =
    ⊥-elim (Presented.Presentation.<-asym Q p (B.below y))
  reflects {E.top} {E.top} (T.point< p) =
    ⊥-elim (Presented.Presentation.<-irrefl Q B.ceiling p)

  below : (x : E.Entry) → to x T.< T.top
  below (E.point x) = T.point<top
  below E.top = T.point<top
