{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Successor.Discriminator where

-- Monotonicity of the successor for ≤ and for proper segments, asked of
-- all presentations, gives LPO. Kraus, Nordvall Forsberg and Xu have both
-- for Brouwer trees (Corollary 40) and LEM for Ord (Theorem 63); for
-- presentations each decides a Boolean stream s:
-- - ≤: from ∅ ≤ possible s, the point of ∅ + 1 lands on the least point
--   of possible s + 1, a hit of s or the top (initial);
-- - <: from ∅ < 1 + possible s, the ceiling of ∅ + 1 inside
--   (1 + possible s) + 1 is the least point above the first, a hit of s
--   or the top (segment).
-- Monotonicity for ≃𝒫 and for strict bounds ≺𝒫 holds (Successor).

open import Agda.Primitive using (lzero)
open import Data.Bool using (Bool; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; subst)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Successor as Adjoin
open import SPT.Cubical.OrdinalGeometry.Presentation.Sum using (_+_)
import SPT.Cubical.OrdinalGeometry.Operation.Base as Operation
import SPT.Cubical.OrdinalGeometry.Presentation.Limit.Discriminator as Stream
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization using
  (empty) renaming (nothing to vacant)

private
  -- The empty presentation, and its successor's entries.
  ∅ : 𝒫 lzero
  ∅ = Operation.empty

  module Z = Presented.Diagonal.Successor
    (Adjoin.constant ∅) zero

  -- The entries of possible s + 1.
  module Possible (s : ℕ → Bool) = Presented.Diagonal.Successor
    (Adjoin.constant (Stream.possible s)) zero

  -- The entries of (1 + possible s) + 1.
  module Joined (s : ℕ → Bool) = Presented.Diagonal.Successor
    (Adjoin.constant (Stream.one + Stream.possible s))
    zero

  -- The least point of possible s + 1 decides s.
  least-point : (s : ℕ → Bool)
    (m : Maps.Initial (Maps.Successor.next ∅)
      (Maps.Successor.next (Stream.possible s)))
    (u : Possible.Entry s) → Maps.Initial.map m Z.top ≡ u
    → Stream.Hit s ⊎ ((n : ℕ) → s n ≡ false)
  least-point s m (Possible.point h) _ = inj₁ h
  least-point s m Possible.top eq = inj₂ (Stream.absent s clash)
    where
    clash : Stream.Hit s → ⊥
    clash h with Maps.Initial.lower m Z.top (Possible.point h)
      (subst (Possible._<_ s (Possible.point h)) (sym eq)
        Possible.point<top)
    ... | Z.point x , _ = empty vacant x
    ... | Z.top , q = top≉point (subst (λ u → Possible._≈_ s u _) eq q)
      where
      top≉point : Possible._≈_ s Possible.top (Possible.point h)
        → ⊥
      top≉point ()

  -- Nothing lies below the first point of 1 + possible s.
  first-least : (s : ℕ → Bool) (y : 𝒫.X (Stream.one + Stream.possible s))
    → 𝒫._<_ (Stream.one + Stream.possible s) y (inj₁ tt) → ⊥
  first-least s (inj₁ tt) ()
  first-least s (inj₂ h) (lift ())

  -- ∅ < 1 + possible s, with ceiling the first point.
  first : (s : ℕ → Bool) → Maps.Segment ∅ (Stream.one + Stream.possible s)
  first s = record
    { bound = record
        { to = λ x → ⊥-elim (empty vacant x)
        ; to-≈ = λ {x} _ → ⊥-elim (empty vacant x)
        ; to-< = λ {x} _ → ⊥-elim (empty vacant x)
        ; reflects-< = λ {x} _ → ⊥-elim (empty vacant x)
        ; ceiling = inj₁ tt
        ; below = λ x → ⊥-elim (empty vacant x)
        }
    ; covers = λ y p → ⊥-elim (first-least s y p)
    }

  -- The ceiling of ∅ + 1 inside (1 + possible s) + 1 decides s.
  next-point : (s : ℕ → Bool)
    (σ : Maps.Segment (Maps.Successor.next ∅)
      (Maps.Successor.next (Stream.one + Stream.possible s)))
    (c : Joined.Entry s)
    → Presented._≺𝒫_.ceiling (Maps.Segment.bound σ) ≡ c
    → Stream.Hit s ⊎ ((n : ℕ) → s n ≡ false)
  next-point s σ (Joined.point (inj₂ h)) _ = inj₁ h
  next-point s σ (Joined.point (inj₁ tt)) eq =
    ⊥-elim (low (B.to Z.top) (subst (Joined._<_ s (B.to Z.top)) eq
      (B.below Z.top)))
    where
    module B = Presented._≺𝒫_ (Maps.Segment.bound σ)
    low : (u : Joined.Entry s) → Joined._<_ s u (Joined.point (inj₁ tt))
      → ⊥
    low (Joined.point v) (Joined.point< p) = first-least s v p
    low Joined.top ()
  next-point s σ Joined.top eq = inj₂ (Stream.absent s clash)
    where
    module B = Presented._≺𝒫_ (Maps.Segment.bound σ)

    -- Every point below the top comes from the top of ∅ + 1.
    from-top : (y : 𝒫.X (Stream.one + Stream.possible s))
      → Joined._≈_ s (B.to Z.top) (Joined.point y)
    from-top y
      with Maps.Segment.covers σ (Joined.point y)
        (subst (Joined._<_ s (Joined.point y)) (sym eq)
          Joined.point<top)
    ... | Z.point x , _ = ⊥-elim (empty vacant x)
    ... | Z.top , q = q

    clash : Stream.Hit s → ⊥
    clash h with Joined.≈-trans s (Joined.≈-sym s (from-top (inj₁ tt)))
      (from-top (inj₂ h))
    ... | Joined.point≈ (lift ())

-- Mathematical shape: (Π P Q. P ≤ Q → P + 1 ≤ Q + 1) → LPO.
initial : ((P Q : 𝒫 lzero) → Maps.Initial P Q
    → Maps.Initial (Maps.Successor.next P) (Maps.Successor.next Q))
  → Stream.LPO
initial monotone s =
  least-point s m (Maps.Initial.map m Z.top) refl
  where
  m = monotone ∅ (Stream.possible s) (vacant (Stream.possible s))

-- Mathematical shape: (Π P Q. P < Q → P + 1 < Q + 1) → LPO.
segment : ((P Q : 𝒫 lzero) → Maps.Segment P Q
    → Maps.Segment (Maps.Successor.next P) (Maps.Successor.next Q))
  → Stream.LPO
segment monotone s =
  next-point s σ (Presented._≺𝒫_.ceiling (Maps.Segment.bound σ)) refl
  where
  σ = monotone ∅ (Stream.one + Stream.possible s) (first s)
