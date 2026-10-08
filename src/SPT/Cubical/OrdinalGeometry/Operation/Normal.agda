{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Operation.Normal where

-- Normal operations: operations on initial maps that commute with chain
-- completions and send proper segments to proper segments. At a fixed
-- point Q the proper segment Q ⊂ F(Q+1) gives the seed Q+1 → F(Q+1) for
-- free, so the next fixed point above Q needs no supplied data; it is
-- least among prefixed points with Q as a proper segment. Completions of
-- chains of fixed points are fixed.

open import Agda.Primitive using (Level; lsuc)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Limit as Limit
import SPT.Cubical.OrdinalGeometry.Operation.Base as Operation

private
  variable
    ℓ : Level
    P Q R : 𝒫 ℓ

-- A proper segment precomposed with an equivalence.
precompose : P Presented.≃𝒫 Q → Maps.Segment Q R → Maps.Segment P R
precompose {P = P} {Q = Q} {R = R} e s = record
  { bound = record
      { to = λ x → Bound.to (Iso.to x)
      ; to-≈ = λ p → Bound.to-≈ (Iso.to-≈ p)
      ; to-< = λ p → Bound.to-< (Iso.to-< p)
      ; reflects-< = λ p → back (Bound.reflects-< p)
      ; ceiling = Bound.ceiling
      ; below = λ x → Bound.below (Iso.to x)
      }
  ; covers = λ y p → let x , q = Maps.Segment.covers s y p in
      Iso.from x , 𝒫.≈-trans R (Bound.to-≈ (Iso.to-from-≈ x)) q
  }
  where
  module Iso = Presented._≃𝒫_ e
  module Bound = Presented._≺𝒫_ (Maps.Segment.bound s)

  back : ∀ {x y} → 𝒫._<_ Q (Iso.to x) (Iso.to y) → 𝒫._<_ P x y
  back p = 𝒫.<-respˡ-≈ P (Iso.from-to-≈ _)
    (𝒫.<-respʳ-≈ P (Iso.from-to-≈ _) (Iso.from-< p))

------------------------------------------------------------------------
-- Normal operations

Strict : Operation.Operation ℓ → Set (lsuc ℓ)
Strict {ℓ} F = {P Q : 𝒫 ℓ} → Maps.Segment P Q
  → Maps.Segment (Operation.Operation.apply F P)
      (Operation.Operation.apply F Q)

record Normal (ℓ : Level) : Set (lsuc ℓ) where
  field
    operation : Operation.Operation ℓ
    continuous : Operation.Continuous operation
    segment : Strict operation

  apply : 𝒫 ℓ → 𝒫 ℓ
  apply = Operation.Operation.apply operation

Fixed : Normal ℓ → 𝒫 ℓ → Set ℓ
Fixed N Q = Normal.apply N Q Presented.≃𝒫 Q

sup-fixed : (N : Normal ℓ) (C : Limit.Chain ℓ)
  → ((k : ℕ) → Fixed N (Limit.Chain.stage C k))
  → Fixed N (Limit.completion C)
sup-fixed N C fixed = Presented.≃𝒫-trans
  (Presented.≃𝒫-sym (Normal.continuous N C))
  (Limit.equivalence (Operation.chain (Normal.operation N) C) C fixed)

------------------------------------------------------------------------
-- The next fixed point above a fixed point

seed : (N : Normal ℓ) (Q : 𝒫 ℓ) → Fixed N Q
  → Maps.Initial (Maps.Successor.next Q)
      (Normal.apply N (Maps.Successor.next Q))
seed N Q fixed = Maps.Segment.closed (precompose
  (Presented.≃𝒫-sym fixed) (Normal.segment N (Maps.successor Q)))

next : (N : Normal ℓ) (Q : 𝒫 ℓ) → Fixed N Q → 𝒫 ℓ
next N Q fixed = Operation.boundary (Normal.operation N)
  (Maps.Successor.next Q) (seed N Q fixed)

next-fixed : (N : Normal ℓ) (Q : 𝒫 ℓ) (fixed : Fixed N Q)
  → Fixed N (next N Q fixed)
next-fixed N Q fixed = Operation.fixed (Normal.operation N)
  (Normal.continuous N) (Maps.Successor.next Q) (seed N Q fixed)

next-above : (N : Normal ℓ) (Q : 𝒫 ℓ) (fixed : Fixed N Q)
  → Maps.Segment Q (next N Q fixed)
next-above N Q fixed = Maps.along (Maps.successor Q)
  (Operation.above (Normal.operation N) (Maps.Successor.next Q)
    (seed N Q fixed))

-- Mathematical shape: Q ⊂ Y properly and F(Y) ⊆ Y give next(Q) ⊆ Y.
next-least : (N : Normal ℓ) (Q : 𝒫 ℓ) (fixed : Fixed N Q) (Y : 𝒫 ℓ)
  → Maps.Initial (Normal.apply N Y) Y → Maps.Segment Q Y
  → Maps.Initial (next N Q fixed) Y
next-least N Q fixed Y prefixed s = Operation.least (Normal.operation N)
  (Maps.Successor.next Q) (seed N Q fixed) Y prefixed (Maps.Segment.closed s)

next-respect : (N : Normal ℓ) → Q Presented.≃𝒫 R
  → (fixed : Fixed N Q) (fixed′ : Fixed N R)
  → Maps.Initial (next N Q fixed) (next N R fixed′)
next-respect {R = R} N e fixed fixed′ =
  next-least N _ fixed (next N R fixed′)
    (Maps.equivalence (next-fixed N R fixed′))
    (precompose e (next-above N R fixed′))

next-≃ : (N : Normal ℓ) → Q Presented.≃𝒫 R
  → (fixed : Fixed N Q) (fixed′ : Fixed N R)
  → next N Q fixed Presented.≃𝒫 next N R fixed′
next-≃ N e fixed fixed′ = Maps.antisymmetry
  (next-respect N e fixed fixed′)
  (next-respect N (Presented.≃𝒫-sym e) fixed′ fixed)
