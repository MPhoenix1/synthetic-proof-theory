{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Addition where

-- The ordered sum P + Q satisfies the addition specification of Kraus,
-- Nordvall Forsberg and Xu in its right argument:
--   P + Z ≃ P               for Z a zero,
--   P + S ≃ D               for S a successor of Q, D one of P + Q,
--   P + A ≃ B               for A the limit of a strictly increasing Qₙ
--                           and B a supremum of the P + Qₙ.
-- P + − acts on initial maps and on proper segments, + respects ≃𝒫 in
-- both arguments, P + (Q + 1) ≃ (P + Q) + 1, and P + − commutes with chain
-- completions. Every law is an equivalence of presentations.

open import SPT.Cubical.Base hiding (_+_; lower)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Successor as Adjoin
open import SPT.Cubical.OrdinalGeometry.Presentation.Sum using (_+_; left)
import SPT.Cubical.OrdinalGeometry.Presentation.Limit as Limit
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization using
  (bijection; Zero; empty; Successor; module Successors; Supremum;
   module Suprema; Increasing)

private
  variable
    ℓ : Level
    P P′ Q Q′ R : 𝒫 ℓ

------------------------------------------------------------------------
-- Actions on maps

-- P + − on an initial map: the left summand stays, the right one moves.
initial : (P : 𝒫 ℓ) → Maps.Initial Q Q′ → Maps.Initial (P + Q) (P + Q′)
initial {Q = Q} {Q′ = Q′} P f = record
  { map = map
  ; resp = λ where
      {inl _} {inl _} p → p
      {inl _} {inr _} ()
      {inr _} {inl _} ()
      {inr _} {inr _} p → F.resp p
  ; strict = λ where
      {inl _} {inl _} p → p
      {inl _} {inr _} p → (lift ⋆)
      {inr _} {inl _} ()
      {inr _} {inr _} p → F.strict p
  ; lower = lower
  }
  where
  module F = Maps.Initial f

  map : 𝒫.X (P + Q) → 𝒫.X (P + Q′)
  map (inl x) = inl x
  map (inr y) = inr (F.map y)

  lower : (u : 𝒫.X (P + Q)) (z : 𝒫.X (P + Q′)) → 𝒫._<_ (P + Q′) z (map u)
    → Σ (𝒫.X (P + Q)) (λ v → 𝒫._≈_ (P + Q′) (map v) z)
  lower (inl x) (inl y) p = inl y , 𝒫.≈-refl P y
  lower (inl x) (inr y) ()
  lower (inr y) (inl x) p = inl x , 𝒫.≈-refl P x
  lower (inr y) (inr w) p with F.lower y w p
  ... | v , q = inr v , q

-- P + − on a proper segment, with ceiling the image of the old ceiling.
segment : (P : 𝒫 ℓ) → Maps.Segment Q Q′ → Maps.Segment (P + Q) (P + Q′)
segment {Q = Q} {Q′ = Q′} P s = record
  { bound = record
      { to = to
      ; to-≈ = λ where
          {inl _} {inl _} p → p
          {inl _} {inr _} ()
          {inr _} {inl _} ()
          {inr _} {inr _} p → Bound.to-≈ p
      ; to-< = λ where
          {inl _} {inl _} p → p
          {inl _} {inr _} p → (lift ⋆)
          {inr _} {inl _} ()
          {inr _} {inr _} p → Bound.to-< p
      ; reflects-< = λ where
          {inl _} {inl _} p → p
          {inl _} {inr _} p → (lift ⋆)
          {inr _} {inl _} ()
          {inr _} {inr _} p → Bound.reflects-< p
      ; ceiling = inr Bound.ceiling
      ; below = λ where
          (inl x) → (lift ⋆)
          (inr y) → Bound.below y
      }
  ; covers = covers
  }
  where
  module Bound = Presented._≺𝒫_ (Maps.Segment.bound s)

  to : 𝒫.X (P + Q) → 𝒫.X (P + Q′)
  to (inl x) = inl x
  to (inr y) = inr (Bound.to y)

  covers : (z : 𝒫.X (P + Q′)) → 𝒫._<_ (P + Q′) z (inr Bound.ceiling)
    → Σ (𝒫.X (P + Q)) (λ u → 𝒫._≈_ (P + Q′) (to u) z)
  covers (inl x) p = inl x , 𝒫.≈-refl P x
  covers (inr w) p with Maps.Segment.covers s w p
  ... | v , q = inr v , q

-- The sum respects equivalence in both arguments.
equivalence : P Presented.≃𝒫 P′ → Q Presented.≃𝒫 Q′
  → (P + Q) Presented.≃𝒫 (P′ + Q′)
equivalence {P = P} {P′ = P′} {Q = Q} {Q′ = Q′} e e′ = record
  { to = to
  ; from = from
  ; to-≈ = λ where
      {inl _} {inl _} p → E.to-≈ p
      {inl _} {inr _} ()
      {inr _} {inl _} ()
      {inr _} {inr _} p → E′.to-≈ p
  ; from-≈ = λ where
      {inl _} {inl _} p → E.from-≈ p
      {inl _} {inr _} ()
      {inr _} {inl _} ()
      {inr _} {inr _} p → E′.from-≈ p
  ; to-< = λ where
      {inl _} {inl _} p → E.to-< p
      {inl _} {inr _} p → (lift ⋆)
      {inr _} {inl _} ()
      {inr _} {inr _} p → E′.to-< p
  ; from-< = λ where
      {inl _} {inl _} p → E.from-< p
      {inl _} {inr _} p → (lift ⋆)
      {inr _} {inl _} ()
      {inr _} {inr _} p → E′.from-< p
  ; from-to-≈ = λ where
      (inl x) → E.from-to-≈ x
      (inr y) → E′.from-to-≈ y
  ; to-from-≈ = λ where
      (inl x) → E.to-from-≈ x
      (inr y) → E′.to-from-≈ y
  }
  where
  module E = Presented._≃𝒫_ e
  module E′ = Presented._≃𝒫_ e′

  to : 𝒫.X (P + Q) → 𝒫.X (P′ + Q′)
  to (inl x) = inl (E.to x)
  to (inr y) = inr (E′.to y)

  from : 𝒫.X (P′ + Q′) → 𝒫.X (P + Q)
  from (inl x) = inl (E.from x)
  from (inr y) = inr (E′.from y)

------------------------------------------------------------------------
-- Zero and successor

-- Mathematical shape: P + Z ≃ P. Every point of P + Z is a left point.
zero-law : (Z : 𝒫 ℓ) → Zero Z → (P + Z) Presented.≃𝒫 P
zero-law {P = P} Z z = Presented.≃𝒫-sym
  (bijection (Maps.Initial.embedding (left P Z)) covers)
  where
  covers : (u : 𝒫.X (P + Z))
    → Σ (𝒫.X P) (λ x → 𝒫._≈_ (P + Z) (inl x) u)
  covers (inl x) = x , 𝒫.≈-refl P x
  covers (inr y) = 𝟘-elim (empty z y)

-- Mathematical shape: P + (Q + 1) ≃ (P + Q) + 1, the new top to the top.
next : (P Q : 𝒫 ℓ)
  → (P + Maps.Successor.next Q) Presented.≃𝒫 Maps.Successor.next (P + Q)
next P Q = record
  { to = to
  ; from = from
  ; to-≈ = λ where
      {inl _} {inl _} p → Outer.point≈ p
      {inl _} {inr _} ()
      {inr _} {inl _} ()
      {inr (Inner.point _)} {inr (Inner.point _)} (Inner.point≈ p) →
        Outer.point≈ p
      {inr Inner.top} {inr Inner.top} Inner.top≈ → Outer.top≈
  ; from-≈ = λ where
      {Outer.point (inl _)} {Outer.point (inl _)} (Outer.point≈ p) → p
      {Outer.point (inr _)} {Outer.point (inr _)} (Outer.point≈ p) →
        Inner.point≈ p
      {Outer.top} {Outer.top} Outer.top≈ → Inner.top≈
  ; to-< = λ where
      {inl _} {inl _} p → Outer.point< p
      {inl _} {inr (Inner.point _)} p → Outer.point< (lift ⋆)
      {inl _} {inr Inner.top} p → Outer.point<top
      {inr _} {inl _} ()
      {inr (Inner.point _)} {inr (Inner.point _)} (Inner.point< p) →
        Outer.point< p
      {inr (Inner.point _)} {inr Inner.top} Inner.point<top →
        Outer.point<top
  ; from-< = λ where
      {Outer.point (inl _)} {Outer.point (inl _)} (Outer.point< p) → p
      {Outer.point (inl _)} {Outer.point (inr _)} (Outer.point< p) → (lift ⋆)
      {Outer.point (inr _)} {Outer.point (inr _)} (Outer.point< p) →
        Inner.point< p
      {Outer.point (inl _)} {Outer.top} Outer.point<top → (lift ⋆)
      {Outer.point (inr _)} {Outer.top} Outer.point<top → Inner.point<top
  ; from-to-≈ = λ where
      (inl x) → 𝒫.≈-refl P x
      (inr (Inner.point y)) → Inner.point≈ (𝒫.≈-refl Q y)
      (inr Inner.top) → Inner.top≈
  ; to-from-≈ = λ where
      (Outer.point (inl x)) → Outer.point≈ (𝒫.≈-refl P x)
      (Outer.point (inr y)) → Outer.point≈ (𝒫.≈-refl Q y)
      Outer.top → Outer.top≈
  }
  where
  module Inner = Presented.Diagonal.Successor
    (Adjoin.constant Q) zero
  module Outer = Presented.Diagonal.Successor
    (Adjoin.constant (P + Q)) zero

  to : 𝒫.X (P + Maps.Successor.next Q) → 𝒫.X (Maps.Successor.next (P + Q))
  to (inl x) = Outer.point (inl x)
  to (inr (Inner.point y)) = Outer.point (inr y)
  to (inr Inner.top) = Outer.top

  from : 𝒫.X (Maps.Successor.next (P + Q)) → 𝒫.X (P + Maps.Successor.next Q)
  from (Outer.point (inl x)) = inl x
  from (Outer.point (inr y)) = inr (Inner.point y)
  from Outer.top = inr Inner.top

-- Mathematical shape: S is-suc-of Q → D is-suc-of (P + Q) → P + S ≃ D.
successor-law : Successor Q R → {D : 𝒫 ℓ} → Successor (P + Q) D
  → (P + R) Presented.≃𝒫 D
successor-law {Q = Q} {P = P} s d = Presented.≃𝒫-trans
  (equivalence (Presented.≃𝒫-refl P) (Successors.equivalent s))
  (Presented.≃𝒫-trans (next P Q) (Presented.≃𝒫-sym
    (Successors.equivalent d)))

------------------------------------------------------------------------
-- Limits

-- The chain P + Cₙ, along P + − on the edges.
chain : (P : 𝒫 ℓ) → Limit.Chain ℓ → Limit.Chain ℓ
chain P C = record
  { stage = λ n → P + Limit.Chain.stage C n
  ; edge = λ n → initial P (Limit.Chain.edge C n)
  }

-- Mathematical shape: sup (P + Cₙ) ≃ P + sup Cₙ. A left point enters at
-- stage 0; a right point at the stage where the completion covers it.
continuous : (P : 𝒫 ℓ) (C : Limit.Chain ℓ)
  → Limit.completion (chain P C) Presented.≃𝒫 (P + Limit.completion C)
continuous P C = Limit.exhaustion (chain P C) (P + Limit.completion C)
  (λ n → initial P (Limit.stage C n)) covers
  where
  covers : (y : 𝒫.X (P + Limit.completion C))
    → Σ ℕ (λ n → Σ (𝒫.X (P + Limit.Chain.stage C n)) (λ x →
        𝒫._≈_ (P + Limit.completion C)
          (Maps.Initial.map (initial P (Limit.stage C n)) x) y))
  covers (inl x) = zero , inl x , 𝒫.≈-refl P x
  covers (inr y) with Limit.coverage C y
  ... | n , x , p = n , inr x ,
    transport (𝒫._≈_ (Limit.completion C) _) p
      (𝒫.≈-refl (Limit.completion C) _)

-- Mathematical shape: A is-lim-of Qₙ → B is-sup-of (P + Qₙ) → P + A ≃ B.
limit-law : (s : Increasing ℓ) {A B : 𝒫 ℓ}
  → Supremum (Increasing.stage s) A
  → Supremum (λ n → P + Increasing.stage s n) B
  → (P + A) Presented.≃𝒫 B
limit-law {P = P} s a b = Presented.≃𝒫-trans
  (equivalence (Presented.≃𝒫-refl P)
    (Suprema.unique a (Increasing.supremum s)))
  (Presented.≃𝒫-trans
    (Presented.≃𝒫-sym (continuous P (Increasing.chain s)))
    (Suprema.unique (Suprema.completion (chain P (Increasing.chain s))) b))
