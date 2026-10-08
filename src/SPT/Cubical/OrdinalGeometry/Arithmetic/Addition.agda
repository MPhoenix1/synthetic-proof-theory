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

open import Agda.Primitive using (Level)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (tt)
open import Relation.Binary.PropositionalEquality using (subst)

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
      {inj₁ _} {inj₁ _} p → p
      {inj₁ _} {inj₂ _} ()
      {inj₂ _} {inj₁ _} ()
      {inj₂ _} {inj₂ _} p → F.resp p
  ; strict = λ where
      {inj₁ _} {inj₁ _} p → p
      {inj₁ _} {inj₂ _} p → tt
      {inj₂ _} {inj₁ _} ()
      {inj₂ _} {inj₂ _} p → F.strict p
  ; lower = lower
  }
  where
  module F = Maps.Initial f

  map : 𝒫.X (P + Q) → 𝒫.X (P + Q′)
  map (inj₁ x) = inj₁ x
  map (inj₂ y) = inj₂ (F.map y)

  lower : (u : 𝒫.X (P + Q)) (z : 𝒫.X (P + Q′)) → 𝒫._<_ (P + Q′) z (map u)
    → Σ (𝒫.X (P + Q)) (λ v → 𝒫._≈_ (P + Q′) (map v) z)
  lower (inj₁ x) (inj₁ y) p = inj₁ y , 𝒫.≈-refl P y
  lower (inj₁ x) (inj₂ y) ()
  lower (inj₂ y) (inj₁ x) p = inj₁ x , 𝒫.≈-refl P x
  lower (inj₂ y) (inj₂ w) p with F.lower y w p
  ... | v , q = inj₂ v , q

-- P + − on a proper segment, with ceiling the image of the old ceiling.
segment : (P : 𝒫 ℓ) → Maps.Segment Q Q′ → Maps.Segment (P + Q) (P + Q′)
segment {Q = Q} {Q′ = Q′} P s = record
  { bound = record
      { to = to
      ; to-≈ = λ where
          {inj₁ _} {inj₁ _} p → p
          {inj₁ _} {inj₂ _} ()
          {inj₂ _} {inj₁ _} ()
          {inj₂ _} {inj₂ _} p → Bound.to-≈ p
      ; to-< = λ where
          {inj₁ _} {inj₁ _} p → p
          {inj₁ _} {inj₂ _} p → tt
          {inj₂ _} {inj₁ _} ()
          {inj₂ _} {inj₂ _} p → Bound.to-< p
      ; reflects-< = λ where
          {inj₁ _} {inj₁ _} p → p
          {inj₁ _} {inj₂ _} p → tt
          {inj₂ _} {inj₁ _} ()
          {inj₂ _} {inj₂ _} p → Bound.reflects-< p
      ; ceiling = inj₂ Bound.ceiling
      ; below = λ where
          (inj₁ x) → tt
          (inj₂ y) → Bound.below y
      }
  ; covers = covers
  }
  where
  module Bound = Presented._≺𝒫_ (Maps.Segment.bound s)

  to : 𝒫.X (P + Q) → 𝒫.X (P + Q′)
  to (inj₁ x) = inj₁ x
  to (inj₂ y) = inj₂ (Bound.to y)

  covers : (z : 𝒫.X (P + Q′)) → 𝒫._<_ (P + Q′) z (inj₂ Bound.ceiling)
    → Σ (𝒫.X (P + Q)) (λ u → 𝒫._≈_ (P + Q′) (to u) z)
  covers (inj₁ x) p = inj₁ x , 𝒫.≈-refl P x
  covers (inj₂ w) p with Maps.Segment.covers s w p
  ... | v , q = inj₂ v , q

-- The sum respects equivalence in both arguments.
equivalence : P Presented.≃𝒫 P′ → Q Presented.≃𝒫 Q′
  → (P + Q) Presented.≃𝒫 (P′ + Q′)
equivalence {P = P} {P′ = P′} {Q = Q} {Q′ = Q′} e e′ = record
  { to = to
  ; from = from
  ; to-≈ = λ where
      {inj₁ _} {inj₁ _} p → E.to-≈ p
      {inj₁ _} {inj₂ _} ()
      {inj₂ _} {inj₁ _} ()
      {inj₂ _} {inj₂ _} p → E′.to-≈ p
  ; from-≈ = λ where
      {inj₁ _} {inj₁ _} p → E.from-≈ p
      {inj₁ _} {inj₂ _} ()
      {inj₂ _} {inj₁ _} ()
      {inj₂ _} {inj₂ _} p → E′.from-≈ p
  ; to-< = λ where
      {inj₁ _} {inj₁ _} p → E.to-< p
      {inj₁ _} {inj₂ _} p → tt
      {inj₂ _} {inj₁ _} ()
      {inj₂ _} {inj₂ _} p → E′.to-< p
  ; from-< = λ where
      {inj₁ _} {inj₁ _} p → E.from-< p
      {inj₁ _} {inj₂ _} p → tt
      {inj₂ _} {inj₁ _} ()
      {inj₂ _} {inj₂ _} p → E′.from-< p
  ; from-to-≈ = λ where
      (inj₁ x) → E.from-to-≈ x
      (inj₂ y) → E′.from-to-≈ y
  ; to-from-≈ = λ where
      (inj₁ x) → E.to-from-≈ x
      (inj₂ y) → E′.to-from-≈ y
  }
  where
  module E = Presented._≃𝒫_ e
  module E′ = Presented._≃𝒫_ e′

  to : 𝒫.X (P + Q) → 𝒫.X (P′ + Q′)
  to (inj₁ x) = inj₁ (E.to x)
  to (inj₂ y) = inj₂ (E′.to y)

  from : 𝒫.X (P′ + Q′) → 𝒫.X (P + Q)
  from (inj₁ x) = inj₁ (E.from x)
  from (inj₂ y) = inj₂ (E′.from y)

------------------------------------------------------------------------
-- Zero and successor

-- Mathematical shape: P + Z ≃ P. Every point of P + Z is a left point.
zero-law : (Z : 𝒫 ℓ) → Zero Z → (P + Z) Presented.≃𝒫 P
zero-law {P = P} Z z = Presented.≃𝒫-sym
  (bijection (Maps.Initial.embedding (left P Z)) covers)
  where
  covers : (u : 𝒫.X (P + Z))
    → Σ (𝒫.X P) (λ x → 𝒫._≈_ (P + Z) (inj₁ x) u)
  covers (inj₁ x) = x , 𝒫.≈-refl P x
  covers (inj₂ y) = ⊥-elim (empty z y)

-- Mathematical shape: P + (Q + 1) ≃ (P + Q) + 1, the new top to the top.
next : (P Q : 𝒫 ℓ)
  → (P + Maps.Successor.next Q) Presented.≃𝒫 Maps.Successor.next (P + Q)
next P Q = record
  { to = to
  ; from = from
  ; to-≈ = λ where
      {inj₁ _} {inj₁ _} p → Outer.point≈ p
      {inj₁ _} {inj₂ _} ()
      {inj₂ _} {inj₁ _} ()
      {inj₂ (Inner.point _)} {inj₂ (Inner.point _)} (Inner.point≈ p) →
        Outer.point≈ p
      {inj₂ Inner.top} {inj₂ Inner.top} Inner.top≈ → Outer.top≈
  ; from-≈ = λ where
      {Outer.point (inj₁ _)} {Outer.point (inj₁ _)} (Outer.point≈ p) → p
      {Outer.point (inj₂ _)} {Outer.point (inj₂ _)} (Outer.point≈ p) →
        Inner.point≈ p
      {Outer.top} {Outer.top} Outer.top≈ → Inner.top≈
  ; to-< = λ where
      {inj₁ _} {inj₁ _} p → Outer.point< p
      {inj₁ _} {inj₂ (Inner.point _)} p → Outer.point< tt
      {inj₁ _} {inj₂ Inner.top} p → Outer.point<top
      {inj₂ _} {inj₁ _} ()
      {inj₂ (Inner.point _)} {inj₂ (Inner.point _)} (Inner.point< p) →
        Outer.point< p
      {inj₂ (Inner.point _)} {inj₂ Inner.top} Inner.point<top →
        Outer.point<top
  ; from-< = λ where
      {Outer.point (inj₁ _)} {Outer.point (inj₁ _)} (Outer.point< p) → p
      {Outer.point (inj₁ _)} {Outer.point (inj₂ _)} (Outer.point< p) → tt
      {Outer.point (inj₂ _)} {Outer.point (inj₂ _)} (Outer.point< p) →
        Inner.point< p
      {Outer.point (inj₁ _)} {Outer.top} Outer.point<top → tt
      {Outer.point (inj₂ _)} {Outer.top} Outer.point<top → Inner.point<top
  ; from-to-≈ = λ where
      (inj₁ x) → 𝒫.≈-refl P x
      (inj₂ (Inner.point y)) → Inner.point≈ (𝒫.≈-refl Q y)
      (inj₂ Inner.top) → Inner.top≈
  ; to-from-≈ = λ where
      (Outer.point (inj₁ x)) → Outer.point≈ (𝒫.≈-refl P x)
      (Outer.point (inj₂ y)) → Outer.point≈ (𝒫.≈-refl Q y)
      Outer.top → Outer.top≈
  }
  where
  module Inner = Presented.Diagonal.Successor
    (Adjoin.constant Q) zero
  module Outer = Presented.Diagonal.Successor
    (Adjoin.constant (P + Q)) zero

  to : 𝒫.X (P + Maps.Successor.next Q) → 𝒫.X (Maps.Successor.next (P + Q))
  to (inj₁ x) = Outer.point (inj₁ x)
  to (inj₂ (Inner.point y)) = Outer.point (inj₂ y)
  to (inj₂ Inner.top) = Outer.top

  from : 𝒫.X (Maps.Successor.next (P + Q)) → 𝒫.X (P + Maps.Successor.next Q)
  from (Outer.point (inj₁ x)) = inj₁ x
  from (Outer.point (inj₂ y)) = inj₂ (Inner.point y)
  from Outer.top = inj₂ Inner.top

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
  covers (inj₁ x) = zero , inj₁ x , 𝒫.≈-refl P x
  covers (inj₂ y) with Limit.coverage C y
  ... | n , x , p = n , inj₂ x ,
    subst (𝒫._≈_ (Limit.completion C) _) p
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
