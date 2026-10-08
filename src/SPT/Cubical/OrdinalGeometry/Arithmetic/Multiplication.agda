{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Multiplication where

-- P · Q, the ordered sum of Q copies of P: one block of the normalized
-- points of P at each normalized point of Q, the blocks along Q. It
-- satisfies the multiplication specification of Kraus, Nordvall Forsberg
-- and Xu in its right argument:
--   P · Z ≃ Z               for Z a zero,
--   P · S ≃ P · Q + P       for S a successor of Q,
--   P · A ≃ B               for A the limit of a strictly increasing Qₙ
--                           and B a supremum of the P · Qₙ.
-- P · − acts on initial maps, respects ≃𝒫, and commutes with chain
-- completions. An initial map of exact indices moves constant blocks.

open import Agda.Primitive using (Level; lzero)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; trans)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Successor as Adjoin
open import SPT.Cubical.OrdinalGeometry.Presentation.Sum using (_+_)
import SPT.Cubical.OrdinalGeometry.Presentation.Sum.Indexed as Indexed
import SPT.Cubical.OrdinalGeometry.Presentation.Limit as Limit
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization as Normal
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization.Maps
  as NormalMaps
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization.Presentation
  as Exact
import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order
import SPT.Cubical.OrdinalGeometry.ExactOrder.Maps as Orders
import SPT.Cubical.OrdinalGeometry.ExactOrder.OrderedSum as Index
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization using
  (bijection; Zero; empty; Successor; module Successors; Supremum;
   module Suprema; Increasing)

private
  variable
    ℓ : Level
    Q Q′ S : 𝒫 ℓ

------------------------------------------------------------------------
-- The product

-- The normalized points of Q, as an exact index.
index : 𝒫 ℓ → Index.Ordinal lzero
index Q = Index.ordinal (Normal.Point Q) (Normal.order Q)

-- An initial map of exact indices moves constant blocks along it.
blocks : {A B C : Set} {I : Order.Order A} {J : Order.Order B}
  (K : Order.Order C) → Orders.Initial I J
  → Orders.Initial (Order.Sum.order I (λ _ → K))
      (Order.Sum.order J (λ _ → K))
blocks {A = A} {B} {C} {I} {J} K f = record
  { map = map
  ; strict = strict
  ; lower = lower
  }
  where
  module F = Orders.Initial f
  module Source = Order.Sum I (λ _ → K)
  module Target = Order.Sum J (λ _ → K)

  map : Σ A (λ _ → C) → Σ B (λ _ → C)
  map (i , c) = F.map i , c

  strict : ∀ {x y} → Source._<_ x y → Target._<_ (map x) (map y)
  strict (Source.earlier p) = Target.earlier (F.strict p)
  strict (Source.within i p) = Target.within (F.map i) p

  lower : (x : Σ A (λ _ → C)) (y : Σ B (λ _ → C)) → Target._<_ y (map x)
    → Σ (Σ A (λ _ → C)) (λ z → map z ≡ y)
  lower (i , c) (j , d) (Target.earlier p) with F.lower i j p
  ... | i′ , q = (i′ , d) , cong (_, d) q
  lower (i , c) (.(F.map i) , d) (Target.within .(F.map i) p) =
    (i , d) , refl

infixl 7 _·_

-- The product is sealed, so that comparing products compares their
-- factors rather than unfolding the normalized sum; the theorems below
-- unfold it locally.
opaque
  -- Mathematical shape: P · Q = Σ_{q ∈ Q} P.
  _·_ : 𝒫 ℓ → 𝒫 ℓ → 𝒫 ℓ
  P · Q = Indexed.sum (index Q) (λ _ → P)

  -- The point a in the copy of P at the point q of Q.
  point : (P Q : 𝒫 ℓ) → Normal.Point Q → Normal.Point P → 𝒫.X (P · Q)
  point P Q q a = lift (q , a)

  -- Every point of P · Q is a point of some copy.
  view : (P Q : 𝒫 ℓ) (v : 𝒫.X (P · Q)) → Σ (Normal.Point Q) (λ q →
    Σ (Normal.Point P) (λ a → v ≡ point P Q q a))
  view P Q (lift (q , a)) = q , a , refl

  -- Points of an earlier copy lie below.
  earlier : (P Q : 𝒫 ℓ) {q q′ : Normal.Point Q} (a a′ : Normal.Point P)
    → Normal.Strict Q q q′
    → 𝒫._<_ (P · Q) (point P Q q a) (point P Q q′ a′)
  earlier P Q {q} {q′} a a′ p =
    lift (Blocks.earlier {a = q} {a′ = q′} {x = a} {y = a′} p)
    where
    module Blocks = Order.Sum (Normal.order Q) (λ _ → Normal.order P)

  -- At one position, points compare by their copies.
  reflect : (P Q : 𝒫 ℓ) {q q′ : Normal.Point Q} (a : Normal.Point P)
    → 𝒫._<_ (P · Q) (point P Q q a) (point P Q q′ a)
    → Normal.Strict Q q q′
  reflect P Q a (lift (Order.Sum.earlier p)) = p
  reflect P Q a (lift (Order.Sum.within _ p)) =
    ⊥-elim (Order.Order.irrefl (Normal.order P) a p)

  -- P · − on initial maps.
  initial : (P : 𝒫 ℓ) → Maps.Initial Q Q′ → Maps.Initial (P · Q) (P · Q′)
  initial P f =
    Exact.initial (blocks (Normal.order P) (NormalMaps.initial f))

-- P · − respects equivalence.
equivalence : (P : 𝒫 ℓ) → Q Presented.≃𝒫 Q′
  → (P · Q) Presented.≃𝒫 (P · Q′)
equivalence P e = Maps.antisymmetry (initial P (Maps.equivalence e))
  (initial P (Maps.equivalence (Presented.≃𝒫-sym e)))

------------------------------------------------------------------------
-- Zero and successor

opaque
  unfolding _·_

  -- Mathematical shape: P · Z ≃ Z; neither has a point.
  zero-law : (P Z : 𝒫 ℓ) → Zero Z → (P · Z) Presented.≃𝒫 Z
  zero-law P Z z = Presented.≃𝒫-sym (Maps.onto (z (P · Z)) covers)
    where
    covers : (u : 𝒫.X (P · Z)) → Σ (𝒫.X Z) (λ x →
      𝒫._≈_ (P · Z) (Maps.Initial.map (z (P · Z)) x) u)
    covers (lift (j , a)) = ⊥-elim (empty z (Normal.representative Z j))

  -- Mathematical shape: P · (Q + 1) ≃ P · Q + P. The copies at old points
  -- of Q + 1 form P · Q; the copy at the top is the last P.
  next : (P Q : 𝒫 ℓ)
    → (P · Maps.Successor.next Q) Presented.≃𝒫 ((P · Q) + P)
  next {ℓ} P Q = Presented.≃𝒫-sym (bijection embedding covers)
    where
    N : 𝒫 ℓ
    N = Maps.Successor.next Q

    module Entry = Presented.Diagonal.Successor
      (Adjoin.constant Q) zero
    module Source = Order.Sum (Normal.order Q) (λ _ → Normal.order P)
    module Target = Order.Sum (Normal.order N) (λ _ → Normal.order P)

    up : Normal.Point Q → Normal.Point N
    up q = Normal.class N (Entry.point (Normal.representative Q q))

    peak : Normal.Point N
    peak = Normal.class N Entry.top

    up-strict : ∀ {q q′} → Normal.Strict Q q q′
      → Normal.Strict N (up q) (up q′)
    up-strict {q} {q′} p = Normal.class-strict N
      {x = Entry.point (Normal.representative Q q)}
      {y = Entry.point (Normal.representative Q q′)}
      (Entry.point< (Normal.representative-strict Q {a = q} {b = q′} p))

    up-peak : (q : Normal.Point Q) → Normal.Strict N (up q) peak
    up-peak q = Normal.class-strict N
      {x = Entry.point (Normal.representative Q q)} {y = Entry.top}
      Entry.point<top

    map : 𝒫.X ((P · Q) + P) → 𝒫.X (P · N)
    map (inj₁ (lift (q , a))) = lift (up q , a)
    map (inj₂ x) = lift (peak , Normal.class P x)

    resp : ∀ {u v} → 𝒫._≈_ ((P · Q) + P) u v
      → 𝒫._≈_ (P · N) (map u) (map v)
    resp {inj₁ _} {inj₁ _} (lift e) =
      lift (cong (λ w → up (proj₁ w) , proj₂ w) e)
    resp {inj₁ _} {inj₂ _} ()
    resp {inj₂ _} {inj₁ _} ()
    resp {inj₂ x} {inj₂ y} p = lift (cong (peak ,_) (Normal.class-resp P p))

    strict : ∀ {u v} → 𝒫._<_ ((P · Q) + P) u v
      → 𝒫._<_ (P · N) (map u) (map v)
    strict {inj₁ (lift (q , a))} {inj₁ (lift (q′ , b))}
      (lift (Source.earlier p)) = lift (Target.earlier (up-strict {q} {q′} p))
    strict {inj₁ (lift (q , a))} {inj₁ (lift (.q , b))}
      (lift (Source.within .q p)) = lift (Target.within (up q) p)
    strict {inj₁ (lift (q , a))} {inj₂ x} p = lift (Target.earlier (up-peak q))
    strict {inj₂ _} {inj₁ _} ()
    strict {inj₂ x} {inj₂ y} p =
      lift (Target.within peak (Normal.class-strict P p))

    embedding : Maps.Embedding ((P · Q) + P) (P · N)
    embedding = record
      { map = map
      ; resp = λ {u} {v} → resp {u} {v}
      ; strict = λ {u} {v} → strict {u} {v}
      }

    -- An old point of Q + 1 is the image of its point of Q; the top is the
    -- last copy.
    covers : (y : 𝒫.X (P · N))
      → Σ (𝒫.X ((P · Q) + P)) (λ u → 𝒫._≈_ (P · N) (map u) y)
    covers (lift (j , a))
      with Normal.representative N j | Normal.class-representative N j
    ... | Entry.point y | e = inj₁ (lift (Normal.class Q y , a)) ,
      lift (cong (_, a) (trans
        (Normal.class-resp N (Entry.point≈ (Normal.representative-class Q y)))
        e))
    ... | Entry.top | e = inj₂ (Normal.representative P a) ,
      lift (cong₂ _,_ e (Normal.class-representative P a))

-- Mathematical shape: S is-suc-of Q → P · S ≃ P · Q + P.
successor-law : (P : 𝒫 ℓ) → Successor Q S
  → (P · S) Presented.≃𝒫 ((P · Q) + P)
successor-law {Q = Q} P s =
  Presented.≃𝒫-trans (equivalence P (Successors.equivalent s)) (next P Q)

------------------------------------------------------------------------
-- Limits

-- The chain P · Cₙ, along P · − on the edges.
chain : (P : 𝒫 ℓ) → Limit.Chain ℓ → Limit.Chain ℓ
chain P C = record
  { stage = λ n → P · Limit.Chain.stage C n
  ; edge = λ n → initial P (Limit.Chain.edge C n)
  }

private
  -- A normalized point of a completion comes from one stage.
  reached : (C : Limit.Chain ℓ) (j : Normal.Point (Limit.completion C))
    → Σ ℕ (λ n → Σ (Normal.Point (Limit.Chain.stage C n)) (λ u →
        NormalMaps.map (Limit.stage C n) u ≡ j))
  reached C j
    with Limit.coverage C (Normal.representative (Limit.completion C) j)
  ... | n , x , p = n , Normal.class (Limit.Chain.stage C n) x ,
    trans (NormalMaps.map-β (Limit.stage C n) x)
      (trans (cong (Normal.class (Limit.completion C)) p)
        (Normal.class-representative (Limit.completion C) j))

opaque
  unfolding _·_ initial

  -- Mathematical shape: sup (P · Cₙ) ≃ P · sup Cₙ. A copy at a point of the
  -- completion is the copy at its point in one stage.
  continuous : (P : 𝒫 ℓ) (C : Limit.Chain ℓ)
    → Limit.completion (chain P C) Presented.≃𝒫 (P · Limit.completion C)
  continuous P C = Limit.exhaustion (chain P C) (P · Limit.completion C)
    (λ n → initial P (Limit.stage C n)) covers
    where
    covers : (y : 𝒫.X (P · Limit.completion C))
      → Σ ℕ (λ n → Σ (𝒫.X (P · Limit.Chain.stage C n)) (λ x →
          𝒫._≈_ (P · Limit.completion C)
            (Maps.Initial.map (initial P (Limit.stage C n)) x) y))
    covers (lift (j , a)) with reached C j
    ... | n , u , e = n , lift (u , a) , lift (cong (_, a) e)

-- Mathematical shape: A is-lim-of Qₙ → B is-sup-of (P · Qₙ) → P · A ≃ B.
limit-law : (P : 𝒫 ℓ) (s : Increasing ℓ) {A B : 𝒫 ℓ}
  → Supremum (Increasing.stage s) A
  → Supremum (λ n → P · Increasing.stage s n) B
  → (P · A) Presented.≃𝒫 B
limit-law P s a b = Presented.≃𝒫-trans
  (equivalence P (Suprema.unique a (Increasing.supremum s)))
  (Presented.≃𝒫-trans
    (Presented.≃𝒫-sym (continuous P (Increasing.chain s)))
    (Suprema.unique (Suprema.completion (chain P (Increasing.chain s))) b))
