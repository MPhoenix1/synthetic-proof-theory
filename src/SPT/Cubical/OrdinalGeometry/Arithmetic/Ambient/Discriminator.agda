{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Ambient.Discriminator where

-- Comparison of presentations without a common ambient. Inside an ambient
-- W, comparison of points gives the domains of points joins, splittings
-- and decisions (Ambient). Asked of all presentations instead, each of
-- these decides an arbitrary Boolean stream s, through possible s, which
-- has a point exactly when s hits true:
--   row 2, ≤ followed by < is <: possible s ≤ 1 < 2 (along);
--   rows 6 and 8, binary joins and suprema of sequences: even a common
--     initial bound of possible s + 1 and 1 decides s (join, supremum);
--   row 15, P < ω decidable: the prefix of ω before the first hit of s is
--     finite exactly when s hits (finite);
--   row 16, P < Q decidable: 1 < possible s + 1 exactly when s hits
--     (decidable);
--   row 17, ≤ splits into < or ≃: possible s ≤ 1 (split);
--   row 18, trichotomy: possible s against 1 (trichotomy).
-- Each gives LPO. So the ambient is the datum these rows use: comparison
-- of points of one W, not of arbitrary presentations.

open import Agda.Primitive using (lzero)
open import Data.Bool using (Bool; false; true; not; _∧_)
open import Data.Bool.Properties using (∧-zeroʳ; ∧-identityʳ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat as Nat
import Data.Nat.Properties as NatProperties
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Level using (lift; lower)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; sym; trans; subst)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Limit.Discriminator as Stream
open Stream using (two; bottom)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization using
  (Supremum)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Ambient using (pair)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Exponential using (omega)

private
  -- The entries of a successor presentation: old points and the top.
  module Entry = Presented.Diagonal.Successor

  -- A proper segment of 2 decides possible s by its ceiling: the top has
  -- a point below it, the old point has none.
  ceiling : (s : ℕ → Bool) → Maps.Segment (Stream.possible s) two
    → Stream.Hit s ⊎ ((n : ℕ) → s n ≡ false)
  ceiling s σ = at B.ceiling B.below (Maps.Segment.covers σ)
    where
    module B = Presented._≺𝒫_ (Maps.Segment.bound σ)

    at : (c : 𝒫.X two) → ((h : Stream.Hit s) → 𝒫._<_ two (B.to h) c)
      → ((y : 𝒫.X two) → 𝒫._<_ two y c
          → Σ (Stream.Hit s) (λ h → 𝒫._≈_ two (B.to h) y))
      → Stream.Hit s ⊎ ((n : ℕ) → s n ≡ false)
    at Entry.top _ covers =
      inj₁ (proj₁ (covers (Entry.point tt) Entry.point<top))
    at (Entry.point _) below _ = inj₂ (Stream.absent s λ h → bottom (below h))

------------------------------------------------------------------------
-- Row 2

-- Mathematical shape: (Π P Q R. P ≤ Q → Q < R → P < R) → LPO.
along : ((P Q R : 𝒫 lzero) → Maps.Initial P Q → Maps.Segment Q R
    → Maps.Segment P R)
  → Stream.LPO
along transitive s = ceiling s (transitive (Stream.possible s) Stream.one
  two (Stream.inclusion s) (Maps.successor Stream.one))

------------------------------------------------------------------------
-- Rows 6 and 8

private
  -- Nothing lies below the image of the point of 1 under an initial map.
  least : {Q : 𝒫 lzero} (g : Maps.Initial Stream.one Q) (y : 𝒫.X Q)
    → 𝒫._<_ Q y (Maps.Initial.map g tt) → ⊥
  least {Q} g y p with Maps.Initial.lower g tt y p
  ... | tt , q = Presented.Presentation.≈↛< Q (𝒫.≈-sym Q q) p

-- A common initial bound Q of possible s + 1 and 1 decides s: the top of
-- possible s + 1 lands on the point of 1 exactly when s never hits, and
-- above it exactly when an old point of possible s lies below.
common : (s : ℕ → Bool) (Q : 𝒫 lzero)
  → Maps.Initial (Maps.Successor.next (Stream.possible s)) Q
  → Maps.Initial Stream.one Q
  → Stream.Hit s ⊎ ((n : ℕ) → s n ≡ false)
common s Q f g
  with 𝒫.compare Q (Maps.Initial.map f Entry.top) (Maps.Initial.map g tt)
... | inj₁ p = ⊥-elim (least g _ p)
... | inj₂ (inj₁ q) = inj₂ (Stream.absent s λ h → least g _
  (𝒫.<-respʳ-≈ Q q
    (Maps.Initial.strict f {x = Entry.point h} Entry.point<top)))
... | inj₂ (inj₂ p)
  with Maps.Initial.lower f Entry.top (Maps.Initial.map g tt) p
...   | Entry.point h , _ = inj₁ h
...   | Entry.top , q =
  ⊥-elim (Presented.Presentation.≈↛< Q (𝒫.≈-sym Q q) p)

-- The family (possible s + 1, 1, 1, …): a common initial bound of its
-- members decides s.
family : (ℕ → Bool) → ℕ → 𝒫 lzero
family s = pair (Maps.Successor.next (Stream.possible s)) Stream.one

-- Mathematical shape: (Π P Q. Σ S. S is-sup-of (P, Q, Q, …)) → LPO.
join : ((P Q : 𝒫 lzero) → Σ (𝒫 lzero) (Supremum (pair P Q)))
  → Stream.LPO
join sup s = common s (proj₁ σ) (Supremum.member (proj₂ σ) zero)
  (Supremum.member (proj₂ σ) (suc zero))
  where
  σ : Σ (𝒫 lzero) (Supremum (family s))
  σ = sup (Maps.Successor.next (Stream.possible s)) Stream.one

-- Mathematical shape: (Π F : ℕ → 𝒫. Σ S. S is-sup-of F) → LPO.
supremum : ((F : ℕ → 𝒫 lzero) → Σ (𝒫 lzero) (Supremum F)) → Stream.LPO
supremum sup = join (λ P Q → sup (pair P Q))

------------------------------------------------------------------------
-- Row 15

private
  module Prefix (s : ℕ → Bool) where

    -- clear n: s is false at every m ≤ n.
    clear : ℕ → Bool
    clear zero = not (s zero)
    clear (suc n) = clear n ∧ not (s (suc n))

    conjunct : (a b : Bool) → a ∧ b ≡ true → a ≡ true
    conjunct true _ _ = refl

    clash : {b : Bool} → b ≡ true → b ≡ false → ⊥
    clash refl ()

    closed : (n : ℕ) → clear n ≡ true → (m : ℕ) → m Nat.≤ n
      → clear m ≡ true
    closed zero p .zero Nat.z≤n = p
    closed (suc n) p m q with NatProperties.m≤n⇒m<n∨m≡n q
    ... | inj₂ refl = p
    ... | inj₁ r = closed n (conjunct (clear n) _ p) m (NatProperties.≤-pred r)

    stop : (n : ℕ) → s n ≡ true → clear n ≡ false
    stop zero p = cong not p
    stop (suc n) p = trans (cong (λ b → clear n ∧ not b) p) (∧-zeroʳ (clear n))

    hit : (n : ℕ) → clear n ≡ false → Stream.Hit s
    hit zero p = zero , flip (s zero) p
      where
      flip : (b : Bool) → not b ≡ false → b ≡ true
      flip true _ = refl
    hit (suc n) p = step (s (suc n)) refl p
      where
      step : (b : Bool) → s (suc n) ≡ b → clear n ∧ not b ≡ false
        → Stream.Hit s
      step true q _ = suc n , q
      step false _ r = hit n (trans (sym (∧-identityʳ (clear n))) r)

    -- The first k at which clear fails: the first hit of s.
    first : (n : ℕ) → clear n ≡ false → Σ ℕ (λ k →
      Σ (clear k ≡ false) (λ _ → (m : ℕ) → m Nat.< k → clear m ≡ true))
    first zero p = zero , p , λ _ ()
    first (suc n) p = step (clear n) refl
      where
      step : (b : Bool) → clear n ≡ b → Σ ℕ (λ k →
        Σ (clear k ≡ false) (λ _ → (m : ℕ) → m Nat.< k → clear m ≡ true))
      step true q = suc n , p , λ m r → closed n q m (NatProperties.≤-pred r)
      step false q = first n q

    -- Mathematical shape: {n ∈ ω | s is false up to n}, ordered as in ω.
    prefix : 𝒫 lzero
    prefix = Stream.hits clear

    -- The prefix is an initial segment of ω.
    initial : Maps.Initial prefix omega
    initial = record
      { map = λ u → lift (proj₁ u)
      ; resp = lift
      ; strict = lift
      ; lower = λ u y p →
          (lower y , closed (proj₁ u) (proj₂ u) (lower y)
            (NatProperties.<⇒≤ (lower p))) , lift refl
      }

    -- A proper segment of ω containing the prefix has its ceiling at a
    -- hit: its map is the initial map above, so the prefix stays below.
    bounded : Maps.Segment prefix omega → Stream.Hit s
    bounded σ = at (clear k) refl
      where
      module B = Presented._≺𝒫_ (Maps.Segment.bound σ)

      k : ℕ
      k = lower B.ceiling

      under : (u : 𝒫.X prefix) → proj₁ u Nat.< k
      under u = subst (λ m → m Nat.< k)
        (lower (Maps.Uniqueness.pointwise (Maps.inclusion σ) initial u))
        (lower (B.below u))

      at : (b : Bool) → clear k ≡ b → Stream.Hit s
      at true q = ⊥-elim (NatProperties.<-irrefl refl (under (k , q)))
      at false q = hit k q

    -- After a hit, the prefix is the proper segment of ω below the first
    -- hit.
    segment : Stream.Hit s → Maps.Segment prefix omega
    segment (n , p) with first n (stop n p)
    ... | k , q , before = record
      { bound = record
          { to = λ u → lift (proj₁ u)
          ; to-≈ = lift
          ; to-< = lift
          ; reflects-< = lower
          ; ceiling = lift k
          ; below = λ u → lift (NatProperties.≰⇒> λ r →
              clash (closed (proj₁ u) (proj₂ u) k r) q)
          }
      ; covers = λ y r → (lower y , before (lower y) (lower r)) , lift refl
      }

-- Mathematical shape: (Π P. Dec (P < ω)) → LPO.
finite : ((P : 𝒫 lzero) → Dec (Maps.Segment P omega)) → Stream.LPO
finite decide s with decide (Prefix.prefix s)
... | yes σ = inj₁ (Prefix.bounded s σ)
... | no none = inj₂ (Stream.absent s λ h → none (Prefix.segment s h))

------------------------------------------------------------------------
-- Row 16

private
  -- 1 < possible s + 1 when s hits: the point of 1 goes to the old point.
  above : (s : ℕ → Bool) → Stream.Hit s
    → Maps.Segment Stream.one (Maps.Successor.next (Stream.possible s))
  above s h = record
    { bound = record
        { to = λ _ → Entry.point h
        ; to-≈ = λ _ → Entry.point≈ tt
        ; to-< = λ ()
        ; reflects-< = λ { (Entry.point< ()) }
        ; ceiling = Entry.top
        ; below = λ _ → Entry.point<top
        }
    ; covers = λ
        { (Entry.point _) _ → tt , Entry.point≈ tt
        ; Entry.top ()
        }
    }

  -- Anything below a point of possible s + 1 is an old point.
  old : (s : ℕ → Bool) (u c : 𝒫.X (Maps.Successor.next (Stream.possible s)))
    → 𝒫._<_ (Maps.Successor.next (Stream.possible s)) u c → Stream.Hit s
  old s (Entry.point h) _ _ = h
  old s Entry.top _ ()

-- Mathematical shape: (Π P Q. Dec (P < Q)) → LPO.
decidable : ((P Q : 𝒫 lzero) → Dec (Maps.Segment P Q)) → Stream.LPO
decidable decide s
  with decide Stream.one (Maps.Successor.next (Stream.possible s))
... | yes σ = inj₁ (old s (B.to tt) B.ceiling (B.below tt))
  where
  module B = Presented._≺𝒫_ (Maps.Segment.bound σ)
... | no none = inj₂ (Stream.absent s λ h → none (above s h))

------------------------------------------------------------------------
-- Rows 17 and 18

-- Mathematical shape: (Π P Q. P ≤ Q → P < Q ⊎ P ≃ Q) → LPO.
split : ((P Q : 𝒫 lzero) → Maps.Initial P Q
    → Maps.Segment P Q ⊎ P Presented.≃𝒫 Q)
  → Stream.LPO
split splitting s
  with splitting (Stream.possible s) Stream.one (Stream.inclusion s)
... | inj₁ σ = inj₂ (Stream.absent s
  (Presented._≺𝒫_.below (Maps.Segment.bound σ)))
... | inj₂ e = inj₁ (Presented._≃𝒫_.from e tt)

-- Mathematical shape: (Π P Q. P < Q ⊎ P ≃ Q ⊎ Q < P) → LPO.
trichotomy : ((P Q : 𝒫 lzero)
    → Maps.Segment P Q ⊎ (P Presented.≃𝒫 Q ⊎ Maps.Segment Q P))
  → Stream.LPO
trichotomy compare s with compare (Stream.possible s) Stream.one
... | inj₁ σ = inj₂ (Stream.absent s
  (Presented._≺𝒫_.below (Maps.Segment.bound σ)))
... | inj₂ (inj₁ e) = inj₁ (Presented._≃𝒫_.from e tt)
... | inj₂ (inj₂ σ) =
  inj₁ (Presented._≺𝒫_.ceiling (Maps.Segment.bound σ))
