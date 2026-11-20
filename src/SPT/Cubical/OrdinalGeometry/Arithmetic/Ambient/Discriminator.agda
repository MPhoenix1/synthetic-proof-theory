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

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Nat.Arithmetic using
  ( <ℕˢ-to-≤ℕˢ; ≤ℕˢ-or-above; ≤ℕˢ-pred; ≤ℕˢ-split )
open import SPT.Cubical.Foundation.Two.Connectives using
  ( _∧_; not; ∧-₀-absorbs-right; ∧-₁-unit-right )

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
  ceiling : (s : ℕ → 𝟚) → Maps.Segment (Stream.possible s) two
    → Stream.Hit s ⊎ ((n : ℕ) → s n ＝ ₀)
  ceiling s σ = at B.ceiling B.below (Maps.Segment.covers σ)
    where
    module B = Presented._≺𝒫_ (Maps.Segment.bound σ)

    at : (c : 𝒫.X two) → ((h : Stream.Hit s) → 𝒫._<_ two (B.to h) c)
      → ((y : 𝒫.X two) → 𝒫._<_ two y c
          → Σ (Stream.Hit s) (λ h → 𝒫._≈_ two (B.to h) y))
      → Stream.Hit s ⊎ ((n : ℕ) → s n ＝ ₀)
    at Entry.top _ covers =
      inl (pr₁ (covers (Entry.point ⋆) Entry.point<top))
    at (Entry.point _) below _ = inr (Stream.absent s λ h → bottom (below h))

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
    → 𝒫._<_ Q y (Maps.Initial.map g ⋆) → 𝟘
  least {Q} g y p with Maps.Initial.lower g ⋆ y p
  ... | ⋆ , q = Presented.Presentation.≈↛< Q (𝒫.≈-sym Q q) p

-- A common initial bound Q of possible s + 1 and 1 decides s: the top of
-- possible s + 1 lands on the point of 1 exactly when s never hits, and
-- above it exactly when an old point of possible s lies below.
common : (s : ℕ → 𝟚) (Q : 𝒫 lzero)
  → Maps.Initial (Maps.Successor.next (Stream.possible s)) Q
  → Maps.Initial Stream.one Q
  → Stream.Hit s ⊎ ((n : ℕ) → s n ＝ ₀)
common s Q f g
  with 𝒫.compare Q (Maps.Initial.map f Entry.top) (Maps.Initial.map g ⋆)
... | inl p = 𝟘-elim (least g _ p)
... | inr (inl q) = inr (Stream.absent s λ h → least g _
  (𝒫.<-respʳ-≈ Q q
    (Maps.Initial.strict f {x = Entry.point h} Entry.point<top)))
... | inr (inr p)
  with Maps.Initial.lower f Entry.top (Maps.Initial.map g ⋆) p
...   | Entry.point h , _ = inl h
...   | Entry.top , q =
  𝟘-elim (Presented.Presentation.≈↛< Q (𝒫.≈-sym Q q) p)

-- The family (possible s + 1, 1, 1, …): a common initial bound of its
-- members decides s.
family : (ℕ → 𝟚) → ℕ → 𝒫 lzero
family s = pair (Maps.Successor.next (Stream.possible s)) Stream.one

-- Mathematical shape: (Π P Q. Σ S. S is-sup-of (P, Q, Q, …)) → LPO.
join : ((P Q : 𝒫 lzero) → Σ (𝒫 lzero) (Supremum (pair P Q)))
  → Stream.LPO
join sup s = common s (pr₁ σ) (Supremum.member (pr₂ σ) zero)
  (Supremum.member (pr₂ σ) (suc zero))
  where
  σ : Σ (𝒫 lzero) (Supremum (family s))
  σ = sup (Maps.Successor.next (Stream.possible s)) Stream.one

-- Mathematical shape: (Π F : ℕ → 𝒫. Σ S. S is-sup-of F) → LPO.
supremum : ((F : ℕ → 𝒫 lzero) → Σ (𝒫 lzero) (Supremum F)) → Stream.LPO
supremum sup = join (λ P Q → sup (pair P Q))

------------------------------------------------------------------------
-- Row 15

private
  module Prefix (s : ℕ → 𝟚) where

    -- clear n: s is false at every m ≤ n.
    clear : ℕ → 𝟚
    clear zero = not (s zero)
    clear (suc n) = clear n ∧ not (s (suc n))

    conjunct : (a b : 𝟚) → a ∧ b ＝ ₁ → a ＝ ₁
    conjunct ₁ _ _ = refl

    clash : {b : 𝟚} → b ＝ ₁ → b ＝ ₀ → 𝟘
    clash refl ()

    closed : (n : ℕ) → clear n ＝ ₁ → (m : ℕ) → m ≤ℕˢ n
      → clear m ＝ ₁
    closed zero p .zero z≤n = p
    closed (suc n) p m q with ≤ℕˢ-split m (suc n) q
    ... | inr refl = p
    ... | inl r = closed n (conjunct (clear n) _ p) m (≤ℕˢ-pred r)

    stop : (n : ℕ) → s n ＝ ₁ → clear n ＝ ₀
    stop zero p = ap not p
    stop (suc n) p =
      ap (λ b → clear n ∧ not b) p ∙ ∧-₀-absorbs-right (clear n)

    hit : (n : ℕ) → clear n ＝ ₀ → Stream.Hit s
    hit zero p = zero , flip (s zero) p
      where
      flip : (b : 𝟚) → not b ＝ ₀ → b ＝ ₁
      flip ₁ _ = refl
    hit (suc n) p = step (s (suc n)) refl p
      where
      step : (b : 𝟚) → s (suc n) ＝ b → clear n ∧ not b ＝ ₀
        → Stream.Hit s
      step ₁ q _ = suc n , q
      step ₀ _ r = hit n (∧-₁-unit-right (clear n) ⁻¹ ∙ r)

    -- The first k at which clear fails: the first hit of s.
    first : (n : ℕ) → clear n ＝ ₀ → Σ ℕ (λ k →
      Σ (clear k ＝ ₀) (λ _ → (m : ℕ) → m <ℕˢ k → clear m ＝ ₁))
    first zero p = zero , p , λ _ ()
    first (suc n) p = step (clear n) refl
      where
      step : (b : 𝟚) → clear n ＝ b → Σ ℕ (λ k →
        Σ (clear k ＝ ₀) (λ _ → (m : ℕ) → m <ℕˢ k → clear m ＝ ₁))
      step ₁ q = suc n , p , λ m r → closed n q m (≤ℕˢ-pred r)
      step ₀ q = first n q

    -- Mathematical shape: {n ∈ ω | s is false up to n}, ordered as in ω.
    prefix : 𝒫 lzero
    prefix = Stream.hits clear

    -- The prefix is an initial segment of ω.
    initial : Maps.Initial prefix omega
    initial = record
      { map = λ u → lift (pr₁ u)
      ; resp = lift
      ; strict = lift
      ; lower = λ u y p →
          (lower y , closed (pr₁ u) (pr₂ u) (lower y)
            (<ℕˢ-to-≤ℕˢ (lower p))) , lift refl
      }

    -- A proper segment of ω containing the prefix has its ceiling at a
    -- hit: its map is the initial map above, so the prefix stays below.
    bounded : Maps.Segment prefix omega → Stream.Hit s
    bounded σ = at (clear k) refl
      where
      module B = Presented._≺𝒫_ (Maps.Segment.bound σ)

      k : ℕ
      k = lower B.ceiling

      under : (u : 𝒫.X prefix) → pr₁ u <ℕˢ k
      under u = transport (λ m → m <ℕˢ k)
        (lower (Maps.Uniqueness.pointwise (Maps.inclusion σ) initial u))
        (lower (B.below u))

      at : (b : 𝟚) → clear k ＝ b → Stream.Hit s
      at ₁ q = 𝟘-elim (<ℕˢ-irrefl k (under (k , q)))
      at ₀ q = hit k q

    -- After a hit, the prefix is the proper segment of ω below the first
    -- hit.
    segment : Stream.Hit s → Maps.Segment prefix omega
    segment (n , p) with first n (stop n p)
    ... | k , q , before = record
      { bound = record
          { to = λ u → lift (pr₁ u)
          ; to-≈ = lift
          ; to-< = lift
          ; reflects-< = lower
          ; ceiling = lift k
          ; below = λ u → lift
              (cases (λ r → 𝟘-elim (clash (closed (pr₁ u) (pr₂ u) k r) q))
                (λ p → p) (≤ℕˢ-or-above k (pr₁ u)))
          }
      ; covers = λ y r → (lower y , before (lower y) (lower r)) , lift refl
      }

-- Mathematical shape: (Π P. Dec (P < ω)) → LPO.
finite : ((P : 𝒫 lzero) → is-decidable (Maps.Segment P omega)) → Stream.LPO
finite decide s with decide (Prefix.prefix s)
... | inl σ = inl (Prefix.bounded s σ)
... | inr none = inr (Stream.absent s λ h → none (Prefix.segment s h))

------------------------------------------------------------------------
-- Row 16

private
  -- 1 < possible s + 1 when s hits: the point of 1 goes to the old point.
  above : (s : ℕ → 𝟚) → Stream.Hit s
    → Maps.Segment Stream.one (Maps.Successor.next (Stream.possible s))
  above s h = record
    { bound = record
        { to = λ _ → Entry.point h
        ; to-≈ = λ _ → Entry.point≈ ⋆
        ; to-< = λ ()
        ; reflects-< = λ { (Entry.point< ()) }
        ; ceiling = Entry.top
        ; below = λ _ → Entry.point<top
        }
    ; covers = λ
        { (Entry.point _) _ → ⋆ , Entry.point≈ ⋆
        ; Entry.top ()
        }
    }

  -- Anything below a point of possible s + 1 is an old point.
  old : (s : ℕ → 𝟚) (u c : 𝒫.X (Maps.Successor.next (Stream.possible s)))
    → 𝒫._<_ (Maps.Successor.next (Stream.possible s)) u c → Stream.Hit s
  old s (Entry.point h) _ _ = h
  old s Entry.top _ ()

-- Mathematical shape: (Π P Q. Dec (P < Q)) → LPO.
decidable : ((P Q : 𝒫 lzero) → is-decidable (Maps.Segment P Q)) → Stream.LPO
decidable decide s
  with decide Stream.one (Maps.Successor.next (Stream.possible s))
... | inl σ = inl (old s (B.to ⋆) B.ceiling (B.below ⋆))
  where
  module B = Presented._≺𝒫_ (Maps.Segment.bound σ)
... | inr none = inr (Stream.absent s λ h → none (above s h))

------------------------------------------------------------------------
-- Rows 17 and 18

-- Mathematical shape: (Π P Q. P ≤ Q → P < Q ⊎ P ≃ Q) → LPO.
split : ((P Q : 𝒫 lzero) → Maps.Initial P Q
    → Maps.Segment P Q ⊎ (P Presented.≃𝒫 Q))
  → Stream.LPO
split splitting s
  with splitting (Stream.possible s) Stream.one (Stream.inclusion s)
... | inl σ = inr (Stream.absent s
  (Presented._≺𝒫_.below (Maps.Segment.bound σ)))
... | inr e = inl (Presented._≃𝒫_.from e ⋆)

-- Mathematical shape: (Π P Q. P < Q ⊎ P ≃ Q ⊎ Q < P) → LPO.
trichotomy : ((P Q : 𝒫 lzero)
    → Maps.Segment P Q ⊎ ((P Presented.≃𝒫 Q) ⊎ Maps.Segment Q P))
  → Stream.LPO
trichotomy compare s with compare (Stream.possible s) Stream.one
... | inl σ = inr (Stream.absent s
  (Presented._≺𝒫_.below (Maps.Segment.bound σ)))
... | inr (inl e) = inl (Presented._≃𝒫_.from e ⋆)
... | inr (inr σ) =
  inl (Presented._≺𝒫_.ceiling (Maps.Segment.bound σ))
