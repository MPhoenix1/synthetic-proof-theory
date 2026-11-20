{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization.Discriminator
  where

-- Weak omniscience calibration of the characterizations (Kraus, Nordvall
-- Forsberg and Xu, Theorems 17, 49 and 51), through possible s, which has
-- a point exactly when the Boolean stream s hits true.
-- - Deciding zero, Dec (Zero P) for all P, gives WLPO (zero).
-- - Deciding equivalence with ω, Dec (P ≃ ω) for all P, gives WLPO: ω +
--   possible s is ω exactly when s never hits (omega). So does deciding
--   ≃𝒫 everywhere (equivalence); the limits of their Theorem 17 are
--   present in the geometry.
-- - Stability of equivalence with ω + 1 gives MP: ω + possible s is
--   ω + 1 exactly when s hits, and an equivalence locates the hit, since
--   ω does not embed below a point of ω (stable). For Brouwer trees
--   stability at ω + 1 holds (Theorem 51 and the remark after it); a
--   presentation need not show whether it is a successor.
-- These are lower bounds, not equivalences.

open import SPT.Cubical.Base hiding (_+_; zero)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
open import SPT.Cubical.OrdinalGeometry.Presentation.Sum using (_+_)
import SPT.Cubical.OrdinalGeometry.Presentation.Limit.Discriminator as Stream
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization using
  (Zero; empty; pointless)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Addition as Addition
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Exponential using (omega)

-- Mathematical shape: Π s. (Π n. s n = ff) ⊎ ¬(Π n. s n = ff).
WLPO : Set
WLPO = (s : ℕ → 𝟚)
  → ((n : ℕ) → s n ＝ ₀) ⊎ ¬ ((n : ℕ) → s n ＝ ₀)

-- Mathematical shape: Π s. ¬(Π n. s n = ff) → Σ n. s n = tt.
MP : Set
MP = (s : ℕ → 𝟚) → ¬ ((n : ℕ) → s n ＝ ₀) → Stream.Hit s

-- ω + possible s: ω + 1 when s hits, ω when it never does.
ascent : (ℕ → 𝟚) → 𝒫 lzero
ascent s = omega + Stream.possible s

private
  clash : (s : ℕ → 𝟚) → Stream.Hit s → ((n : ℕ) → s n ＝ ₀) → 𝟘
  clash s (n , p) none = true≢false (p ⁻¹ ∙ none n)
    where
    true≢false : ₁ ＝ ₀ → 𝟘
    true≢false ()

  -- With no hit, possible s is a zero and ω + possible s is ω.
  unshifted : (s : ℕ → 𝟚) → ((n : ℕ) → s n ＝ ₀)
    → ascent s Presented.≃𝒫 omega
  unshifted s none =
    Addition.zero-law {P = omega} (Stream.possible s)
      (pointless λ h → clash s h none)

  -- ω lies strictly below ω + Q at any point of Q.
  left : (Q : 𝒫 lzero) → 𝒫.X Q → omega Presented.≺𝒫 (omega + Q)
  left Q q = record
    { to = inl ; to-≈ = λ p → p ; to-< = λ p → p ; reflects-< = λ p → p
    ; ceiling = inr q ; below = λ _ → (lift ⋆)
    }

  -- ω does not lie strictly below itself.
  irreflexive : omega {lzero} Presented.≺𝒫 omega → 𝟘
  irreflexive = Presented.≃𝒫↛≺𝒫 (Presented.≃𝒫-refl omega)

-- Mathematical shape: (Π P. Dec (Zero P)) → WLPO.
zero : ((P : 𝒫 lzero) → is-decidable (Zero P)) → WLPO
zero decide s with decide (Stream.possible s)
... | inl z = inl (Stream.absent s λ h → empty z h)
... | inr not-zero = inr λ none → not-zero (pointless λ h → clash s h none)

-- Mathematical shape: (Π P. Dec (P ≃ ω)) → WLPO.
omega-local : ((P : 𝒫 lzero) → is-decidable (P Presented.≃𝒫 omega)) → WLPO
omega-local decide s with decide (ascent s)
... | inl e = inl (Stream.absent s λ h →
  irreflexive
    (Maps.bounded (left (Stream.possible s) h) (Maps.equivalence e)))
... | inr not-omega = inr λ none → not-omega (unshifted s none)

-- Mathematical shape: (Π P Q. Dec (P ≃ Q)) → WLPO.
equivalence : ((P Q : 𝒫 lzero) → is-decidable (P Presented.≃𝒫 Q)) → WLPO
equivalence decide = omega-local λ P → decide P omega

private
  -- Points of ω + Q below a left point are left points.
  module Below (Q : 𝒫 lzero) (k : 𝒫.X (omega {lzero})) where

    private
      module S = 𝒫 (omega + Q)
      module O = 𝒫 (omega {lzero})

    part : (v : S.X) → v S.< inl k → O.X
    part (inl y) _ = y
    part (inr _) (lift ())

    part-below : (v : S.X) (p : v S.< inl k) → part v p O.< k
    part-below (inl y) p = p
    part-below (inr _) (lift ())

    part-≈ : (v w : S.X) (p : v S.< inl k) (q : w S.< inl k)
      → v S.≈ w → part v p O.≈ part w q
    part-≈ (inl y) (inl z) _ _ e = e
    part-≈ (inr _) _ (lift ()) _ _
    part-≈ (inl _) (inr _) _ (lift ()) _

    part-< : (v w : S.X) (p : v S.< inl k) (q : w S.< inl k)
      → v S.< w → part v p O.< part w q
    part-< (inl y) (inl z) _ _ r = r
    part-< (inr _) _ (lift ()) _ _
    part-< (inl _) (inr _) _ (lift ()) _

    part-<⁻ : (v w : S.X) (p : v S.< inl k) (q : w S.< inl k)
      → part v p O.< part w q → v S.< w
    part-<⁻ (inl y) (inl z) _ _ r = r
    part-<⁻ (inr _) _ (lift ()) _ _
    part-<⁻ (inl _) (inr _) _ (lift ()) _

  -- A strict bound of ω in ω + Q with a left ceiling k restricts to a
  -- strict bound of ω in ω with ceiling k, which is impossible.
  finite-ceiling : (Q : 𝒫 lzero) (b : omega Presented.≺𝒫 (omega + Q))
    (k : 𝒫.X (omega {lzero})) → Presented._≺𝒫_.ceiling b ＝ inl k → 𝟘
  finite-ceiling Q b k eq = irreflexive record
    { to = λ x → part (B.to x) (below x)
    ; to-≈ = λ {x} {y} e → part-≈ (B.to x) (B.to y) (below x) (below y)
        (B.to-≈ e)
    ; to-< = λ {x} {y} r → part-< (B.to x) (B.to y) (below x) (below y)
        (B.to-< r)
    ; reflects-< = λ {x} {y} r →
        B.reflects-< (part-<⁻ (B.to x) (B.to y) (below x) (below y) r)
    ; ceiling = k
    ; below = λ x → part-below (B.to x) (below x)
    }
    where
    module B = Presented._≺𝒫_ b
    open Below Q k

    below : (x : 𝒫.X (omega {lzero}))
      → 𝒫._<_ (omega + Q) (B.to x) (inl k)
    below x = transport (𝒫._<_ (omega + Q) (B.to x)) eq (B.below x)

-- Mathematical shape: (Π P. ¬¬(P ≃ ω + 1) → P ≃ ω + 1) → MP.
stable : ((P : 𝒫 lzero) → ¬ ¬ (P Presented.≃𝒫 (omega + Stream.one))
    → P Presented.≃𝒫 (omega + Stream.one))
  → MP
stable stability s not-none = located (Presented._≃𝒫_.from e (inr ⋆)) refl
  where
  e : ascent s Presented.≃𝒫 (omega + Stream.one)
  e = stability (ascent s) λ not-equivalent →
    not-none (Stream.absent s λ h →
      not-equivalent
        (Addition.equivalence (Presented.≃𝒫-refl omega) (Stream.single s h)))

  -- The preimage of the top point is a hit; a left point is impossible.
  located : (u : 𝒫.X (ascent s))
    → Presented._≃𝒫_.from e (inr ⋆) ＝ u → Stream.Hit s
  located (inr h) _ = h
  located (inl k) eq =
    𝟘-elim (finite-ceiling (Stream.possible s)
      (Maps.bounded (left Stream.one ⋆)
        (Maps.equivalence (Presented.≃𝒫-sym e)))
      k eq)
