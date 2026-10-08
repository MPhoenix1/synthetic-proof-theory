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

open import Agda.Primitive using (lzero)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
import Data.Unit.Polymorphic as Polymorphic
open import Level using (lift)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; subst)

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
WLPO = (s : ℕ → Bool)
  → ((n : ℕ) → s n ≡ false) ⊎ ¬ ((n : ℕ) → s n ≡ false)

-- Mathematical shape: Π s. ¬(Π n. s n = ff) → Σ n. s n = tt.
MP : Set
MP = (s : ℕ → Bool) → ¬ ((n : ℕ) → s n ≡ false) → Stream.Hit s

-- ω + possible s: ω + 1 when s hits, ω when it never does.
ascent : (ℕ → Bool) → 𝒫 lzero
ascent s = omega + Stream.possible s

private
  clash : (s : ℕ → Bool) → Stream.Hit s → ((n : ℕ) → s n ≡ false) → ⊥
  clash s (n , p) none = true≢false (trans (sym p) (none n))
    where
    true≢false : true ≡ false → ⊥
    true≢false ()

  -- With no hit, possible s is a zero and ω + possible s is ω.
  unshifted : (s : ℕ → Bool) → ((n : ℕ) → s n ≡ false)
    → ascent s Presented.≃𝒫 omega
  unshifted s none =
    Addition.zero-law {P = omega} (Stream.possible s)
      (pointless λ h → clash s h none)

  -- ω lies strictly below ω + Q at any point of Q.
  left : (Q : 𝒫 lzero) → 𝒫.X Q → omega Presented.≺𝒫 (omega + Q)
  left Q q = record
    { to = inj₁ ; to-≈ = λ p → p ; to-< = λ p → p ; reflects-< = λ p → p
    ; ceiling = inj₂ q ; below = λ _ → Polymorphic.tt
    }

  -- ω does not lie strictly below itself.
  irreflexive : omega {lzero} Presented.≺𝒫 omega → ⊥
  irreflexive = Presented.≃𝒫↛≺𝒫 (Presented.≃𝒫-refl omega)

-- Mathematical shape: (Π P. Dec (Zero P)) → WLPO.
zero : ((P : 𝒫 lzero) → Dec (Zero P)) → WLPO
zero decide s with decide (Stream.possible s)
... | yes z = inj₁ (Stream.absent s λ h → empty z h)
... | no not-zero = inj₂ λ none → not-zero (pointless λ h → clash s h none)

-- Mathematical shape: (Π P. Dec (P ≃ ω)) → WLPO.
omega-local : ((P : 𝒫 lzero) → Dec (P Presented.≃𝒫 omega)) → WLPO
omega-local decide s with decide (ascent s)
... | yes e = inj₁ (Stream.absent s λ h →
  irreflexive
    (Maps.bounded (left (Stream.possible s) h) (Maps.equivalence e)))
... | no not-omega = inj₂ λ none → not-omega (unshifted s none)

-- Mathematical shape: (Π P Q. Dec (P ≃ Q)) → WLPO.
equivalence : ((P Q : 𝒫 lzero) → Dec (P Presented.≃𝒫 Q)) → WLPO
equivalence decide = omega-local λ P → decide P omega

private
  -- Points of ω + Q below a left point are left points.
  module Below (Q : 𝒫 lzero) (k : 𝒫.X (omega {lzero})) where

    private
      module S = 𝒫 (omega + Q)
      module O = 𝒫 (omega {lzero})

    part : (v : S.X) → v S.< inj₁ k → O.X
    part (inj₁ y) _ = y
    part (inj₂ _) (lift ())

    part-below : (v : S.X) (p : v S.< inj₁ k) → part v p O.< k
    part-below (inj₁ y) p = p
    part-below (inj₂ _) (lift ())

    part-≈ : (v w : S.X) (p : v S.< inj₁ k) (q : w S.< inj₁ k)
      → v S.≈ w → part v p O.≈ part w q
    part-≈ (inj₁ y) (inj₁ z) _ _ e = e
    part-≈ (inj₂ _) _ (lift ()) _ _
    part-≈ (inj₁ _) (inj₂ _) _ (lift ()) _

    part-< : (v w : S.X) (p : v S.< inj₁ k) (q : w S.< inj₁ k)
      → v S.< w → part v p O.< part w q
    part-< (inj₁ y) (inj₁ z) _ _ r = r
    part-< (inj₂ _) _ (lift ()) _ _
    part-< (inj₁ _) (inj₂ _) _ (lift ()) _

    part-<⁻ : (v w : S.X) (p : v S.< inj₁ k) (q : w S.< inj₁ k)
      → part v p O.< part w q → v S.< w
    part-<⁻ (inj₁ y) (inj₁ z) _ _ r = r
    part-<⁻ (inj₂ _) _ (lift ()) _ _
    part-<⁻ (inj₁ _) (inj₂ _) _ (lift ()) _

  -- A strict bound of ω in ω + Q with a left ceiling k restricts to a
  -- strict bound of ω in ω with ceiling k, which is impossible.
  finite-ceiling : (Q : 𝒫 lzero) (b : omega Presented.≺𝒫 (omega + Q))
    (k : 𝒫.X (omega {lzero})) → Presented._≺𝒫_.ceiling b ≡ inj₁ k → ⊥
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
      → 𝒫._<_ (omega + Q) (B.to x) (inj₁ k)
    below x = subst (𝒫._<_ (omega + Q) (B.to x)) eq (B.below x)

-- Mathematical shape: (Π P. ¬¬(P ≃ ω + 1) → P ≃ ω + 1) → MP.
stable : ((P : 𝒫 lzero) → ¬ ¬ (P Presented.≃𝒫 (omega + Stream.one))
    → P Presented.≃𝒫 (omega + Stream.one))
  → MP
stable stability s not-none = located (Presented._≃𝒫_.from e (inj₂ tt)) refl
  where
  e : ascent s Presented.≃𝒫 (omega + Stream.one)
  e = stability (ascent s) λ not-equivalent →
    not-none (Stream.absent s λ h →
      not-equivalent
        (Addition.equivalence (Presented.≃𝒫-refl omega) (Stream.single s h)))

  -- The preimage of the top point is a hit; a left point is impossible.
  located : (u : 𝒫.X (ascent s))
    → Presented._≃𝒫_.from e (inj₂ tt) ≡ u → Stream.Hit s
  located (inj₂ h) _ = h
  located (inj₁ k) eq =
    ⊥-elim (finite-ceiling (Stream.possible s)
      (Maps.bounded (left Stream.one tt)
        (Maps.equivalence (Presented.≃𝒫-sym e)))
      k eq)
