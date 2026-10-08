{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization.Strength where

-- Exact strength of the decisions of Characterization.Discriminator.
-- - Dec (Zero P) for all P is exactly WLPO (zero-strength): P is a zero
--   exactly when its enumeration never hits, a Π⁰₁ statement
--   (decide-zero).
-- - Dec (P ≃ ω) for all P is exactly LPO (omega-strength). The lower bound
--   uses the presentation {n | s hits at some m ≤ n} (Suffix), which is ω
--   after a hit and empty otherwise; Characterization.Discriminator.
--   omega-local reached only WLPO, through ω + possible s. The upper bound
--   is Comparison.equivalent.
-- - Stability of P ≃ ω + 1 lies between MP (Characterization.
--   Discriminator.stable) and LPO (stable); its exact strength is not
--   determined here.

open import Agda.Primitive using (Level; lzero)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤′_; ≤′-refl; ≤′-step)
import Data.Nat as Nat
import Data.Nat.Properties as NatProperties
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function.Bundles using (_⇔_; mk⇔)
open import Level using (lift; lower)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
open import SPT.Cubical.OrdinalGeometry.Presentation.Sum using (_+_)
import SPT.Cubical.OrdinalGeometry.Presentation.Limit.Discriminator as Stream
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization using
  (Zero; empty; pointless)
open import
  SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization.Discriminator
  using (WLPO)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization.Discriminator
  as CharacterizationDiscriminator
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Exponential using (omega)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Comparison as Comparison

private
  variable
    ℓ : Level

  true≢false : true ≡ false → ⊥
  true≢false ()

  -- Mathematical shape: m ≠ nothing, as a Boolean.
  occupied : {A : Set ℓ} → Maybe A → Bool
  occupied = maybe′ (λ _ → true) false

------------------------------------------------------------------------
-- Zero

-- Mathematical shape: WLPO → Π P. Dec (Zero P).
decide-zero : WLPO → (P : 𝒫 ℓ) → Dec (Zero P)
decide-zero wlpo P =
  [ (λ none → yes (pointless {Z = P} (vacant none)))
  , (λ hit → no λ z → hit (gap z))
  ]′ (wlpo (λ n → occupied (𝒫.enum P n)))
  where
  -- No enumerated point: no point at all.
  vacant : ((n : ℕ) → occupied (𝒫.enum P n) ≡ false) → 𝒫.X P → ⊥
  vacant none x =
    let n , r , selected , r≈x = 𝒫.covers P x
    in true≢false (trans (sym (cong occupied selected)) (none n))

  -- A zero has no point, so its enumeration never hits.
  gap : Zero P → (n : ℕ) → occupied (𝒫.enum P n) ≡ false
  gap z n = at (𝒫.enum P n)
    where
    at : (m : Maybe (𝒫.X P)) → occupied m ≡ false
    at nothing = refl
    at (just x) = ⊥-elim (empty {Z = P} z x)

-- Mathematical shape: WLPO ⇔ Π P. Dec (Zero P).
zero-strength : WLPO ⇔ ((P : 𝒫 lzero) → Dec (Zero P))
zero-strength =
  mk⇔ (λ wlpo → decide-zero wlpo) CharacterizationDiscriminator.zero

------------------------------------------------------------------------
-- Equivalence with ω

-- The points at or after the first hit of s.
module Suffix (s : ℕ → Bool) where

  -- reached n: s hits at some m ≤ n.
  reached : ℕ → Bool
  reached zero = s zero
  reached (suc n) = reached n ∨ s (suc n)

  private
    disjunct : (a b : Bool) → a ∨ b ≡ true → a ≡ true ⊎ b ≡ true
    disjunct true _ _ = inj₁ refl
    disjunct false b p = inj₂ p

    up : (n : ℕ) → reached n ≡ true → reached (suc n) ≡ true
    up n p = cong (λ a → a ∨ s (suc n)) p

    monotone : {m n : ℕ} → m ≤′ n → reached m ≡ true → reached n ≡ true
    monotone ≤′-refl p = p
    monotone (≤′-step {n = n} q) p = up n (monotone q p)

    reach : (k : ℕ) → s k ≡ true → reached k ≡ true
    reach zero p = p
    reach (suc k) p =
      trans (cong (λ b → reached k ∨ b) p) (∨-zeroʳ (reached k))

    -- Below an unreached point nothing is reached.
    falls : (m k : ℕ) → m Nat.≤ k → reached k ≡ false → reached m ≡ false
    falls m k r q = settle (reached m) refl
      where
      settle : (u : Bool) → reached m ≡ u → reached m ≡ false
      settle false e = e
      settle true e = ⊥-elim (true≢false
        (trans (sym (monotone (NatProperties.≤⇒≤′ r) e)) q))

    -- The least reached point at or below a reached point.
    Least : Set
    Least = Σ ℕ (λ b → reached b ≡ true
      × ((m : ℕ) → m Nat.< b → reached m ≡ false))

    bottom : (k : ℕ) → reached k ≡ true → Least
    bottom zero p = zero , p , λ m ()
    bottom (suc k) p = settle (reached k) refl (bottom k)
      where
      settle : (u : Bool) → reached k ≡ u → (reached k ≡ true → Least)
        → Least
      settle true q deeper = deeper q
      settle false q deeper =
        suc k , p , λ m r → falls m k (NatProperties.≤-pred r) q

  -- Mathematical shape: {n ∈ ω | s hits at some m ≤ n}, ordered as in ω.
  suffix : 𝒫 lzero
  suffix = Stream.hits reached

  -- A point of the suffix holds a hit.
  hit : (n : ℕ) → reached n ≡ true → Stream.Hit s
  hit zero p = zero , p
  hit (suc n) p =
    [ hit n , (λ q → suc n , q) ]′ (disjunct (reached n) (s (suc n)) p)

  -- After a hit the suffix is ω, shifted down by its least point.
  equivalence : Stream.Hit s → suffix Presented.≃𝒫 omega
  equivalence (k , p) = record
    { to = λ u → lift (proj₁ u ∸ first)
    ; from = λ j → lower j Nat.+ first
        , monotone (NatProperties.≤⇒≤′ (NatProperties.m≤n+m first (lower j)))
            reached-first
    ; to-≈ = λ e → lift (cong (_∸ first) e)
    ; from-≈ = λ e → cong (Nat._+ first) (lower e)
    ; to-< = λ {u} {v} q → lift (NatProperties.∸-monoˡ-< q (above u))
    ; from-< = λ q → NatProperties.+-monoˡ-< first (lower q)
    ; from-to-≈ = λ u → NatProperties.m∸n+n≡m (above u)
    ; to-from-≈ = λ j → lift (NatProperties.m+n∸n≡m (lower j) first)
    }
    where
    least : Least
    least = bottom k (reach k p)

    first : ℕ
    first = proj₁ least

    reached-first : reached first ≡ true
    reached-first = proj₁ (proj₂ least)

    above : (u : 𝒫.X suffix) → first Nat.≤ proj₁ u
    above (n , q) = NatProperties.≮⇒≥ λ r →
      true≢false (trans (sym q) (proj₂ (proj₂ least) n r))

-- Mathematical shape: (Π P. Dec (P ≃ ω)) → LPO.
omega-lpo : ((P : 𝒫 lzero) → Dec (P Presented.≃𝒫 omega)) → Stream.LPO
omega-lpo decide s with decide (Suffix.suffix s)
... | yes e =
  let u = Presented._≃𝒫_.from e (lift zero)
  in inj₁ (Suffix.hit s (proj₁ u) (proj₂ u))
... | no none = inj₂ (Stream.absent s λ h → none (Suffix.equivalence s h))

-- Mathematical shape: LPO ⇔ Π P. Dec (P ≃ ω).
omega-strength : Stream.LPO
  ⇔ ((P : 𝒫 lzero) → Dec (P Presented.≃𝒫 omega))
omega-strength =
  mk⇔ (λ lpo P → Comparison.equivalent lpo P omega) omega-lpo

------------------------------------------------------------------------
-- Stability at ω + 1

-- Mathematical shape: LPO → Π P. ¬¬(P ≃ ω + 1) → P ≃ ω + 1.
stable : Stream.LPO → (P : 𝒫 lzero)
  → ¬ ¬ (P Presented.≃𝒫 (omega + Stream.one))
  → P Presented.≃𝒫 (omega + Stream.one)
stable lpo P twice =
  decided (Comparison.equivalent lpo P (omega + Stream.one))
  where
  decided : Dec (P Presented.≃𝒫 (omega + Stream.one))
    → P Presented.≃𝒫 (omega + Stream.one)
  decided (yes e) = e
  decided (no n) = ⊥-elim (twice n)
