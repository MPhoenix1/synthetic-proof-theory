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

open import SPT.Cubical.Base hiding (_+_)
import SPT.Cubical.Base as Nat
open import SPT.Cubical.Foundation.LogicalEquivalence using (_⇔_)
open import SPT.Cubical.Foundation.Nat.Arithmetic using
  ( +-right-preserves-≤ℕˢ; +-∸-cancels; ∸-+-cancels; ∸-right-preserves-<ℕˢ
  ; ≤ℕˢ-+-left; ≤ℕˢ-or-above; ≤ℕˢ-pred )
open import SPT.Cubical.Foundation.Two.Connectives using (_∨_; ∨-＝-₁-right)

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

  true≢false : ₁ ＝ ₀ → 𝟘
  true≢false ()

  -- Mathematical shape: m ≠ nothing, as a Boolean.
  occupied : {A : Set ℓ} → Maybe A → 𝟚
  occupied = maybe-rec ₀ (λ _ → ₁)

------------------------------------------------------------------------
-- Zero

-- Mathematical shape: WLPO → Π P. Dec (Zero P).
decide-zero : WLPO → (P : 𝒫 ℓ) → is-decidable (Zero P)
decide-zero wlpo P =
  cases
    (λ none → inl (pointless {Z = P} (vacant none)))
    (λ hit → inr λ z → hit (gap z))
    (wlpo (λ n → occupied (𝒫.enum P n)))
  where
  -- No enumerated point: no point at all.
  vacant : ((n : ℕ) → occupied (𝒫.enum P n) ＝ ₀) → 𝒫.X P → 𝟘
  vacant none x =
    let n , r , selected , r≈x = 𝒫.covers P x
    in true≢false (ap occupied selected ⁻¹ ∙ none n)

  -- A zero has no point, so its enumeration never hits.
  gap : Zero P → (n : ℕ) → occupied (𝒫.enum P n) ＝ ₀
  gap z n = at (𝒫.enum P n)
    where
    at : (m : Maybe (𝒫.X P)) → occupied m ＝ ₀
    at nothing = refl
    at (just x) = 𝟘-elim (empty {Z = P} z x)

-- Mathematical shape: WLPO ⇔ Π P. Dec (Zero P).
zero-strength : WLPO ⇔ ((P : 𝒫 lzero) → is-decidable (Zero P))
zero-strength =
  ((λ wlpo → decide-zero wlpo) , CharacterizationDiscriminator.zero)

------------------------------------------------------------------------
-- Equivalence with ω

-- The points at or after the first hit of s.
module Suffix (s : ℕ → 𝟚) where

  -- reached n: s hits at some m ≤ n.
  reached : ℕ → 𝟚
  reached zero = s zero
  reached (suc n) = reached n ∨ s (suc n)

  private
    disjunct : (a b : 𝟚) → a ∨ b ＝ ₁ → (a ＝ ₁) ⊎ (b ＝ ₁)
    disjunct ₁ _ _ = inl refl
    disjunct ₀ b p = inr p

    up : (n : ℕ) → reached n ＝ ₁ → reached (suc n) ＝ ₁
    up n p = ap (λ a → a ∨ s (suc n)) p

    monotone : {m n : ℕ} → m ≤ℕ′ n → reached m ＝ ₁ → reached n ＝ ₁
    monotone ≤ℕ′-refl p = p
    monotone (≤ℕ′-step {n = n} q) p = up n (monotone q p)

    reach : (k : ℕ) → s k ＝ ₁ → reached k ＝ ₁
    reach zero p = p
    reach (suc k) p =
      ap (λ b → reached k ∨ b) p ∙ ∨-＝-₁-right (reached k) ₁ refl

    -- Below an unreached point nothing is reached.
    falls : (m k : ℕ) → m ≤ℕˢ k → reached k ＝ ₀ → reached m ＝ ₀
    falls m k r q = settle (reached m) refl
      where
      settle : (u : 𝟚) → reached m ＝ u → reached m ＝ ₀
      settle ₀ e = e
      settle ₁ e = 𝟘-elim (true≢false
        (monotone (≤ℕˢ-to-≤ℕ′ r) e ⁻¹ ∙ q))

    -- The least reached point at or below a reached point.
    Least : Set
    Least = Σ ℕ (λ b → (reached b ＝ ₁)
      × ((m : ℕ) → m <ℕˢ b → reached m ＝ ₀))

    bottom : (k : ℕ) → reached k ＝ ₁ → Least
    bottom zero p = zero , p , λ m ()
    bottom (suc k) p = settle (reached k) refl (bottom k)
      where
      settle : (u : 𝟚) → reached k ＝ u → (reached k ＝ ₁ → Least)
        → Least
      settle ₁ q deeper = deeper q
      settle ₀ q deeper =
        suc k , p , λ m r → falls m k (≤ℕˢ-pred r) q

  -- Mathematical shape: {n ∈ ω | s hits at some m ≤ n}, ordered as in ω.
  suffix : 𝒫 lzero
  suffix = Stream.hits reached

  -- A point of the suffix holds a hit.
  hit : (n : ℕ) → reached n ＝ ₁ → Stream.Hit s
  hit zero p = zero , p
  hit (suc n) p =
    cases (hit n) (λ q → suc n , q) (disjunct (reached n) (s (suc n)) p)

  -- After a hit the suffix is ω, shifted down by its least point.
  equivalence : Stream.Hit s → suffix Presented.≃𝒫 omega
  equivalence (k , p) = record
    { to = λ u → lift (pr₁ u ∸ first)
    ; from = λ j → lower j Nat.+ first
        , monotone (≤ℕˢ-to-≤ℕ′ (≤ℕˢ-+-left (lower j) first))
            reached-first
    ; to-≈ = λ e → lift (ap (_∸ first) e)
    ; from-≈ = λ e → ap (Nat._+ first) (lower e)
    ; to-< = λ {u} {v} q →
        lift (∸-right-preserves-<ℕˢ first (above u) q)
    ; from-< = λ q → +-right-preserves-≤ℕˢ first (lower q)
    ; from-to-≈ = λ u → ∸-+-cancels (above u)
    ; to-from-≈ = λ j → lift (+-∸-cancels (lower j) first)
    }
    where
    least : Least
    least = bottom k (reach k p)

    first : ℕ
    first = pr₁ least

    reached-first : reached first ＝ ₁
    reached-first = pr₁ (pr₂ least)

    above : (u : 𝒫.X suffix) → first ≤ℕˢ pr₁ u
    above (n , q) =
      cases (λ p → p)
        (λ r → 𝟘-elim (true≢false (q ⁻¹ ∙ pr₂ (pr₂ least) n r)))
        (≤ℕˢ-or-above first n)

-- Mathematical shape: (Π P. Dec (P ≃ ω)) → LPO.
omega-lpo : ((P : 𝒫 lzero) → is-decidable (P Presented.≃𝒫 omega)) → Stream.LPO
omega-lpo decide s with decide (Suffix.suffix s)
... | inl e =
  let u = Presented._≃𝒫_.from e (lift zero)
  in inl (Suffix.hit s (pr₁ u) (pr₂ u))
... | inr none = inr (Stream.absent s λ h → none (Suffix.equivalence s h))

-- Mathematical shape: LPO ⇔ Π P. Dec (P ≃ ω).
omega-strength : Stream.LPO
  ⇔ ((P : 𝒫 lzero) → is-decidable (P Presented.≃𝒫 omega))
omega-strength =
  ((λ lpo P → Comparison.equivalent lpo P omega) , omega-lpo)

------------------------------------------------------------------------
-- Stability at ω + 1

-- Mathematical shape: LPO → Π P. ¬¬(P ≃ ω + 1) → P ≃ ω + 1.
stable : Stream.LPO → (P : 𝒫 lzero)
  → ¬ ¬ (P Presented.≃𝒫 (omega + Stream.one))
  → P Presented.≃𝒫 (omega + Stream.one)
stable lpo P twice =
  decided (Comparison.equivalent lpo P (omega + Stream.one))
  where
  decided : is-decidable (P Presented.≃𝒫 (omega + Stream.one))
    → P Presented.≃𝒫 (omega + Stream.one)
  decided (inl e) = e
  decided (inr n) = 𝟘-elim (twice n)
