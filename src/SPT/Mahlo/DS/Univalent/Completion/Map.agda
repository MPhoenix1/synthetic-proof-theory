{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Univalent.Completion.Map where

-- Completed codes along a map of codes that keeps decodings. Over the
-- ambient parent under univalence (Univalent.Types' `Type-Hypotheses`), let
-- A complete S₁ : K₁ → Set ℓ and B complete S₂ : K₂ → Set ℓ
-- (Univalent.Completion), and let g : K₁ → K₂ keep decodings,
-- S₂ (g k) ＝ S₁ k. Every completed code of A is named in B (`transfer`):
--
--   u : completed A   ⊢   Σ (v : completed B). decode v ＝ decode u.
--
-- The code u is merely the image of a code k of A, the image g k is named
-- in B with the same decoding, and a code covered by such names is named
-- in B (Univalent.Completion's `names-in-the-completion`); no choice of k
-- is made.

open import SPT.Base
open import SPT.Foundation.Covers using (map-covered)
import SPT.Mahlo.Specification as Specification
open import SPT.Mahlo.DS.Univalent.Completion using
  (Completion; names-in-the-completion)
open import SPT.Mahlo.DS.Univalent.Types using (Type-Hypotheses; type-parent)

module _ {ℓ : Level} (H : Type-Hypotheses ℓ) {K₁ K₂ : Set ℓ}
  {S₁ : K₁ → Set ℓ} {S₂ : K₂ → Set ℓ} (A : Completion S₁) (B : Completion S₂)
  (g : K₁ → K₂) (g-β : (k : K₁) → S₂ (g k) ＝ S₁ k)
  where

  -- Mathematical shape: u : completed A ⊢ Name (decode B) (decode u).
  transfer : (u : Completion.completed A) →
    Specification.Name (Completion.decode B) (Completion.decode A u)
  transfer u =
    names-in-the-completion (type-parent H) B (Completion.decode A u)
      (map-covered
        (λ w →
          g (pr₁ w) ,
          (g-β (pr₁ w)
            ∙ (Completion.include-decodes A (pr₁ w) ⁻¹
              ∙ ap (Completion.decode A) (pr₂ w))))
        (Completion.include-covers A u))
