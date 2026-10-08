{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Comparison.Discriminator where

-- Lower bounds for the statements of Arithmetic.Comparison that
-- Ambient.Discriminator does not cover. Each goes through possible s, which
-- has a point exactly when s hits true, and gives LPO:
-- - comparability: 1 against possible s (comparable);
-- - Dec (P ≤ Q): 1 ≤ possible s exactly when s hits (initial);
-- - Dec (P ≃ Q): possible s ≃ 1 exactly when s hits (equivalent). This
--   sharpens Characterization.Discriminator.equivalence, which reaches
--   only WLPO through ω;
-- - strict upper bounds of sequences: a common strict bound of
--   possible s + 1 and 1 is a common initial bound, which decides s
--   (bound, through Ambient.Discriminator.common).

open import Agda.Primitive using (lzero)
open import Data.Bool using (Bool)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Limit.Discriminator as Stream
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Ambient using (pair)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Ambient.Discriminator using
  (common)

private
  -- 1 ≤ possible s at a hit: the point goes to the hit.
  point : (s : ℕ → Bool) → Stream.Hit s
    → Maps.Initial Stream.one (Stream.possible s)
  point s h = record
    { map = λ _ → h ; resp = λ _ → tt ; strict = λ () ; lower = λ _ _ () }

-- Mathematical shape: (Π P Q. P ≤ Q ⊎ Q < P) → LPO.
comparable : ((P Q : 𝒫 lzero) → Maps.Initial P Q ⊎ Maps.Segment Q P)
  → Stream.LPO
comparable compare s with compare Stream.one (Stream.possible s)
... | inj₁ f = inj₁ (Maps.Initial.map f tt)
... | inj₂ σ = inj₂ (Stream.absent s λ h →
  Presented._≺𝒫_.below (Maps.Segment.bound σ) h)

-- Mathematical shape: (Π P Q. Dec (P ≤ Q)) → LPO.
initial : ((P Q : 𝒫 lzero) → Dec (Maps.Initial P Q)) → Stream.LPO
initial decide s with decide Stream.one (Stream.possible s)
... | yes f = inj₁ (Maps.Initial.map f tt)
... | no none = inj₂ (Stream.absent s λ h → none (point s h))

-- Mathematical shape: (Π P Q. Dec (P ≃ Q)) → LPO.
equivalent : ((P Q : 𝒫 lzero) → Dec (P Presented.≃𝒫 Q)) → Stream.LPO
equivalent decide s with decide (Stream.possible s) Stream.one
... | yes e = inj₁ (Presented._≃𝒫_.from e tt)
... | no none = inj₂ (Stream.absent s λ h → none (Stream.single s h))

-- Mathematical shape: (Π F : ℕ → 𝒫. Σ S. Π n. F n < S) → LPO.
bound : ((F : ℕ → 𝒫 lzero)
    → Σ (𝒫 lzero) (λ S → (n : ℕ) → Maps.Segment (F n) S))
  → Stream.LPO
bound strict s =
  common s (proj₁ bounded) (Maps.inclusion (proj₂ bounded zero))
    (Maps.inclusion (proj₂ bounded (suc zero)))
  where
  bounded : Σ (𝒫 lzero) (λ S → (n : ℕ)
    → Maps.Segment
        (pair (Maps.Successor.next (Stream.possible s)) Stream.one n) S)
  bounded = strict (pair (Maps.Successor.next (Stream.possible s)) Stream.one)
