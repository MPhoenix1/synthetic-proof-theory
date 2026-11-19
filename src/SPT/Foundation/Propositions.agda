{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Propositions where

-- A type is a proposition when any two of its points are identified, so that it
-- carries at most the information that it is inhabited. A type is a set when
-- each of its identity types is a proposition. The loop space of a type at a
-- point is the type of identifications of the point with itself. Nothing here
-- assumes K or uniqueness of identity proofs: a type is a set only by a proof
-- that it is one.
--
-- The empty type and the unit type are propositions. Propositions are sets
-- (`propositions-are-sets`, Hedberg's argument: in a proposition with h,
-- every identification p : y ＝ z is h y y ⁻¹ ∙ h y z), and a sum of
-- propositions over a proposition is a proposition (`Σ-is-proposition`).
-- After TypeTopology (UF.Subsingletons-Properties: props-are-sets,
-- Σ-is-prop).

open import SPT.Base
open import SPT.Foundation.Identifications using
  (apd; transport-is-post-composition; left-transpose)

is-proposition : {ℓ : Level} → Set ℓ → Set ℓ
is-proposition A = (x y : A) → x ＝ y

is-set : {ℓ : Level} → Set ℓ → Set ℓ
is-set A = (x y : A) → is-proposition (x ＝ y)

Loop : {ℓ : Level} (A : Set ℓ) → A → Set ℓ
Loop A x = x ＝ x

------------------------------------------------------------------------
-- Properties

𝟘-is-proposition : is-proposition 𝟘
𝟘-is-proposition () y

𝟙-is-proposition : is-proposition 𝟙
𝟙-is-proposition x y = refl

------------------------------------------------------------------------
-- Propositions are sets

-- h y transports along p : y ＝ z to h z, so p is h y y ⁻¹ ∙ h y z.

module _ {ℓ : Level} {A : Set ℓ} where

  propositions-are-sets : is-proposition A → is-set A
  propositions-are-sets h y z p q =
    left-transpose (h y y) p (h y z)
      (transport-is-post-composition (h y y) p ⁻¹ ∙ apd (h y) p)
    ∙ left-transpose (h y y) q (h y z)
        (transport-is-post-composition (h y y) q ⁻¹ ∙ apd (h y) q) ⁻¹

------------------------------------------------------------------------
-- Sums of propositions

module _ {ℓ κ : Level} {A : Set ℓ} {B : A → Set κ} where

  Σ-is-proposition : is-proposition A → ((a : A) → is-proposition (B a)) →
    is-proposition (Σ A B)
  Σ-is-proposition h k (a , b) (a′ , b′) =
    to-Σ-＝ (h a a′) (k a′ (transport B (h a a′) b) b′)

------------------------------------------------------------------------
-- See also

-- - Function extensionality, under which dependent function types of
--   propositions are propositions.
-- - Contractible types, which are sets.
