{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Isomorphisms.Sets where

-- Sets under isomorphism. For E : A ≅ B with forward-backward law ε, an
-- identification of B is recovered from its backward image, conjugated by
-- ε (`recovered-from-backward-image`):
--
--   ε x ⁻¹ ∙ (ap (forward E) (ap (backward E) p) ∙ ε y) ＝ p.
--
-- So the identifications of B are a retract of those of A, and a type
-- isomorphic to a set is a set (`isomorphic-to-a-set`).

open import SPT.Base
open import SPT.Foundation.Isomorphisms using
  (_≅_; forward; backward; forward-backward)
open import SPT.Foundation.Propositions using (is-set)

------------------------------------------------------------------------
-- Identifications through the backward map

module _ {ℓ κ : Level} {A : Set ℓ} {B : Set κ} (E : A ≅ B) where

  recovered-from-backward-image : {x y : B} (p : x ＝ y) →
    forward-backward E x ⁻¹
      ∙ (ap (forward E) (ap (backward E) p) ∙ forward-backward E y)
      ＝ p
  recovered-from-backward-image {x} refl =
    left-inverse (forward-backward E x)

  isomorphic-to-a-set : is-set A → is-set B
  isomorphic-to-a-set s x y p q =
    recovered-from-backward-image p ⁻¹
      ∙ ap
          (λ r → forward-backward E x ⁻¹
            ∙ (ap (forward E) r ∙ forward-backward E y))
          (s (backward E x) (backward E y) (ap (backward E) p)
            (ap (backward E) q))
      ∙ recovered-from-backward-image q
