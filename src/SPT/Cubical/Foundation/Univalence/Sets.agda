{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Univalence.Sets where

-- The type of sets under univalence. Under univalence at two types, the second
-- a set, and extensionality at their level, their identifications form a set
-- (`identifications-with-a-set-form-a-set`). They are isomorphic to the
-- equivalences between the two through `idtoeq`, and the equivalences into a
-- set form a set (`equivalences-into-a-set-form-a-set` of
-- SPT.Cubical.Foundation.Equivalences).
--
-- So the type of sets is a 1-type, a type whose identifications form sets
-- (`universe-of-sets-is-a-1-type`). An identification of two sets is one
-- of their underlying types together with one of their proofs of being a
-- set, and being a set is a proposition:
--
--   is-univalent-at X Y → is-set ((X , s) ＝ (Y , t)).

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Extensionality using (FunExt)
open import SPT.Cubical.Foundation.Isomorphisms using (Σ-＝-≅; ≅-sym)
open import SPT.Cubical.Foundation.Isomorphisms.Sets using (isomorphic-to-a-set)
open import SPT.Cubical.Foundation.Propositions
  using (is-set; propositions-are-sets)
open import SPT.Cubical.Foundation.Sets using
  (being-a-set-is-a-proposition; sums-of-sets-are-sets)
open import SPT.Cubical.Foundation.Univalence using
  (is-univalent-at; idtoeq; equivalence-to-isomorphism)
open import SPT.Cubical.Foundation.Equivalences using
  (equivalences-into-a-set-form-a-set)

------------------------------------------------------------------------
-- Identifications with a set, and the type of sets

module _ {ℓ : Level}
  (extensionality : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y) where

  identifications-with-a-set-form-a-set : (X Y : Set ℓ) → is-set Y →
    is-univalent-at X Y → is-set (X ＝ Y)
  identifications-with-a-set-form-a-set X Y set univalent =
    isomorphic-to-a-set
      (≅-sym (equivalence-to-isomorphism (idtoeq X Y , univalent)))
      (equivalences-into-a-set-form-a-set extensionality X Y set)

  -- The second components of an identification lie in a proposition.

  universe-of-sets-is-a-1-type : (σ τ : Σ (Set ℓ) is-set) →
    is-univalent-at (pr₁ σ) (pr₁ τ) → is-set (σ ＝ τ)
  universe-of-sets-is-a-1-type σ τ univalent =
    isomorphic-to-a-set (≅-sym (Σ-＝-≅ σ τ))
      (sums-of-sets-are-sets
        (identifications-with-a-set-form-a-set (pr₁ σ) (pr₁ τ) (pr₂ τ)
          univalent)
        (λ p → propositions-are-sets
          (propositions-are-sets
            (being-a-set-is-a-proposition extensionality (pr₁ τ))
            (transport is-set p (pr₂ σ)) (pr₂ τ))))
