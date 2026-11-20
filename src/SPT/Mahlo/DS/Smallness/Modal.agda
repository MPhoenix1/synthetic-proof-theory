{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Smallness.Modal where

-- The smallness principle and the ambient Mahlo rule from their forms under a
-- modality. A small algebra with its law makes the raised fixed point of its
-- description essentially small, since generated parts of lawful algebras are
-- isomorphic (`raised-fixed-point-is-small`). So where essential smallness is
-- stable under a modality ○, small algebras under ○ give the principle
-- (`smallness-of-modal-algebras`) and reflections under ○ give the rule
-- (`rule-of-modal-rule`). Essential smallness is a proposition under
-- univalence, so it is stable at propositional truncation
-- (`smallness-is-truncation-stable`), and the rule follows from its truncation
-- (`smallness-of-mere-algebras`, `rule-of-mere-rule`):
--
--   (Π Ψ. ∥ Reflection Ψ ∥) → Mahlo, under univalence.
--
-- Nonclaim: the reflections obtained are the generated closures, up to
-- isomorphism; nothing here carries a degree.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Extensionality.Levels using (funext-below)
open import SPT.Foundation.Isomorphisms using
  (forward; backward; forward-backward)
open import SPT.Foundation.Modalities using
  ( Modality; is-stable; ○-map; truncation-modality
  ; propositions-are-truncation-stable)
open import SPT.Foundation.Size using
  (is-small; being-small-is-proposition)
open import SPT.Foundation.Truncations using (Truncation)
open import SPT.Foundation.Univalence using
  ( is-univalent; isomorphism-to-equivalence
  ; equivalence-to-isomorphism)
import SPT.Mahlo.Ambient as Ambient
import SPT.Mahlo.Specification as Specification

open import SPT.IR.Algebra using
  (Algebra; Law; identity; identity-β)
open import SPT.Mahlo.DS.Ambient using (mahlo)
open import SPT.IR.Description using (Desc)
import SPT.IR.Generated as Generated
open import SPT.IR.Morphism.Uniqueness using
  (generated-parts-are-isomorphic)
import SPT.IR.Polynomial as Polynomial
import SPT.Mahlo.DS.Realization as Realization
open import SPT.IR.Smallness using (Smallness)
open import SPT.IR.Smallness.Lowering using (Lowering)
  renaming (smallness to lowerings-give-smallness)

------------------------------------------------------------------------
-- An essentially small raised fixed point is a lowering

-- A small type with an equivalence to the raised fixed point, its points
-- decoded through the equivalence, is a lowering of the description.
lowering-of-small : {ℓ : Level} (γ : Desc {s = ℓ} (Set ℓ)) →
  is-small ℓ (Generated.G (identity γ)) → Lowering γ
lowering-of-small γ (K , e) =
  let E = equivalence-to-isomorphism e
  in record
    { carrier = K
    ; value = λ x → Generated.t (identity γ) (forward E x)
    ; down = backward E
    ; up = forward E
    ; down-β = λ u →
        ap (Generated.t (identity γ)) (forward-backward E u)
    ; up-β = λ x → refl
    }

------------------------------------------------------------------------
-- Small algebras and the raised fixed point

-- The raised fixed point is the generated part of the identity algebra, so
-- every small algebra with its law presents it on a small type.

module _ {ℓ : Level}
  (funext : (A : Set (lsuc ℓ)) (B : A → Set (lsuc ℓ)) → FunExt A B) where

  raised-fixed-point-is-small : (γ : Desc {s = ℓ} (Set ℓ))
    (M : Algebra ℓ γ) → Law M → is-small ℓ (Generated.G (identity γ))
  raised-fixed-point-is-small γ M law =
    Generated.G M ,
    isomorphism-to-equivalence
      ( generated-parts-are-isomorphic
          (funext-below (lsuc ℓ) funext)
          (Polynomial.lowered (lsuc ℓ) (funext-below (lsuc ℓ) funext))
          (funext-below (lsuc ℓ) funext)
          (funext-below (lsuc ℓ) funext)
          (funext-below (lsuc ℓ) funext)
          M
          law
          (identity γ)
          (identity-β γ))

  ----------------------------------------------------------------------
  -- Under a modality

  -- Mathematical shape: Π γ. ○ (small algebra of γ) → Smallness ℓ, when ○
  -- is stable at essential smallness.
  smallness-of-modal-algebras : (M : Modality (lsuc ℓ)) →
    ((X : Set (lsuc ℓ)) → is-stable M (is-small ℓ X)) →
    ( (γ : Desc {s = ℓ} (Set ℓ)) →
      Modality.○_ M (Σ (Algebra ℓ γ) Law)) →
    Smallness ℓ
  smallness-of-modal-algebras M stable h =
    lowerings-give-smallness
      (λ A → funext-below (lsuc ℓ) funext A (λ _ → Set ℓ))
      ( λ γ →
          lowering-of-small γ
            ( stable (Generated.G (identity γ))
                ( ○-map M
                    (λ p → raised-fixed-point-is-small γ (pr₁ p) (pr₂ p))
                    (h γ))))

  -- Mathematical shape: (Π Ψ. ○ (Reflection Ψ)) → Mahlo, when ○ is stable at
  -- essential smallness.
  rule-of-modal-rule : (M : Modality (lsuc ℓ)) →
    ((X : Set (lsuc ℓ)) → is-stable M (is-small ℓ X)) →
    ( (Ψ : Ambient.Operator ℓ) →
      Modality.○_ M (Specification.Reflection (Ambient.formers ℓ) Ψ)) →
    Specification.Mahlo (Ambient.formers ℓ)
  rule-of-modal-rule M stable h =
    mahlo
      (λ X → funext-below (lsuc ℓ) funext X (λ _ → Set ℓ))
      ( smallness-of-modal-algebras M stable
          ( λ γ →
              ○-map M
                ( λ r →
                    Realization.algebra γ
                      (Specification.Reflection.closure r)
                    , Realization.law γ
                        (Specification.Reflection.closure r))
                (h (Realization.operator γ))))

------------------------------------------------------------------------
-- At propositional truncation

module _ {ℓ : Level}
  (funext : (A : Set (lsuc ℓ)) (B : A → Set (lsuc ℓ)) → FunExt A B)
  (t : Truncation (lsuc ℓ)) (u : is-univalent ℓ) where

  smallness-is-truncation-stable : (X : Set (lsuc ℓ)) →
    is-stable (truncation-modality t) (is-small ℓ X)
  smallness-is-truncation-stable X =
    propositions-are-truncation-stable t
      (being-small-is-proposition funext u X)

  smallness-of-mere-algebras :
    ( (γ : Desc {s = ℓ} (Set ℓ)) →
      Truncation.∥_∥ t (Σ (Algebra ℓ γ) Law)) →
    Smallness ℓ
  smallness-of-mere-algebras =
    smallness-of-modal-algebras funext (truncation-modality t)
      smallness-is-truncation-stable

  -- Mathematical shape: (Π Ψ. ∥ Reflection Ψ ∥) → Mahlo, under univalence.
  rule-of-mere-rule :
    ( (Ψ : Ambient.Operator ℓ) →
      Truncation.∥_∥ t (Specification.Reflection (Ambient.formers ℓ) Ψ)) →
    Specification.Mahlo (Ambient.formers ℓ)
  rule-of-mere-rule =
    rule-of-modal-rule funext (truncation-modality t)
      smallness-is-truncation-stable
