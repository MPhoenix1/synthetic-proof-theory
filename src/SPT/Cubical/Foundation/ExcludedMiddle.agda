{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.ExcludedMiddle where

-- Excluded middle for the propositions of one level, as a hypothesis
-- (`Excluded-Middle`):
--
--   Excluded-Middle ℓ = Π (P : Set ℓ). is-proposition P → P ⊎ ¬ P.
--
-- It descends a level, through lifting (`excluded-middle-descends`). A
-- decided proposition of level ℓ + 1 is small at ℓ, presented by the unit
-- or the empty type (`decided-propositions-are-small`), so excluded middle
-- at ℓ + 1 gives propositional resizing at ℓ
-- (`excluded-middle-gives-resizing`), and with function extensionality at
-- ℓ + 1 a truncation at ℓ (`excluded-middle-gives-truncation`, through
-- Impredicative.PropositionalResizing.Truncation). At one level, excluded
-- middle makes the two truth values, indexed by 𝟚, a classifier of
-- propositions (`truth-value`, `decided-is-classified`,
-- `classifier-from-excluded-middle`;
-- Impredicative.PropositionalClassifier's `Propositional-Classifier`).

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Extensionality using (FunExt)
open import SPT.Cubical.Foundation.Isomorphisms using (_≅_)
open import SPT.Cubical.Foundation.Propositions using (is-proposition)
open import SPT.Cubical.Foundation.Impredicative.PropositionalResizing using
  (Propositional-Resizing)
open import SPT.Cubical.Foundation.Impredicative.PropositionalClassifier using
  (Propositional-Classifier)
open import SPT.Cubical.Foundation.Size using (is-small)
open import SPT.Cubical.Foundation.Truncations using (Truncation)
open import
  SPT.Cubical.Foundation.Impredicative.PropositionalResizing.Truncation using
  (truncation-from-resizing)
open import SPT.Cubical.Foundation.Univalence using (isomorphism-to-equivalence)

------------------------------------------------------------------------
-- Excluded middle

-- Mathematical shape: Π (P : Set ℓ). is-proposition P → P ⊎ ¬ P.
Excluded-Middle : (ℓ : Level) → Set (lsuc ℓ)
Excluded-Middle ℓ = (P : Set ℓ) → is-proposition P → P ⊎ ¬ P

-- Excluded middle descends a level, through lifting.
excluded-middle-descends : (ℓ : Level) → Excluded-Middle (lsuc ℓ) →
  Excluded-Middle ℓ
excluded-middle-descends ℓ lem P p =
  cases (λ x → inl (lower x)) (λ n → inr (λ x → n (lift x)))
    (lem (Lift (lsuc ℓ) P) (λ x y → ap lift (p (lower x) (lower y))))

------------------------------------------------------------------------
-- Decided propositions are small

module _ (ℓ : Level) {P : Set (lsuc ℓ)} where

  -- A proposition with a point is presented by the unit type.
  unit-presents-a-point : is-proposition P → P → Lift ℓ 𝟙 ≅ P
  unit-presents-a-point p x = record
    { forward = λ _ → x
    ; backward = λ _ → lift ⋆
    ; backward-forward = λ u → refl
    ; forward-backward = λ y → p x y
    }

  -- A refuted type is presented by the empty type.
  empty-presents-a-refutation : ¬ P → Lift ℓ 𝟘 ≅ P
  empty-presents-a-refutation n = record
    { forward = λ z → 𝟘-elim (lower z)
    ; backward = λ y → 𝟘-elim (n y)
    ; backward-forward = λ z → 𝟘-elim (lower z)
    ; forward-backward = λ y → 𝟘-elim (n y)
    }

  decided-propositions-are-small : is-proposition P → P ⊎ ¬ P →
    is-small ℓ P
  decided-propositions-are-small p (inl x) =
    Lift ℓ 𝟙 , isomorphism-to-equivalence (unit-presents-a-point p x)
  decided-propositions-are-small p (inr n) =
    Lift ℓ 𝟘 , isomorphism-to-equivalence (empty-presents-a-refutation n)

------------------------------------------------------------------------
-- Resizing and truncation

-- Mathematical shape: excluded middle at ℓ + 1 gives propositional resizing
-- at ℓ.
excluded-middle-gives-resizing : (ℓ : Level) → Excluded-Middle (lsuc ℓ) →
  Propositional-Resizing ℓ
excluded-middle-gives-resizing ℓ lem P p =
  decided-propositions-are-small ℓ p (lem P p)

-- With function extensionality at ℓ + 1, excluded middle there gives a
-- truncation at ℓ.
excluded-middle-gives-truncation : (ℓ : Level) →
  ((A : Set (lsuc ℓ)) (B : A → Set (lsuc ℓ)) → FunExt A B) →
  Excluded-Middle (lsuc ℓ) → Truncation ℓ
excluded-middle-gives-truncation ℓ funext lem =
  truncation-from-resizing funext (excluded-middle-gives-resizing ℓ lem)

------------------------------------------------------------------------
-- A classifier of propositions

-- The truth values of level ℓ, indexed by the two-point type.
truth-value : (ℓ : Level) → Lift ℓ 𝟚 → Set ℓ
truth-value ℓ (lift ₀) = Lift ℓ 𝟘
truth-value ℓ (lift ₁) = Lift ℓ 𝟙

decided-is-classified : (ℓ : Level) {P : Set ℓ} → P ⊎ ¬ P →
  Σ (Lift ℓ 𝟚) (λ j → (P → truth-value ℓ j) × (truth-value ℓ j → P))
decided-is-classified ℓ (inl p) =
  lift ₁ , (λ _ → lift ⋆) , (λ _ → p)
decided-is-classified ℓ (inr n) =
  lift ₀ , (λ p → 𝟘-elim (n p)) , (λ z → 𝟘-elim (lower z))

-- Mathematical shape: excluded middle for propositions gives a classifier with
-- proxies in 𝟚.
classifier-from-excluded-middle : (ℓ : Level) → Excluded-Middle ℓ →
  Propositional-Classifier ℓ
classifier-from-excluded-middle ℓ decide = record
  { proxies = Lift ℓ 𝟚
  ; proxy = truth-value ℓ
  ; classify = λ P p → decided-is-classified ℓ (decide P p)
  }
