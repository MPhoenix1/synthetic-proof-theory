{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Impredicative.WeakResizing where

-- Weak presentations and weak resizing. A type has a weak presentation at a
-- level when a type of that level maps to it and back
-- (`Weak-Presentation`):
--
--   Weak-Presentation ℓ X = Σ (Q : Set ℓ). (Q → X) × (X → Q).
--
-- No inverse law is asked. Weak resizing is the resizing of
-- Impredicative.Classification for the family of all types of one level,
--
--   Resizing (λ (X : Set ℓ) → X)
--     = Π (P : Set (ℓ + 1)). Σ (I : Set ℓ). (P → I) × (I → P),
--
-- and SPT writes it as that instance, never as a definition of its own. It
-- gives every type of the next level a weak presentation, and conversely
-- (`weak-resizing-presents`, `presentations-give-weak-resizing`). Under
-- double negation every type is presented by the unit or the empty type
-- (`every-type-is-presented-under-double-negation`), so that statement alone
-- has no content.

open import SPT.Base
open import SPT.Foundation.Impredicative.Classification using (Resizing)

------------------------------------------------------------------------
-- Weak presentations

-- Mathematical shape: Σ (Q : Set ℓ). (Q → X) × (X → Q).
Weak-Presentation : (ℓ : Level) {κ : Level} → Set κ → Set (lsuc ℓ ⊔ κ)
Weak-Presentation ℓ X = Σ (Set ℓ) (λ Q → (Q → X) × (X → Q))

-- Under double negation the unit type or the empty type presents any type.
every-type-is-presented-under-double-negation : (ℓ : Level) {κ : Level}
  (X : Set κ) → ¬ ¬ Weak-Presentation ℓ X
every-type-is-presented-under-double-negation ℓ X k =
  k ( Lift ℓ 𝟘
    , (λ q → 𝟘-elim (lower q))
    , (λ x → 𝟘-elim (k (Lift ℓ 𝟙 , (λ _ → x) , (λ _ → lift ⋆)))))


------------------------------------------------------------------------
-- Weak resizing

-- The two forms differ only in the order of the two maps.

module _ {ℓ : Level} where

  -- Mathematical shape: weak resizing presents every type of level ℓ + 1.
  weak-resizing-presents : Resizing (λ (X : Set ℓ) → X) →
    (P : Set (lsuc ℓ)) → Weak-Presentation ℓ P
  weak-resizing-presents r P = pr₁ (r P) , pr₂ (pr₂ (r P)) , pr₁ (pr₂ (r P))

  presentations-give-weak-resizing :
    ((P : Set (lsuc ℓ)) → Weak-Presentation ℓ P) →
    Resizing (λ (X : Set ℓ) → X)
  presentations-give-weak-resizing w P =
    pr₁ (w P) , pr₂ (pr₂ (w P)) , pr₁ (pr₂ (w P))
