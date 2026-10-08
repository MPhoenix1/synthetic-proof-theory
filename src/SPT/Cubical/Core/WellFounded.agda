{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.WellFounded where

-- Accessibility and well-foundedness for type-valued relations, and the
-- induction principle along an accessibility witness.

open import Agda.Primitive using (Level; _⊔_)
open import Relation.Nullary.Negation using (¬_)

------------------------------------------------------------------------
-- Accessibility / well-foundedness

data Acc
  {ℓ ℓr : Level}
  {A : Set ℓ}
  (_<_ : A → A → Set ℓr)
  (x : A)
  : Set (ℓ ⊔ ℓr)
  where
  acc : ((y : A) → y < x → Acc _<_ y) → Acc _<_ x


WellFounded :
  {ℓ ℓr : Level} {A : Set ℓ} →
  (A → A → Set ℓr) →
  Set (ℓ ⊔ ℓr)
WellFounded _<_ = ∀ x → Acc _<_ x

acc-ind :
  {ℓ ℓr ℓp : Level}
  {A : Set ℓ}
  {_<_ : A → A → Set ℓr} →
  (P : A → Set ℓp) →
  ((x : A) → ((y : A) → y < x → P y) → P x) →
  (x : A) → Acc _<_ x → P x
acc-ind P step x (acc smaller) =
  step x (λ y y<x → acc-ind P step y (smaller y y<x))


predecessorAcc :
    ∀ {ℓ ℓr}
      {A : Set ℓ}
      {_<_ : A → A → Set ℓr}
      {x : A}
  → Acc _<_ x
  → (y : A)
  → y < x
  → Acc _<_ y
predecessorAcc (acc smaller) y y<x = smaller y y<x


------------------------------------------------------------------------
-- Generic accessibility laws

acc↛loop :
    ∀ {ℓ ℓr : Level}
      {A : Set ℓ}
      {R : A → A → Set ℓr}
      {x : A}
  → Acc R x
  → ¬ R x x
acc↛loop (acc smaller) loop =
  acc↛loop (smaller _ loop) loop

