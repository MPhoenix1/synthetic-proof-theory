{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.ExactOrder.Boolean where

-- Boolean orders: countable well-orders given by Boolean data on ℕ.  A
-- Boolean order is a decidable set of points and a Boolean strict order,
-- transitive, well founded, and trichotomous on the points.  The relation
-- of an exact order is type-valued, so exact orders form a large type;
-- Boolean orders form a small one (Set).  Each Boolean order is an exact
-- order on its points (order), which it enumerates by their own indices.
-- Normalization.Boolean gives every presentation a Boolean order.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Accessibility using (is-well-founded)
open import SPT.Cubical.Foundation.Two.Truth using (is-₁; is-₁-is-proposition)
open import SPT.Cubical.Foundation.WellFounded.Pullback using
  ( pullback-is-well-founded )

import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order

------------------------------------------------------------------------
-- Boolean orders

-- Mathematical shape:
--
--   BooleanOrder ≃ Σ(point : ℕ → 𝟚). Σ(less : ℕ → ℕ → 𝟚).
--     Transitive(less) × WellFounded(less)
--     × Π i j. point i → point j → less i j + (i = j + less j i).
--
-- Every field is small.  Trichotomy is asked only of points; off the
-- points `less` is unconstrained.
record BooleanOrder : Set where
  field
    point : ℕ → 𝟚
    less : ℕ → ℕ → 𝟚
    trans : ∀ {i j k} → is-₁ (less i j) → is-₁ (less j k) → is-₁ (less i k)
    wf : is-well-founded (λ i j → is-₁ (less i j))
    compare : (i j : ℕ) → is-₁ (point i) → is-₁ (point j)
      → is-₁ (less i j) ⊎ ((i ＝ j) ⊎ is-₁ (less j i))

-- The points of a Boolean order: indices together with their membership.
Points : BooleanOrder → Set
Points O = Σ ℕ (λ n → is-₁ (BooleanOrder.point O n))

-- A point is determined by its index, since each is-₁ b is a proposition.
point-≡ : (O : BooleanOrder) {a b : Points O}
  → pr₁ a ＝ pr₁ b → a ＝ b
point-≡ O {i , s} {.i , t} refl =
  ap (i ,_) (is-₁-is-proposition (BooleanOrder.point O i) s t)

------------------------------------------------------------------------
-- The exact order of a Boolean order

private
  -- The partial sequence that lists n exactly when n is a point.
  select : {A : Set} (b : 𝟚) → (is-₁ b → A) → Maybe A
  select ₁ f = just (f ⋆)
  select ₀ f = nothing

  select-hit : {A : Set} (b : 𝟚) (f : is-₁ b → A) (t : is-₁ b)
    → select b f ＝ just (f t)
  select-hit ₁ f t = refl

order : (O : BooleanOrder) → Order.Order (Points O)
order O = record
  { _<_ = λ a b → is-₁ (BooleanOrder.less O (pr₁ a) (pr₁ b))
  ; trans = λ {a} {b} {c} →
      BooleanOrder.trans O {pr₁ a} {pr₁ b} {pr₁ c}
  ; wf = pullback-is-well-founded pr₁
      (λ i j → is-₁ (BooleanOrder.less O i j))
      (BooleanOrder.wf O)
  ; compare = comparison
  ; enum = λ n → select (BooleanOrder.point O n) (λ t → n , t)
  ; covers = λ a →
      pr₁ a
      , select-hit (BooleanOrder.point O (pr₁ a))
          (λ t → pr₁ a , t) (pr₂ a)
  }
  where
    comparison : (a b : Points O)
      → is-₁ (BooleanOrder.less O (pr₁ a) (pr₁ b))
        ⊎ ((a ＝ b) ⊎ is-₁ (BooleanOrder.less O (pr₁ b) (pr₁ a)))
    comparison (i , s) (j , t) with BooleanOrder.compare O i j s t
    ... | inl p = inl p
    ... | inr (inl e) = inr (inl (point-≡ O e))
    ... | inr (inr p) = inr (inr p)
