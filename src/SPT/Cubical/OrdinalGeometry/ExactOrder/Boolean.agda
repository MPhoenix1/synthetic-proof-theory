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

open import Data.Bool.Base using (Bool; true; false; T)
open import Data.Bool.Properties using (T-irrelevant)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import SPT.Cubical.Core.WellFounded using (WellFounded)
open import SPT.Cubical.Core.WellFounded.Pullback using (pullback-wf)
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
    point : ℕ → Bool
    less : ℕ → ℕ → Bool
    trans : ∀ {i j k} → T (less i j) → T (less j k) → T (less i k)
    wf : WellFounded (λ i j → T (less i j))
    compare : (i j : ℕ) → T (point i) → T (point j)
      → T (less i j) ⊎ (i ≡ j ⊎ T (less j i))

-- The points of a Boolean order: indices together with their membership.
Points : BooleanOrder → Set
Points O = Σ ℕ (λ n → T (BooleanOrder.point O n))

-- A point is determined by its index, since each T b is a proposition.
point-≡ : (O : BooleanOrder) {a b : Points O}
  → proj₁ a ≡ proj₁ b → a ≡ b
point-≡ O {i , s} {.i , t} refl = cong (i ,_) (T-irrelevant s t)

------------------------------------------------------------------------
-- The exact order of a Boolean order

private
  -- The partial sequence that lists n exactly when n is a point.
  select : {A : Set} (b : Bool) → (T b → A) → Maybe A
  select true f = just (f tt)
  select false f = nothing

  select-hit : {A : Set} (b : Bool) (f : T b → A) (t : T b)
    → select b f ≡ just (f t)
  select-hit true f t = refl

order : (O : BooleanOrder) → Order.Order (Points O)
order O = record
  { _<_ = λ a b → T (BooleanOrder.less O (proj₁ a) (proj₁ b))
  ; trans = λ {a} {b} {c} →
      BooleanOrder.trans O {proj₁ a} {proj₁ b} {proj₁ c}
  ; wf = pullback-wf {rank = proj₁}
      {_<_ = λ i j → T (BooleanOrder.less O i j)}
      (BooleanOrder.wf O)
  ; compare = comparison
  ; enum = λ n → select (BooleanOrder.point O n) (λ t → n , t)
  ; covers = λ a →
      proj₁ a
      , select-hit (BooleanOrder.point O (proj₁ a))
          (λ t → proj₁ a , t) (proj₂ a)
  }
  where
    comparison : (a b : Points O)
      → T (BooleanOrder.less O (proj₁ a) (proj₁ b))
        ⊎ (a ≡ b ⊎ T (BooleanOrder.less O (proj₁ b) (proj₁ a)))
    comparison (i , s) (j , t) with BooleanOrder.compare O i j s t
    ... | inj₁ p = inj₁ p
    ... | inj₂ (inj₁ e) = inj₂ (inj₁ (point-≡ O e))
    ... | inj₂ (inj₂ p) = inj₂ (inj₂ p)
