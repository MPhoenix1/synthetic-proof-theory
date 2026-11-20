{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Two.Connectives where

-- Conjunction, disjunction and negation of bits (`_∧_`, `_∨_`, `not`), read
-- through the truth family of Two.Truth: a conjunction is true exactly when
-- both conjuncts are (`∧-left`, `∧-right`, `∧-intro`), and a negation
-- exactly when the bit is not (`not-intro`, `not-elim`):
--
--   is-₁ (a ∧ b) ↔ is-₁ a × is-₁ b,   is-₁ (not b) ↔ ¬ is-₁ b.
--
-- Two bits with logically equivalent truth are equal
-- (`truth-determines-bit`). The same laws hold for the values of the
-- connectives (`∧-＝-₁-split`, `∧-＝-₁-join`, `not-＝-₁`, `not-＝-₀`), a
-- disjunction is ₁ exactly when a disjunct is (`∨-＝-₁-split`,
-- `∨-＝-₁-left`, `∨-＝-₁-right`), ₀ absorbs and ₁ is a unit on the right of
-- a conjunction (`∧-₀-absorbs-right`, `∧-₁-unit-right`), and negation is
-- involutive (`not-is-involutive`):
--
--   a ∧ b = ₁ ↔ a = ₁ × b = ₁,   a ∨ b = ₁ ↔ a = ₁ ⊎ b = ₁,
--   a ∧ ₀ = ₀,   a ∧ ₁ = a,
--   not a = ₁ → a = ₀,   not a = ₀ → a = ₁,   not (not b) = b.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Two.Truth using (is-₁)

------------------------------------------------------------------------
-- The connectives

infixr 54 _∧_
infixr 52 _∨_

_∧_ : 𝟚 → 𝟚 → 𝟚
₀ ∧ b = ₀
₁ ∧ b = b

_∨_ : 𝟚 → 𝟚 → 𝟚
₀ ∨ b = b
₁ ∨ b = ₁

not : 𝟚 → 𝟚
not ₀ = ₁
not ₁ = ₀

------------------------------------------------------------------------
-- Their truth

∧-left : (a b : 𝟚) → is-₁ (a ∧ b) → is-₁ a
∧-left ₀ b ()
∧-left ₁ b p = ⋆

∧-right : (a b : 𝟚) → is-₁ (a ∧ b) → is-₁ b
∧-right ₀ b ()
∧-right ₁ b p = p

∧-intro : (a b : 𝟚) → is-₁ a → is-₁ b → is-₁ (a ∧ b)
∧-intro ₀ b () q
∧-intro ₁ b p q = q

not-intro : (b : 𝟚) → ¬ is-₁ b → is-₁ (not b)
not-intro ₀ p = ⋆
not-intro ₁ p = p ⋆

not-elim : (b : 𝟚) → is-₁ (not b) → ¬ is-₁ b
not-elim ₀ q ()
not-elim ₁ () p

truth-determines-bit : (a b : 𝟚) → (is-₁ a → is-₁ b) → (is-₁ b → is-₁ a) →
  a ＝ b
truth-determines-bit ₀ ₀ f g = refl
truth-determines-bit ₀ ₁ f g = 𝟘-elim (g ⋆)
truth-determines-bit ₁ ₀ f g = 𝟘-elim (f ⋆)
truth-determines-bit ₁ ₁ f g = refl

------------------------------------------------------------------------
-- Their values

∧-＝-₁-split : (a b : 𝟚) → a ∧ b ＝ ₁ → (a ＝ ₁) × (b ＝ ₁)
∧-＝-₁-split ₀ b ()
∧-＝-₁-split ₁ ₀ ()
∧-＝-₁-split ₁ ₁ p = refl , refl

∧-＝-₁-join : {a b : 𝟚} → a ＝ ₁ → b ＝ ₁ → a ∧ b ＝ ₁
∧-＝-₁-join refl refl = refl

∨-＝-₁-split : (a b : 𝟚) → a ∨ b ＝ ₁ → (a ＝ ₁) ⊎ (b ＝ ₁)
∨-＝-₁-split ₀ b p = inr p
∨-＝-₁-split ₁ b p = inl refl

∨-＝-₁-left : (a b : 𝟚) → a ＝ ₁ → a ∨ b ＝ ₁
∨-＝-₁-left ₀ b ()
∨-＝-₁-left ₁ b p = refl

∨-＝-₁-right : (a b : 𝟚) → b ＝ ₁ → a ∨ b ＝ ₁
∨-＝-₁-right ₀ b p = p
∨-＝-₁-right ₁ b p = refl

∧-₀-absorbs-right : (a : 𝟚) → a ∧ ₀ ＝ ₀
∧-₀-absorbs-right ₀ = refl
∧-₀-absorbs-right ₁ = refl

∧-₁-unit-right : (a : 𝟚) → a ∧ ₁ ＝ a
∧-₁-unit-right ₀ = refl
∧-₁-unit-right ₁ = refl

not-＝-₁ : (a : 𝟚) → not a ＝ ₁ → a ＝ ₀
not-＝-₁ ₀ p = refl
not-＝-₁ ₁ ()

not-＝-₀ : (a : 𝟚) → not a ＝ ₀ → a ＝ ₁
not-＝-₀ ₀ ()
not-＝-₀ ₁ p = refl

not-is-involutive : (b : 𝟚) → not (not b) ＝ b
not-is-involutive ₀ = refl
not-is-involutive ₁ = refl
