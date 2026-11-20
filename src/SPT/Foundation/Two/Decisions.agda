{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Two.Decisions where

-- The Boolean reading of a decision: `decision-bit d` is ₁ when the
-- decision d gives a point and ₀ when it gives a refutation. Truth of the
-- bit gives the point back (`bit-gives-witness`), and a point makes the bit
-- true (`witness-gives-bit`).

open import SPT.Base
open import SPT.Foundation.Two.Truth using (is-₁)

module _ {ℓ : Level} {A : Set ℓ} where

  decision-bit : is-decidable A → 𝟚
  decision-bit (inl _) = ₁
  decision-bit (inr _) = ₀

  bit-gives-witness : (d : is-decidable A) → is-₁ (decision-bit d) → A
  bit-gives-witness (inl a) _ = a
  bit-gives-witness (inr n) ()

  witness-gives-bit : (d : is-decidable A) → A → is-₁ (decision-bit d)
  witness-gives-bit (inl _) a = ⋆
  witness-gives-bit (inr n) a = n a
