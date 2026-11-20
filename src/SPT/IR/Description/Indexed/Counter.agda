{-# OPTIONS --safe --without-K #-}

module SPT.IR.Description.Indexed.Counter where

-- A general code whose constructors land at computed indices (`counter`):
-- a seed at ₀ decoding to 0, and a step taking a child at any index j and
-- landing at the parity of its decoding's successor, decoding to that
-- successor (`branch`, with the parity of a number, `parity`, `flip`).
-- It is the example of the general rules on the universal family
-- (IR.Indexed.General.Discriminator) and on the generated part of an
-- explicit algebra (IR.Polynomial.General.Discriminator); it is
-- stated here, with no induction–recursion, so that both read one code.

open import SPT.Base
open import SPT.IR.Description.Indexed using (General; ι; σ; δ)

flip : 𝟚 → 𝟚
flip ₀ = ₁
flip ₁ = ₀

parity : ℕ → 𝟚
parity zero = ₀
parity (suc n) = flip (parity n)

-- The seed at ₀, and the step at the parity of the child's successor.

branch : 𝟚 → General lzero lzero 𝟚 (λ _ → ℕ)
branch ₀ = ι (₀ , 0)
branch ₁ =
  σ 𝟚 (λ j → δ 𝟙 (λ _ → j) (λ g → ι (parity (suc (g ⋆)) , suc (g ⋆))))

counter : General lzero lzero 𝟚 (λ _ → ℕ)
counter = σ 𝟚 branch
