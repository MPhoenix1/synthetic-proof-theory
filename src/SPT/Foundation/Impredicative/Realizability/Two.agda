{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Impredicative.Realizability.Two where

-- Realizers of the two points in a partial combinatory algebra at level
-- zero. Bit identifies a realizer of ₀ with k and a realizer of ₁ with
-- second, the two projection combinators.

open import SPT.Base
open import SPT.Foundation.Impredicative.Realizability.CombinatoryAlgebra
  using (Partial-Combinatory-Algebra; second)

module _ (𝔸 : Partial-Combinatory-Algebra lzero) where

  open Partial-Combinatory-Algebra 𝔸 using (Carrier; k)

  Bit : 𝟚 → Carrier → Set
  Bit ₀ r = r ＝ k
  Bit ₁ r = r ＝ second 𝔸
