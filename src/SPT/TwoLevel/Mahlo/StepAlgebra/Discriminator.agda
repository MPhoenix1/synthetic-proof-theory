{-# OPTIONS --safe --without-K --two-level #-}

module SPT.TwoLevel.Mahlo.StepAlgebra.Discriminator where

-- Induction–recursion gives a labelled algebra of the ambient formers.
-- Code and decode satisfy each label law by computation, giving universe
-- and hence the strict ambient Mahlo rule (mahlo).

open import SPT.Base
open import SPT.TwoLevel.Coherence using (same)
open import SPT.Mahlo.Specification using (Operator)
import SPT.Mahlo.Ambient as Ambient
open import SPT.Foundation.Tree.W using (W)
open import SPT.TwoLevel.Mahlo using (Strict-Mahlo)
open import SPT.TwoLevel.Mahlo.StepAlgebra using (Labelled; ambient-mahlo)

------------------------------------------------------------------------
-- The universe of the step at an operator

module _ {ℓ : Level} (Ψ : Operator (λ (A : Set ℓ) → A)) where

  data Code : Set ℓ
  decode : Code → Set ℓ

  data Code where
    empty unit two natural : Code
    product sum tree result : Σ Code (λ a → decode a → Code) → Code
    identity : (a : Code) → decode a → decode a → Code
    branch :
      (F : Σ Code (λ a → decode a → Code))
      → pr₁ (Ψ (decode (pr₁ F) , (λ x → decode (pr₂ F x)))) → Code

  decode empty = Lift ℓ 𝟘
  decode unit = Lift ℓ 𝟙
  decode two = Lift ℓ 𝟚
  decode natural = Lift ℓ ℕ
  decode (product (a , b)) = (x : decode a) → decode (b x)
  decode (sum (a , b)) = Σ (decode a) (λ x → decode (b x))
  decode (tree (a , b)) = W (decode a) (λ x → decode (b x))
  decode (result (a , b)) = pr₁ (Ψ (decode a , (λ x → decode (b x))))
  decode (identity a x y) = x ＝ y
  decode (branch (a , b) y) = pr₂ (Ψ (decode a , (λ x → decode (b x)))) y

------------------------------------------------------------------------
-- The labelled algebra and the strict ambient Mahlo rule

module _ (ℓ : Level) where

  universe : Labelled (Ambient.formers ℓ)
  universe = record
    { Carrier = Code
    ; readout = decode
    ; empty = λ Ψ → empty
    ; unit = λ Ψ → unit
    ; two = λ Ψ → two
    ; natural = λ Ψ → natural
    ; product = λ Ψ F → product F
    ; sum = λ Ψ F → sum F
    ; tree = λ Ψ F → tree F
    ; result = λ Ψ F → result F
    ; identity = λ Ψ a x y → identity a x y
    ; branch = λ Ψ F y → branch F y
    ; empty-β = same
    ; unit-β = same
    ; two-β = same
    ; natural-β = same
    ; product-β = same
    ; sum-β = same
    ; tree-β = same
    ; result-β = same
    ; identity-β = same
    ; branch-β = same
    }

  mahlo : Strict-Mahlo (Ambient.formers ℓ)
  mahlo = ambient-mahlo universe
