{-# OPTIONS --safe --without-K #-}

module SPT.IR.Universal.Morphism.Discriminator where

-- The fold out of the universal type computes, and the morphism laws
-- exclude maps into the fibers. On Universal.Discriminator's description
-- of a leaf or a binary node, the numbers with 0 at a leaf and a node one
-- above its child ₀ form a lawful algebra (`depth-step`, `depths`,
-- `depths-law`). Its fold counts two at Source.Discriminator's lopsided
-- node, by refl at variable extensionality (`fold-depth`). The map that is
-- 0 everywhere is not a morphism (`zero-not-morphism`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Induction.Initiality using (Section)

open import SPT.IR.Universal using (U)
open import SPT.IR.Universal.Discriminator using (γ; leaf; node; plain)
open import SPT.IR.Universal.Morphism using (fold)
open import SPT.IR.Universal.Source using (algebra; law)
open import SPT.IR.Universal.Source.Discriminator using (lopsided)
open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.IR.Description using (indexed; Shape)
open import SPT.IR.Morphism using (Morphism)

------------------------------------------------------------------------
-- The algebra of depths along child ₀

-- Every output is the point of 𝟙, so the law holds by refl.

depth-step : Shape γ (indexed ℕ (λ n → ⋆)) → ℕ
depth-step (₀ , z) = zero
depth-step (₁ , (g , z)) = suc (g ₀)

depths : Algebra lzero γ
depths = record
  { K = ℕ
  ; value = λ n → ⋆
  ; operation = depth-step
  }

depths-law : Law depths
depths-law z = refl

------------------------------------------------------------------------
-- The fold computes

-- Morphism's step assembles the shape of N at the identification of the
-- children's decodings that extensionality gives, so only the continuation
-- after a node waits on it. That continuation is the unit shape, and the
-- children and the tag compute.

fold-depth :
  (extensionality : (A : Set) → FunExt A (λ _ → 𝟙))
  (motive : (A : Set) (B : A → Set) → FunExt A B)
  → pr₁
      ( Section.valuation (fold extensionality motive depths depths-law)
          (node lopsided))
    ＝ suc (suc zero)
fold-depth extensionality motive = refl

------------------------------------------------------------------------
-- A map into the fibers that is not a morphism

-- At the node with two leaves the equation of a morphism puts one above
-- the value at its child ₀.

zero-not-morphism :
  (extensionality : (A : Set) → FunExt A (λ _ → 𝟙))
  (h : Morphism extensionality (algebra γ) depths (law γ) depths-law)
  → ((u : U γ) → pr₁ (Section.valuation h u) ＝ zero)
  → 𝟘
zero-not-morphism extensionality h zeros =
  zero-is-not-suc
    ( zeros (node plain) ⁻¹
    ∙ ( ap pr₁ (Section.equations h (₁ , (plain , lift ⋆)))
      ∙ ap suc (zeros leaf)))
