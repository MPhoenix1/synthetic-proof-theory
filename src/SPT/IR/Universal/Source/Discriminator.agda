{-# OPTIONS --safe --without-K #-}

module SPT.IR.Universal.Source.Discriminator where

-- Source induction keeps the children of a node apart. On
-- Universal.Discriminator's description of a leaf or a binary node, take
-- the node whose child ₀ is a node and whose child ₁ a leaf (`lopsided`).
-- A step reading the position of child ₀ counts two there, one reading
-- child ₁ counts one, by refl (`left`, `left-depth`, `right`,
-- `right-depth`). Reading the tuple hypotheses with the children
-- exchanged is a well-typed conversion at a constant motive, and it fails
-- the law of `positioned-calls` (`exchanged`, `exchanged-calls-fail`).

open import SPT.Base

open import SPT.IR.Universal using (U; value; Std-Hyp; std-calls)
open import SPT.IR.Universal.Discriminator using
  (γ; leaf; node; plain; depth)
open import SPT.IR.Universal.Induction using (intro)
open import SPT.IR.Universal.Source using (source)
open import SPT.IR.Description using (indexed; Shape)
open import SPT.IR.Restriction using (Position; input)

------------------------------------------------------------------------
-- A node with different children

lopsided : 𝟚 → U γ
lopsided ₀ = node plain
lopsided ₁ = leaf

Count : U γ → Set
Count u = ℕ

------------------------------------------------------------------------
-- Steps reading one position

-- The positions of a node are its two children, then none. Each step
-- counts one at a node and continues at the child its position names.

left : Argument-Step (input γ (indexed (U γ) (value γ))) (intro γ) Count
left (₀ , z) h = zero
left (₁ , (f , z)) h = suc (h (inl ₀))

right : Argument-Step (input γ (indexed (U γ) (value γ))) (intro γ) Count
right (₀ , z) h = zero
right (₁ , (f , z)) h = suc (h (inl ₁))

left-depth : source γ lzero Count left (node lopsided) ＝ suc (suc zero)
left-depth = refl

right-depth : source γ lzero Count right (node lopsided) ＝ suc zero
right-depth = refl

------------------------------------------------------------------------
-- Exchanged children fail the law of the calls

-- At the constant motive the hypothesis at one child has the type of the
-- other's, so reading child ₁ at the position of child ₀ is well typed.
-- The law of `positioned-calls` at native depth then asks the depth of the
-- leaf to be the depth of the node.

exchanged :
  (z : Shape γ (indexed (U γ) (value γ)))
  → Std-Hyp γ (U γ) (value γ) Count z
  → (p : Position γ (indexed (U γ) (value γ)) z)
  → Count (input γ (indexed (U γ) (value γ)) z p)
exchanged (₀ , z) t (lift ())
exchanged (₁ , (f , z)) (g , t) (inl ₀) = g ₁
exchanged (₁ , (f , z)) (g , t) (inl ₁) = g ₀
exchanged (₁ , (f , z)) (g , t) (inr (lift ()))

exchanged-calls-fail :
  ( (h : (u : U γ) → Count u) (z : Shape γ (indexed (U γ) (value γ)))
    (p : Position γ (indexed (U γ) (value γ)) z)
    → exchanged z (std-calls γ (U γ) (value γ) Count h z) p
      ＝ h (input γ (indexed (U γ) (value γ)) z p))
  → 𝟘
exchanged-calls-fail calls =
  zero-is-not-suc (calls depth (₁ , (lopsided , lift ⋆)) (inl ₀))
