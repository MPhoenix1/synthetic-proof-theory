{-# OPTIONS --safe --without-K #-}

module SPT.IR.Universal.Translation.Discriminator where

-- The action of a translation on the universal type is not the identity.
-- On Universal.Discriminator's description of a leaf or a binary node,
-- the translation exchanging the two children of every node (`other`,
-- `mirror`) acts on the universal type by its fold into the universal
-- type itself (`mirrored`). Source.Discriminator's lopsided node has
-- depth two along child ₀, its image depth one, and its image along the
-- composite of the exchange with itself depth two again, by refl at
-- variable extensionality (`original-depth`, `mirrored-depth`,
-- `twice-mirrored-depth`). So the fold along the exchange moves a tree
-- (`mirror-moves`), where the fold along the identity translation keeps
-- every tree (Translation's `fold-identity`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Induction.Initiality using (Section)

open import SPT.IR.Universal using (U)
open import SPT.IR.Universal.Discriminator using (γ; node; depth)
open import SPT.IR.Universal.Source using (algebra; law)
open import SPT.IR.Universal.Source.Discriminator using (lopsided)
open import SPT.IR.Universal.Translation using (fold)
open import SPT.IR.Description using (indexed; Shape)
open import SPT.IR.Restriction using (Position; input)
open import SPT.IR.Translation using (Translation; compose)

------------------------------------------------------------------------
-- Exchanging the children of a node

-- On shapes over the outputs a leaf stays, and a node reads its children
-- in the other order; each position of the image reads back the other
-- child, whose output is the same by computation.

other : 𝟚 → 𝟚
other ₀ = ₁
other ₁ = ₀

mirror-shape :
  Shape γ (indexed 𝟙 (λ e → e)) → Shape γ (indexed 𝟙 (λ e → e))
mirror-shape (₀ , z) = ₀ , z
mirror-shape (₁ , (g , z)) = ₁ , ((λ b → g (other b)) , z)

mirror-back :
  (c : Shape γ (indexed 𝟙 (λ e → e)))
  → Position γ (indexed 𝟙 (λ e → e)) (mirror-shape c)
  → Position γ (indexed 𝟙 (λ e → e)) c
mirror-back (₀ , z) (lift ())
mirror-back (₁ , (g , z)) (inl b) = inl (other b)
mirror-back (₁ , (g , z)) (inr (lift ()))

mirror-inputs :
  (c : Shape γ (indexed 𝟙 (λ e → e)))
  (q : Position γ (indexed 𝟙 (λ e → e)) (mirror-shape c))
  → input γ (indexed 𝟙 (λ e → e)) c (mirror-back c q)
    ＝ input γ (indexed 𝟙 (λ e → e)) (mirror-shape c) q
mirror-inputs (₀ , z) (lift ())
mirror-inputs (₁ , (g , z)) (inl b) = refl
mirror-inputs (₁ , (g , z)) (inr (lift ()))

mirror : Translation (λ e → e) γ γ
mirror = record
  { shape = mirror-shape
  ; back = mirror-back
  ; inputs = mirror-inputs
  ; output = λ c → refl
  }

------------------------------------------------------------------------
-- The action on the lopsided node

-- The fold along a translation assembles the translated shape at the
-- identification of decodings that extensionality gives; only the unit
-- continuation after a node waits on it, so depths compute.

mirrored :
  (arities : (A : Set) (B : A → Set) → FunExt A B)
  (motive : (A : Set) (B : A → Set) → FunExt A B)
  → U γ → U γ
mirrored arities motive u =
  pr₁ (Section.valuation (fold arities motive mirror (algebra γ) (law γ)) u)

original-depth : depth (node lopsided) ＝ suc (suc zero)
original-depth = refl

mirrored-depth :
  (arities : (A : Set) (B : A → Set) → FunExt A B)
  (motive : (A : Set) (B : A → Set) → FunExt A B)
  → depth (mirrored arities motive (node lopsided)) ＝ suc zero
mirrored-depth arities motive = refl

twice-mirrored-depth :
  (arities : (A : Set) (B : A → Set) → FunExt A B)
  (motive : (A : Set) (B : A → Set) → FunExt A B)
  → depth
      ( pr₁
          ( Section.valuation
              ( fold arities motive (compose mirror mirror) (algebra γ)
                  (law γ))
              (node lopsided)))
    ＝ suc (suc zero)
twice-mirrored-depth arities motive = refl

mirror-moves :
  (arities : (A : Set) (B : A → Set) → FunExt A B)
  (motive : (A : Set) (B : A → Set) → FunExt A B)
  → ((u : U γ) → mirrored arities motive u ＝ u) → 𝟘
mirror-moves arities motive fixed =
  zero-is-not-suc (suc-is-injective (ap depth (fixed (node lopsided))))
