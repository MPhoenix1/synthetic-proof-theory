{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Univalent.Discriminator where

-- What the univalent universes change, and that their rules have models.
-- The description `twin` has two introductions, both decoding to the unit
-- type. The generated part of any algebra of it keeps them apart: induction
-- reads off the label (`tag`, `apart`). Every univalent universe of it
-- identifies them (`identified`), and no path method reaches a family with
-- two distinct points (`no-tag`), so no eliminator separates them. The
-- rules of `Universe` hold for every description under extensionality
-- alone, with codes one level up: the identity algebra names each type
-- once, its names being singletons (`singletons`), and the intersection
-- needs no resizing there (`large`). This is Sattler and Vezzosi's universe
-- over the ambient one; what the Mahlo rule adds is small codes.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Impredicative.PropositionalResizing using
  (propositions-resize-to-their-level)
open import SPT.Foundation.Propositions using (is-proposition)

open import SPT.IR.Algebra using (Algebra; identity; identity-β)
open import SPT.IR.Description using (Desc; ι; σ)
import SPT.IR.Generated as Generated
import SPT.Mahlo.DS.Univalent.Construction as Construction
open import SPT.IR.Univalent.Generation using (Closed-Family)
open import SPT.IR.Univalent.Resizing using (generation)
open import SPT.IR.Univalent.Universe using
  (Universe; Path-method; forced)

------------------------------------------------------------------------
-- Two introductions with one decoding

twin : (ℓ : Level) → Desc {s = ℓ} (Set ℓ)
twin ℓ = σ (Lift ℓ 𝟚) (λ _ → ι (Lift ℓ 𝟙))

-- In the generated part of an algebra, induction reads the label.

module _
  {ℓ κ : Level} (M : Algebra κ (twin ℓ))
  where

  tag : Generated.G M → 𝟚
  tag = Generated.ind M (λ _ → 𝟚) (λ a xs hs → lower (pr₁ a))

  apart :
    Generated.make M (lift ₀ , lift ⋆) ≠ Generated.make M (lift ₁ , lift ⋆)
  apart e = ₀-is-not-₁ (ap tag e)

-- In a univalent universe the two codes decode alike, so ua identifies
-- them; and a path method makes its motive propositional, so it never
-- reaches a family with two distinct points.

module _
  {ℓ κ : Level} (U : Universe κ (twin ℓ))
  where

  identified :
    Universe.intro U (lift ₀ , lift ⋆) ＝ Universe.intro U (lift ₁ , lift ⋆)
  identified =
    Universe.ua U (Universe.intro U (lift ₀ , lift ⋆))
      (Universe.intro U (lift ₁ , lift ⋆))
      ( Universe.intro-β U (lift ₀ , lift ⋆)
      ∙ Universe.intro-β U (lift ₁ , lift ⋆) ⁻¹)

no-tag :
  {ℓ κ : Level} {γ : Desc {s = ℓ} (Set ℓ)} (ν : Level) (U : Universe κ γ)
  (a : Universe.Code U) → Path-method U (λ _ → Lift ν 𝟚) → 𝟘
no-tag ν U a n =
  ₀-is-not-₁ (ap lower (forced U (λ _ → Lift ν 𝟚) n a (lift ₀) (lift ₁)))

------------------------------------------------------------------------
-- The large universe

-- The identity algebra decodes each type as itself, so the names of X
-- are the singleton at X. Its carrier is one level up, so the
-- intersection of the closed families of level ℓ lies at the carrier's
-- level with no resizing.

singletons :
  {ℓ : Level} (X : Set ℓ) → is-proposition (Σ (Set ℓ) (λ Y → Y ＝ X))
singletons X (Y , refl) (Y′ , refl) = refl

large :
  {ℓ : Level} (γ : Desc {s = ℓ} (Set ℓ))
  → ((X : Set ℓ)
    → FunExt (Closed-Family (identity γ) ℓ)
        (λ C → Closed-Family.family C X))
  → Universe (lsuc ℓ) γ
large {ℓ} γ extensionality =
  Construction.universe (identity γ) (identity-β γ) singletons
    ( generation (identity γ) ℓ (propositions-resize-to-their-level (lsuc ℓ))
        extensionality)
