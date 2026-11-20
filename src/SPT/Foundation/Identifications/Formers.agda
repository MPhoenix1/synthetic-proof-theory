{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Identifications.Formers where

-- Type formers along an identification p : A ＝ B of their domains, with
-- `transport (λ X → X) p` carrying points of A to points of B. A former T
-- applied to a family on B pulled back along p is T at the family itself
-- (`former-at-transported-family`):
--
--   T A (λ x → F (transport (λ X → X) p x)) ＝ T B F,
--
-- so, under extensionality for families on A, families identified
-- pointwise along p give identified types (`former-path`). Identity types
-- of points carried back along p are the identity types of the points
-- (`identity-type-path`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)

module _ {ℓ κ μ : Level} (T : (A : Set ℓ) → (A → Set κ) → Set μ) where

  former-at-transported-family : {A B : Set ℓ} (p : A ＝ B)
    (F : B → Set κ) →
    T A (λ x → F (transport (λ X → X) p x)) ＝ T B F
  former-at-transported-family refl F = refl

  former-path : {A B : Set ℓ} (extensionality : FunExt A (λ x → Set κ))
    (p : A ＝ B) {F : A → Set κ} {G : B → Set κ} →
    ((x : A) → F x ＝ G (transport (λ X → X) p x)) → T A F ＝ T B G
  former-path {A} extensionality p {F} {G} q =
    ap (T A) (extensionality F (λ x → G (transport (λ X → X) p x)) q)
      ∙ former-at-transported-family p G

module _ {ℓ : Level} where

  identity-type-path : {A B : Set ℓ} (p : A ＝ B) (x y : B) →
    (transport (λ X → X) (p ⁻¹) x ＝ transport (λ X → X) (p ⁻¹) y)
      ＝ (x ＝ y)
  identity-type-path refl x y = refl
