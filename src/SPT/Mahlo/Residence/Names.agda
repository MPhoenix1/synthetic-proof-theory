{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Residence.Names where

-- Names, in a closure, of the families and codes formed from named codes.
-- Along an identification of families the branches agree at corresponding
-- points (`branch-along`). A family whose head and branches are named is
-- the image of a family of names (`family-join`, `realized-family`), under
-- function extensionality for the maps into the codes. So the formers of
-- named codes, the operator's result and branch codes at them, and identity
-- codes over a named code are named (`former-name`, `result-name`,
-- `branch-name`, `identity-name`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Mahlo.Specification using
  (Family; Operator; Formers; Decode; map; Name; Closure)

------------------------------------------------------------------------
-- Identifications of families

branch-along : {κ ℓ : Level} {C : Set κ} (D : C → Set ℓ) {c c′ : C}
  {f : D c → C} {f′ : D c′ → C} (p : _＝_ {A = Family D} (c , f) (c′ , f′))
  (y : D c) → f y ＝ f′ (transport D (ap pr₁ p) y)
branch-along D refl y = refl

-- A named head with named branches is named by the family of the names.
family-join : {κ ℓ α : Level} {C : Set κ} {A : Set α} (D : C → Set ℓ)
  (code : A → C) (a : A) {c : C} (e : code a ＝ c) (g : D c → C)
  (h : (y : D c) → Σ A (λ b → code b ＝ g y)) → FunExt (D c) (λ _ → C) →
  _＝_ {A = Family D} (code a , (λ x → code (pr₁ (h (transport D e x)))))
    (c , g)
family-join D code a refl g h funext =
  ap (λ k → code a , k) (funext (λ x → code (pr₁ (h x))) g (λ x → pr₂ (h x)))

------------------------------------------------------------------------
-- Names of formed codes

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} (Q : Formers C D)
  (Ψ : Operator D) where

  -- A family with named head and branches, with the identification of its
  -- names.
  realized-family : ((X : Set ℓ) → FunExt X (λ _ → C)) → {A : Set ℓ}
    (L : Closure Q Ψ A) {c : C} (g : D c → C) →
    Name (Closure.interpret L) c →
    ((y : D c) → Name (Closure.interpret L) (g y)) →
    Σ (Family (Decode D (Closure.interpret L)))
      (λ F → map D (Closure.interpret L) F ＝ (c , g))
  realized-family funext L {c} g head branches =
    (pr₁ head , (λ x → pr₁ (branches (transport D (pr₂ head) x)))) ,
    family-join D (Closure.interpret L) (pr₁ head) (pr₂ head) g branches
      (funext (D c))

  former-name : {A : Set ℓ} (L : Closure Q Ψ A) (former : Family D → C) →
    ((F : Family (Decode D (Closure.interpret L))) →
      Name (Closure.interpret L) (former (map D (Closure.interpret L) F))) →
    {c : C} {g : D c → C} →
    Σ (Family (Decode D (Closure.interpret L)))
      (λ F → map D (Closure.interpret L) F ＝ (c , g)) →
    Name (Closure.interpret L) (former (c , g))
  former-name L former close (F , path) =
    pr₁ (close F) , (pr₂ (close F) ∙ ap former path)

  result-name : {A : Set ℓ} (L : Closure Q Ψ A) {c : C} {g : D c → C} →
    Σ (Family (Decode D (Closure.interpret L)))
      (λ F → map D (Closure.interpret L) F ＝ (c , g)) →
    Name (Closure.interpret L) (pr₁ (Ψ (c , g)))
  result-name L (F , path) =
    pr₁ (Closure.inner L F) ,
    (ap pr₁ (Closure.inner-β L F) ∙ ap (λ G → pr₁ (Ψ G)) path)

  branch-name : {A : Set ℓ} (L : Closure Q Ψ A) {c : C} {g : D c → C} →
    Σ (Family (Decode D (Closure.interpret L)))
      (λ F → map D (Closure.interpret L) F ＝ (c , g)) →
    (y : D (pr₁ (Ψ (c , g)))) →
    Name (Closure.interpret L) (pr₂ (Ψ (c , g)) y)
  branch-name L {c} {g} (F , path) y =
    let q = Closure.inner-β L F ∙ ap Ψ path
    in pr₂ (Closure.inner L F) (transport D (ap pr₁ q ⁻¹) y) ,
       ( branch-along D q (transport D (ap pr₁ q ⁻¹) y)
       ∙ ap (pr₂ (Ψ (c , g))) (back-and-forth-transport D (ap pr₁ q) y))

  identity-name : {A : Set ℓ} (L : Closure Q Ψ A) {c : C} →
    Name (Closure.interpret L) c → (x y : D c) →
    Name (Closure.interpret L) (Formers.identity Q c x y)
  identity-name L (a , refl) x y = Closure.identity L a x y
