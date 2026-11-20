{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Residence.Adjoined.Children where

-- Codes of families, children and closure under an operator in an
-- adjoined Tarski universe (family, child, closed-under). included maps
-- a child's decoded families into its parent's. Transport of function
-- and sum codes and closure-congruence retain the given paths of codes.

open import SPT.Base
open import SPT.Foundation.Happly using (happly)
open import SPT.Foundation.Happly.Pointwise using (pointwise)
open import SPT.Foundation.Sets.Uniqueness using (Extensionality)
open import SPT.Mahlo.Residence.Adjoined using
  (Name; decode; product; sum; identity)

module _ {ℓ : Level} (L : Set ℓ) (D : L → Set ℓ) (I : Set (lsuc ℓ))
  (E : I → Set ℓ) (M : Name L D I E)
  (N : decode L D I E M → Name L D I E) where

  family : Name L D I E
  family = sum M (λ m → product (N m) (λ _ → M))

  child : (a : decode L D I E M) →
    (decode L D I E (N a) → decode L D I E M) → Name L D I E
  child a b = sum (N a) (λ n → product (N (b n)) (λ _ → N a))

  included : (a : decode L D I E M)
    (b : decode L D I E (N a) → decode L D I E M) →
    decode L D I E (child a b) → decode L D I E family
  included a b f = b (pr₁ f) , λ x → b (pr₂ f x)

  closed-under : (a : decode L D I E M)
    (b : decode L D I E (N a) → decode L D I E M) →
    (decode L D I E family → decode L D I E family) → Name L D I E
  closed-under a b o =
    product (child a b) (λ f →
      sum (child a b) (λ g →
        identity family (included a b g) (o (included a b f))))

module _ {ℓ : Level} (L : Set ℓ) (D : L → Set ℓ) (I : Set (lsuc ℓ))
  (E : I → Set ℓ) where

  transport-sum-back : (P : Name L D I E)
    {Q₁ Q₂ : decode L D I E P → Name L D I E}
    (h : Q₁ ＝ Q₂) (g : decode L D I E (sum P Q₂)) →
    transport (decode L D I E) (ap (sum P) h ⁻¹) g
      ＝ (pr₁ g ,
          transport (decode L D I E) (happly h (pr₁ g) ⁻¹) (pr₂ g))
  transport-sum-back P refl g = refl

  transport-arrow-back : {ν : Level} {X : Set ν}
    (P : X → Name L D I E) {v₀ v : X} (ρ : v₀ ＝ v)
    (R : Name L D I E)
    (c : decode L D I E (P v) → decode L D I E R) →
    transport (decode L D I E) (ap (λ u → product (P u) (λ _ → R)) ρ ⁻¹) c
      ＝ λ y → c (transport (decode L D I E) (ap P ρ) y)
  transport-arrow-back P refl R c = refl

module _ (ext : Extensionality) {ℓ : Level}
  (L : Set ℓ) (D : L → Set ℓ) (I : Set (lsuc ℓ)) (E : I → Set ℓ) where

  closure-congruence : {P P′ : Name L D I E} (e : P ＝ P′)
    (J : decode L D I E P → decode L D I E P → Name L D I E)
    (J′ : decode L D I E P′ → decode L D I E P′ → Name L D I E) →
    ((f g : decode L D I E P′) →
      J (transport (decode L D I E) (e ⁻¹) f)
        (transport (decode L D I E) (e ⁻¹) g) ＝ J′ f g) →
    product P (λ f → sum P (λ g → J f g))
      ＝ product P′ (λ f → sum P′ (λ g → J′ f g))
  closure-congruence {P} refl J J′ ι =
    ap (product P)
      (pointwise ext (λ f → ap (sum P) (pointwise ext (λ g → ι f g))))
