{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Decoding where

-- The decoding laws of a parent's formers are identifications of types: the
-- empty, unit and two-point codes decode to `𝟘`, `𝟙` and `𝟚`, the code of the
-- natural numbers to `ℕ`, each lifted to the decoded level (the lift asserts no
-- resizing), and the product, sum, tree and identity codes to dependent
-- function types, dependent pair types, W-types (Foundation.Tree.W) and
-- identity types.
--
-- Every closure inherits the laws: a closure's names give its child its own
-- formers (`child-formers`), and the parent's laws, composed with the
-- identifications of the names, give their laws (`child-decoding`). A Mahlo
-- reflection is a reflector together with the parent's decoding laws; every
-- reflected child then decodes its formers as the parent does
-- (`reflected-decoding`).

open import SPT.Base
open import SPT.Foundation.Tree.W using (W)
open import SPT.Mahlo.Specification using
  (Family; Operator; Formers; Decode; Closure; Reflection; Mahlo)

------------------------------------------------------------------------
-- Decoding laws

record DecodingLaws {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Formers C D) : Set (κ ⊔ lsuc ℓ) where
  field
    empty-β : D (Formers.empty Q) ＝ Lift ℓ 𝟘
    unit-β : D (Formers.unit Q) ＝ Lift ℓ 𝟙
    two-β : D (Formers.two Q) ＝ Lift ℓ 𝟚
    natural-β : D (Formers.natural Q) ＝ Lift ℓ ℕ
    product-β : (a : C) (b : D a → C) →
      D (Formers.product Q (a , b)) ＝ ((x : D a) → D (b x))
    sum-β : (a : C) (b : D a → C) →
      D (Formers.sum Q (a , b)) ＝ Σ (D a) (λ x → D (b x))
    tree-β : (a : C) (b : D a → C) →
      D (Formers.tree Q (a , b)) ＝ W (D a) (λ x → D (b x))
    identity-β : (a : C) (x y : D a) →
      D (Formers.identity Q a x y) ＝ (x ＝ y)

------------------------------------------------------------------------
-- Mahlo reflections

record MahloReflection {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Formers C D) : Set (κ ⊔ lsuc ℓ) where
  field
    codeReflection : Mahlo Q
    decoding : DecodingLaws Q

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D}
  where

  reflect : MahloReflection Q → (Ψ : Operator D) → Reflection Q Ψ
  reflect M = Mahlo.reflect (MahloReflection.codeReflection M)

------------------------------------------------------------------------
-- The formers and laws of a closure's child

-- Each law of the child is the identification its name carries, followed by the
-- parent's law.

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D}
  {Ψ : Operator D} {A : Set ℓ} where

  child-formers : (L : Closure Q Ψ A) →
    Formers A (Decode D (Closure.interpret L))
  child-formers L = record
    { empty = pr₁ (Closure.empty L)
    ; unit = pr₁ (Closure.unit L)
    ; two = pr₁ (Closure.two L)
    ; natural = pr₁ (Closure.natural L)
    ; product = λ F → pr₁ (Closure.product L F)
    ; sum = λ F → pr₁ (Closure.sum L F)
    ; tree = λ F → pr₁ (Closure.tree L F)
    ; identity = λ a x y → pr₁ (Closure.identity L a x y)
    }

  child-decoding : DecodingLaws Q → (L : Closure Q Ψ A) →
    DecodingLaws (child-formers L)
  child-decoding laws L = record
    { empty-β = ap D (pr₂ (Closure.empty L)) ∙ DecodingLaws.empty-β laws
    ; unit-β = ap D (pr₂ (Closure.unit L)) ∙ DecodingLaws.unit-β laws
    ; two-β = ap D (pr₂ (Closure.two L)) ∙ DecodingLaws.two-β laws
    ; natural-β =
        ap D (pr₂ (Closure.natural L)) ∙ DecodingLaws.natural-β laws
    ; product-β = λ a b →
        ap D (pr₂ (Closure.product L (a , b)))
          ∙ DecodingLaws.product-β laws (Closure.interpret L a)
            (λ x → Closure.interpret L (b x))
    ; sum-β = λ a b →
        ap D (pr₂ (Closure.sum L (a , b)))
          ∙ DecodingLaws.sum-β laws (Closure.interpret L a)
            (λ x → Closure.interpret L (b x))
    ; tree-β = λ a b →
        ap D (pr₂ (Closure.tree L (a , b)))
          ∙ DecodingLaws.tree-β laws (Closure.interpret L a)
            (λ x → Closure.interpret L (b x))
    ; identity-β = λ a x y →
        ap D (pr₂ (Closure.identity L a x y))
          ∙ DecodingLaws.identity-β laws (Closure.interpret L a) x y
    }

------------------------------------------------------------------------
-- Every reflected child decodes as the parent

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D}
  where

  reflected-decoding : (M : MahloReflection Q) (Ψ : Operator D) →
    DecodingLaws (child-formers (Reflection.closure (reflect M Ψ)))
  reflected-decoding M Ψ =
    child-decoding (MahloReflection.decoding M)
      (Reflection.closure (reflect M Ψ))
