{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.Mahlo.Decoding where

-- Decoding laws of a parent's formers, as identities of types, and their
-- inheritance by every closure: a closure's names give the child its own
-- formers (child-formers), and the parent's laws give their laws
-- (child-decoding).  MahloReflection is a reflector with decoding laws;
-- every reflected child then decodes its formers as the parent does
-- (reflected-decoding).  W is an ordinary W-type with its induction.

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Bool.Base using (Bool)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Level using (Lift)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; trans)
open import SPT.Cubical.Core.Mahlo.Specification using
  (Family; Operator; Formers; Closure; Reflection; Mahlo)

private
  variable
    ℓ κ : Level

-- W A B: well-founded trees with nodes x : A branching over B x.
data W {a b : Level} (A : Set a) (B : A → Set b)
    : Set (a ⊔ b) where
  sup : (x : A) → (B x → W A B) → W A B

induction : ∀ {a b ν} {A : Set a} {B : A → Set b}
  (P : W A B → Set ν) →
  ((x : A) (f : B x → W A B) →
    ((y : B x) → P (f y)) → P (sup x f)) →
  (w : W A B) → P w
induction P step (sup x f) =
  step x f (λ y → induction P step (f y))

induction-β : ∀ {a b ν} {A : Set a} {B : A → Set b}
  (P : W A B → Set ν)
  (step : (x : A) (f : B x → W A B) →
    ((y : B x) → P (f y)) → P (sup x f))
  (x : A) (f : B x → W A B) →
  induction P step (sup x f) ≡ step x f (λ y → induction P step (f y))
induction-β P step x f = refl

-- The formers decode to the standard library's empty, unit, Bool, ℕ,
-- Σ and identity types, to function types, and to W.  Lift places Bool
-- and ℕ at the decoded level; it asserts no resizing.
record DecodingLaws {C : Set κ} {D : C → Set ℓ}
  (Q : Formers C D) : Set (κ ⊔ lsuc ℓ) where
  field
    empty-β : D (Formers.empty Q) ≡ ⊥ {ℓ}
    unit-β : D (Formers.unit Q) ≡ ⊤ {ℓ}
    two-β : D (Formers.two Q) ≡ Lift ℓ Bool
    natural-β : D (Formers.natural Q) ≡ Lift ℓ ℕ

    product-β : (a : C) (b : D a → C) →
      D (Formers.product Q (a , b)) ≡ ((x : D a) → D (b x))

    sum-β : (a : C) (b : D a → C) →
      D (Formers.sum Q (a , b)) ≡ Σ (D a) (λ x → D (b x))

    tree-β : (a : C) (b : D a → C) →
      D (Formers.tree Q (a , b)) ≡ W (D a) (λ x → D (b x))

    identity-β : (a : C) (x y : D a) →
      D (Formers.identity Q a x y) ≡ (x ≡ y)

-- The formers of a closure's child, read off its names.
child-formers : {C : Set κ} {D : C → Set ℓ}
  {Q : Formers C D} {Ψ : Operator D} {A : Set ℓ}
  (L : Closure Q Ψ A) → Formers A (Closure.Decode L)
child-formers L = record
  { empty = proj₁ (Closure.empty L)
  ; unit = proj₁ (Closure.unit L)
  ; two = proj₁ (Closure.two L)
  ; natural = proj₁ (Closure.natural L)
  ; product = λ F → proj₁ (Closure.product L F)
  ; sum = λ F → proj₁ (Closure.sum L F)
  ; tree = λ F → proj₁ (Closure.tree L F)
  ; identity = λ a x y → proj₁ (Closure.identity L a x y)
  }

-- Each law of the child: the name's identity, then the parent's law.
child-decoding : {C : Set κ} {D : C → Set ℓ}
  {Q : Formers C D} {Ψ : Operator D} {A : Set ℓ} →
  DecodingLaws Q → (L : Closure Q Ψ A) →
  DecodingLaws (child-formers L)
child-decoding {D = D} laws L = record
  { empty-β = trans (cong D (proj₂ (Closure.empty L)))
      (DecodingLaws.empty-β laws)
  ; unit-β = trans (cong D (proj₂ (Closure.unit L)))
      (DecodingLaws.unit-β laws)
  ; two-β = trans (cong D (proj₂ (Closure.two L)))
      (DecodingLaws.two-β laws)
  ; natural-β = trans (cong D (proj₂ (Closure.natural L)))
      (DecodingLaws.natural-β laws)
  ; product-β = λ a b →
      trans (cong D (proj₂ (Closure.product L (a , b))))
        (DecodingLaws.product-β laws (Closure.interpret L a)
          (λ x → Closure.interpret L (b x)))
  ; sum-β = λ a b →
      trans (cong D (proj₂ (Closure.sum L (a , b))))
        (DecodingLaws.sum-β laws (Closure.interpret L a)
          (λ x → Closure.interpret L (b x)))
  ; tree-β = λ a b →
      trans (cong D (proj₂ (Closure.tree L (a , b))))
        (DecodingLaws.tree-β laws (Closure.interpret L a)
          (λ x → Closure.interpret L (b x)))
  ; identity-β = λ a x y →
      trans (cong D (proj₂ (Closure.identity L a x y)))
        (DecodingLaws.identity-β laws (Closure.interpret L a) x y)
  }

-- A reflector together with the parent's decoding laws.
record MahloReflection {C : Set κ} {D : C → Set ℓ}
  (Q : Formers C D) : Set (κ ⊔ lsuc ℓ) where
  field
    codeReflection : Mahlo Q
    decoding : DecodingLaws Q

  reflect : (Ψ : Operator D) → Reflection Q Ψ
  reflect = Mahlo.reflect codeReflection

-- Every reflected child decodes its formers as the parent does.
reflected-decoding : {C : Set κ} {D : C → Set ℓ}
  {Q : Formers C D} (M : MahloReflection Q) (Ψ : Operator D) →
  DecodingLaws
    (child-formers (Reflection.closure (MahloReflection.reflect M Ψ)))
reflected-decoding M Ψ =
  child-decoding (MahloReflection.decoding M)
    (Reflection.closure (MahloReflection.reflect M Ψ))
