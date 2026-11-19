{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Equivalences where

-- Under function extensionality, being contractible is a proposition
-- (`being-contractible-is-proposition`), so having contractible fibers is one
-- (`being-equivalence-is-proposition`), and two equivalences with one map are
-- identified (`equivalences-with-one-map`). Each statement names the function
-- types it needs extensionality for. Under extensionality at one level, the
-- equivalences into a set form a set (`equivalences-into-a-set-form-a-set`).

open import SPT.Base
open import SPT.Foundation.Contractible using
  (is-contractible; contractible-types-are-sets)
open import SPT.Foundation.Extensionality using (FunExt; Π-is-proposition)
open import SPT.Foundation.Fibers using (fiber; has-contractible-fibers)
open import SPT.Foundation.Propositions using
  (is-proposition; is-set; propositions-are-sets)
open import SPT.Foundation.Sets using
  (products-of-sets-are-sets; sums-of-sets-are-sets)
open import SPT.Foundation.Univalence using (Equivalence)

------------------------------------------------------------------------
-- Being contractible

module _ {μ : Level} (A : Set μ) where

  being-contractible-is-proposition :
    ((c : A) → FunExt A (λ x → c ＝ x)) → is-proposition (is-contractible A)
  being-contractible-is-proposition extensionality (c , p) (c′ , p′) =
    to-Σ-＝ (p c′)
      ( extensionality c′
          (transport (λ z → (x : A) → z ＝ x) (p c′) p)
          p′
          ( λ x →
              contractible-types-are-sets (c , p) c′ x
                (transport (λ z → (y : A) → z ＝ y) (p c′) p x)
                (p′ x)))

------------------------------------------------------------------------
-- Being an equivalence

module _ {μ ν : Level} {A : Set μ} {B : Set ν} (f : A → B) where

  being-equivalence-is-proposition :
    FunExt B (λ b → is-contractible (fiber f b)) →
    ((b : B) (c : fiber f b) → FunExt (fiber f b) (λ x → c ＝ x)) →
    is-proposition (has-contractible-fibers f)
  being-equivalence-is-proposition extensionality extensionality′ =
    Π-is-proposition extensionality
      ( λ b →
          being-contractible-is-proposition (fiber f b) (extensionality′ b))

module _ {μ ν : Level} {A : Set μ} {B : Set ν} where

  equivalences-with-one-map : (e e′ : Equivalence A B) →
    FunExt B (λ b → is-contractible (fiber (pr₁ e) b)) →
    ( (b : B) (c : fiber (pr₁ e) b) →
      FunExt (fiber (pr₁ e) b) (λ x → c ＝ x)) →
    pr₁ e ＝ pr₁ e′ → e ＝ e′
  equivalences-with-one-map (f , c) (.f , c′) extensionality extensionality′
    refl =
    to-Σ-＝ refl
      (being-equivalence-is-proposition f extensionality extensionality′ c c′)

------------------------------------------------------------------------
-- Equivalences into a set

-- The maps into a set form a set, and having contractible fibers is a
-- proposition.

module _ {ℓ : Level}
  (extensionality : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y) where

  equivalences-into-a-set-form-a-set : (A B : Set ℓ) → is-set B →
    is-set (Equivalence A B)
  equivalences-into-a-set-form-a-set A B set =
    sums-of-sets-are-sets
      (products-of-sets-are-sets extensionality A (λ a → B) (λ a → set))
      (λ f → propositions-are-sets
        (being-equivalence-is-proposition f
          (extensionality B (λ b → is-contractible (fiber f b)))
          (λ b c → extensionality (fiber f b) (λ x → c ＝ x))))
