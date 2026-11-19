{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Sets where

-- Sets and propositions under the type formers. A retract of a
-- proposition is a proposition (`retracts-of-propositions-are-propositions`).
-- Under extensionality for the dependent functions of one level, being a
-- proposition and being a set are propositions
-- (`being-a-proposition-is-a-proposition`, `being-a-set-is-a-proposition`),
-- and a product of sets is a set, an identification of functions being the
-- one extensionality makes from its homotopy (`products-of-sets-are-sets`,
-- through `funext-happly`). A sum of sets over a set is a set, an
-- identification of pairs being a pair of identifications
-- (`sums-of-sets-are-sets`, through `Σ-＝-≅`), and the lift of a set is a
-- set (`lifts-of-sets-are-sets`). In the same way a sum of 1-types over a
-- 1-type, a type whose identifications form sets, is a 1-type
-- (`sums-of-1-types-are-1-types`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Happly using (happly; funext; funext-happly)
open import SPT.Foundation.Isomorphisms using (Σ-＝-≅; ≅-sym)
open import SPT.Foundation.Isomorphisms.Sets using (isomorphic-to-a-set)
open import SPT.Foundation.Lifting using (lifting-is-isomorphism)
open import SPT.Foundation.Propositions using
  (is-proposition; is-set; propositions-are-sets; Σ-is-proposition)
open import SPT.Foundation.Propositions.Closure using
  (isomorphic-to-a-proposition)

------------------------------------------------------------------------
-- Retracts of propositions

module _ {ℓ κ : Level} {P : Set ℓ} {Q : Set κ} where

  retracts-of-propositions-are-propositions : (r : Q → P) (s : P → Q) →
    ((p : P) → r (s p) ＝ p) → is-proposition Q → is-proposition P
  retracts-of-propositions-are-propositions r s retraction q p p′ =
    retraction p ⁻¹ ∙ ap r (q (s p) (s p′)) ∙ retraction p′

------------------------------------------------------------------------
-- Under extensionality

module _ {ℓ : Level}
  (extensionality : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y) where

  being-a-proposition-is-a-proposition : (P : Set ℓ) →
    is-proposition (is-proposition P)
  being-a-proposition-is-a-proposition P h k =
    extensionality P (λ x → (y : P) → x ＝ y) h k
      (λ x → extensionality P (λ y → x ＝ y) (h x) (k x)
        (λ y → propositions-are-sets h x y (h x y) (k x y)))

  being-a-set-is-a-proposition : (P : Set ℓ) → is-proposition (is-set P)
  being-a-set-is-a-proposition P s t =
    extensionality P (λ x → (y : P) → is-proposition (x ＝ y)) s t
      (λ x → extensionality P (λ y → is-proposition (x ＝ y)) (s x) (t x)
        (λ y → being-a-proposition-is-a-proposition (x ＝ y) (s x y)
          (t x y)))

  -- An identification of functions is the one extensionality makes from
  -- its homotopy, and homotopies into sets are identified pointwise.
  products-of-sets-are-sets : (A : Set ℓ) (B : A → Set ℓ) →
    ((x : A) → is-set (B x)) → is-set ((x : A) → B x)
  products-of-sets-are-sets A B sets f g p q =
    funext-happly (extensionality A B) p ⁻¹
      ∙ ap (funext (extensionality A B) f g)
          (extensionality A (λ x → f x ＝ g x) (happly p) (happly q)
            (λ x → sets x (f x) (g x) (happly p x) (happly q x)))
      ∙ funext-happly (extensionality A B) q

------------------------------------------------------------------------
-- Sums and lifts

module _ {ℓ κ : Level} {A : Set ℓ} {B : A → Set κ} where

  sums-of-sets-are-sets : is-set A → ((x : A) → is-set (B x)) →
    is-set (Σ A B)
  sums-of-sets-are-sets s t σ τ =
    isomorphic-to-a-proposition (≅-sym (Σ-＝-≅ σ τ))
      (Σ-is-proposition (s (pr₁ σ) (pr₁ τ))
        (λ p → t (pr₁ τ) (transport B p (pr₂ σ)) (pr₂ τ)))

module _ {ℓ : Level} (κ : Level) {A : Set ℓ} where

  lifts-of-sets-are-sets : is-set A → is-set (Lift κ A)
  lifts-of-sets-are-sets = isomorphic-to-a-set (lifting-is-isomorphism κ A)

------------------------------------------------------------------------
-- Sums of 1-types

-- An identification of pairs is a pair of identifications, the first in a
-- set and the second in a set over it.

module _ {ℓ κ : Level} {A : Set ℓ} {B : A → Set κ} where

  sums-of-1-types-are-1-types : ((x y : A) → is-set (x ＝ y)) →
    ((x : A) (u v : B x) → is-set (u ＝ v)) →
    (σ τ : Σ A B) → is-set (σ ＝ τ)
  sums-of-1-types-are-1-types base fibers σ τ =
    isomorphic-to-a-set (≅-sym (Σ-＝-≅ σ τ))
      (sums-of-sets-are-sets (base (pr₁ σ) (pr₁ τ))
        (λ p → fibers (pr₁ τ) (transport B p (pr₂ σ)) (pr₂ τ)))
