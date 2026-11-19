{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Contractible where

-- A type is contractible when it has a point, its center, with which every
-- point is identified. Contractible types are closed under dependent pairs,
-- and, under function extensionality for the function type, under dependent
-- functions. The based path space of a point, the type of points together with
-- an identification from the given one, is contractible. A contractible type is
-- a set: every identification is identified with the one obtained from the
-- contraction.

open import SPT.Base
open import SPT.Foundation.Propositions using (is-set)
open import SPT.Foundation.Extensionality using (FunExt)

is-contractible : {ℓ : Level} → Set ℓ → Set ℓ
is-contractible A = Σ A (λ c → (x : A) → c ＝ x)

------------------------------------------------------------------------
-- Based path spaces, and contractible types are sets

module _ {ℓ : Level} {A : Set ℓ} where

  based-path-spaces-are-contractible : (a : A) →
    is-contractible (Σ A (λ x → a ＝ x))
  based-path-spaces-are-contractible a = (a , refl) , contraction
    where
    contraction : (p : Σ A (λ x → a ＝ x)) → (a , refl) ＝ p
    contraction (.a , refl) = refl

  contractible-types-are-sets : is-contractible A → is-set A
  contractible-types-are-sets (c , contraction) x y p q =
    canonical p ⁻¹ ∙ canonical q
    where
    canonical : (r : x ＝ y) → contraction x ⁻¹ ∙ contraction y ＝ r
    canonical refl = left-inverse (contraction x)

------------------------------------------------------------------------
-- Dependent pairs and dependent functions

-- For pairs, the contraction of the base is matched first, so the fiber over
-- the center is used as it is. For functions, under function extensionality for
-- `(x : A) → B x`, the center and the contraction are built pointwise;
-- extensionality only turns the pointwise contraction into an identification of
-- functions.

module _ {ℓ κ : Level} {A : Set ℓ} {B : A → Set κ} where

  Σ-is-contractible : is-contractible A →
    ((x : A) → is-contractible (B x)) → is-contractible (Σ A B)
  Σ-is-contractible (c , contraction) fibers =
    (c , pr₁ (fibers c)) , total
    where
    over : (a : A) → c ＝ a → (b : B a) → (c , pr₁ (fibers c)) ＝ (a , b)
    over .c refl b = to-Σ-＝ refl (pr₂ (fibers c) b)

    total : (p : Σ A B) → (c , pr₁ (fibers c)) ＝ p
    total (a , b) = over a (contraction a) b

  Π-is-contractible : FunExt A B → ((x : A) → is-contractible (B x)) →
    is-contractible ((x : A) → B x)
  Π-is-contractible extensionality fibers =
    (λ x → pr₁ (fibers x)) ,
    (λ f → extensionality (λ x → pr₁ (fibers x)) f
      (λ x → pr₂ (fibers x) (f x)))
