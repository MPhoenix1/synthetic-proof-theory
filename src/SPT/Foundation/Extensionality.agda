{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Extensionality where

-- Function extensionality for a dependent function type `(x : A) → B x` says
-- that two of its functions are identified as soon as they agree at every
-- point. SPT never assumes it. It is a hypothesis about one function type at a
-- time, passed as an explicit argument to the theorems that use it, and each of
-- those theorems names the function type it needs it for.
--
-- Under function extensionality, a dependent function type whose values are all
-- propositions is a proposition.

open import SPT.Base
open import SPT.Foundation.Propositions using (is-proposition)

module _ {ℓ κ : Level} (A : Set ℓ) (B : A → Set κ) where

  FunExt : Set (ℓ ⊔ κ)
  FunExt = (f g : (x : A) → B x) → ((x : A) → f x ＝ g x) → f ＝ g

------------------------------------------------------------------------
-- Properties

module _ {ℓ κ : Level} {A : Set ℓ} {B : A → Set κ} where

  Π-is-proposition : FunExt A B → ((x : A) → is-proposition (B x)) →
    is-proposition ((x : A) → B x)
  Π-is-proposition extensionality propositions f g =
    extensionality f g (λ x → propositions x (f x) (g x))
