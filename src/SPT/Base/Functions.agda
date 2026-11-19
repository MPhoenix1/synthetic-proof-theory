{-# OPTIONS --safe --without-K #-}

module SPT.Base.Functions where

-- Dependent functions are Agda's own `(x : A) → B x`. SPT defines no `Π` of its
-- own: a definition `Π A B` would be a second spelling of that type.
--
-- This module gives the identity function, composition `g ∘ f` and the constant
-- functions. Composition is not dependent: a dependent composition asks Agda to
-- solve its family by higher-order unification at every use.

open import SPT.Base.Universes

module _ {ℓ : Level} {A : Set ℓ} where

  id : A → A
  id x = x

module _ {ℓ κ μ : Level} {A : Set ℓ} {B : Set κ} {C : Set μ} where

  infixr 15 _∘_

  _∘_ : (B → C) → (A → B) → A → C
  (g ∘ f) x = g (f x)

module _ {ℓ κ : Level} {A : Set ℓ} {B : Set κ} where

  const : A → B → A
  const x _ = x
