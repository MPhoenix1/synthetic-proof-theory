{-# OPTIONS --safe --without-K #-}

module SPT.Base.List where

-- A list of points of `A` is either empty, `[]`, or a point followed by a list,
-- `x ∷ xs`. Lists are concatenated (`xs ++ ys`), which is associative with `[]`
-- as unit, and they have a length, which adds under concatenation. They are
-- the lists of `Agda.Builtin.List`, with SPT's fixity for `_∷_` given in the
-- renaming.

open import Agda.Builtin.List public
  renaming (_∷_ to infixr 10 _∷_)

open import SPT.Base.Universes
open import SPT.Base.Identity using (_＝_; refl; ap)
open import SPT.Base.Natural using (ℕ; zero; suc; _+_)

module _ {ℓ : Level} {A : Set ℓ} where

  infixr 10 _++_

  _++_ : List A → List A → List A
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  length : List A → ℕ
  length [] = zero
  length (x ∷ xs) = suc (length xs)

------------------------------------------------------------------------
-- Properties

module _ {ℓ : Level} {A : Set ℓ} where

  []-right-neutral : (xs : List A) → xs ++ [] ＝ xs
  []-right-neutral [] = refl
  []-right-neutral (x ∷ xs) = ap (x ∷_) ([]-right-neutral xs)

  ++-assoc : (xs ys zs : List A) → (xs ++ ys) ++ zs ＝ xs ++ (ys ++ zs)
  ++-assoc [] ys zs = refl
  ++-assoc (x ∷ xs) ys zs = ap (x ∷_) (++-assoc xs ys zs)

  length-++ : (xs ys : List A) →
    length (xs ++ ys) ＝ length xs + length ys
  length-++ [] ys = refl
  length-++ (x ∷ xs) ys = ap suc (length-++ xs ys)
