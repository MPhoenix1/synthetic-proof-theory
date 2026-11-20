{-# OPTIONS --safe --without-K #-}

module SPT.Base.List where

-- A list of points of `A` is either empty, `[]`, or a point followed by a list,
-- `x ∷ xs`. Lists are concatenated (`xs ++ ys`), which is associative with `[]`
-- as unit, and they have a length, which adds under concatenation. They are
-- the lists of `Agda.Builtin.List`, with SPT's fixity for `_∷_` given in the
-- renaming.
--
-- Lists under a map (`list-map`), a predicate holding at every member of a
-- list (`List-All`, carried along a map of predicates by `all-map`) or at
-- some member (`List-Any`), and membership in a list,
--
--   x ∈ˡ xs = List-Any (λ y → x ＝ y) xs,
--
-- whose proofs are the positions of x in xs: `at-head refl` at the head, and
-- `in-tail` for a position in the tail.
--
-- Identified nonempty lists have identified heads and identified tails
-- (`∷-injective-head`, `∷-injective-tail`).
--
-- The entry of a list at a position below its length (`list-lookup`):
--
--   list-lookup (x ∷ xs) fzero = x,
--   list-lookup (x ∷ xs) (fsuc i) = list-lookup xs i.

open import Agda.Builtin.List public
  renaming (_∷_ to infixr 10 _∷_)

open import SPT.Base.Universes
open import SPT.Base.Identity using (_＝_; refl; ap)
open import SPT.Base.Natural using (ℕ; zero; suc; _+_)
open import SPT.Base.Fin using (Fin; fsuc; fzero)

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

------------------------------------------------------------------------
-- Maps

module _ {ℓ κ : Level} {A : Set ℓ} {B : Set κ} where

  list-map : (A → B) → List A → List B
  list-map f [] = []
  list-map f (x ∷ xs) = f x ∷ list-map f xs

------------------------------------------------------------------------
-- Every member and some member

infixr 10 _∷_

data List-All {ℓ κ : Level} {A : Set ℓ} (P : A → Set κ) : List A → Set (ℓ ⊔ κ)
  where
  [] : List-All P []
  _∷_ : {x : A} {xs : List A} → P x → List-All P xs → List-All P (x ∷ xs)

data List-Any {ℓ κ : Level} {A : Set ℓ} (P : A → Set κ) : List A → Set (ℓ ⊔ κ)
  where
  at-head : {x : A} {xs : List A} → P x → List-Any P (x ∷ xs)
  in-tail : {x : A} {xs : List A} → List-Any P xs → List-Any P (x ∷ xs)

------------------------------------------------------------------------
-- Maps of predicates

module _ {ℓ κ μ : Level} {A : Set ℓ} {P : A → Set κ} {Q : A → Set μ} where

  -- A pointwise map of predicates carries List-All along a list.
  all-map : ({x : A} → P x → Q x) → {xs : List A} → List-All P xs →
    List-All Q xs
  all-map f [] = []
  all-map f (p ∷ ps) = f p ∷ all-map f ps

------------------------------------------------------------------------
-- Membership

module _ {ℓ : Level} {A : Set ℓ} where

  infix 6 _∈ˡ_

  _∈ˡ_ : A → List A → Set ℓ
  x ∈ˡ xs = List-Any (λ y → x ＝ y) xs

------------------------------------------------------------------------
-- Injectivity of cons

module _ {ℓ : Level} {A : Set ℓ} where

  ∷-injective-head : {x y : A} {xs ys : List A} → x ∷ xs ＝ y ∷ ys → x ＝ y
  ∷-injective-head refl = refl

  ∷-injective-tail :
    {x y : A} {xs ys : List A} → x ∷ xs ＝ y ∷ ys → xs ＝ ys
  ∷-injective-tail refl = refl

------------------------------------------------------------------------
-- Lookup

module _ {ℓ : Level} {A : Set ℓ} where

  list-lookup : (xs : List A) → Fin (length xs) → A
  list-lookup [] ()
  list-lookup (x ∷ xs) fzero = x
  list-lookup (x ∷ xs) (fsuc i) = list-lookup xs i
