{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.Support where

-- Supports of ω^P for an exact order P: finite lists of exponent and
-- coefficient pairs with strictly decreasing exponents, their validity
-- check, and their lexicographic order.

open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
import Data.List as List
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂)

import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order

-- A coefficient n stands for n + 1 copies.  Validity is a finite Boolean
-- check of the decreasing exponents; its witnesses are unique even when
-- those of P are not.
module Power {A : Set} (P : Order.Order A) where

  module P = Order.Order P
  module Pair = Order.Sum P (λ _ → Order.natural)

  Raw : Set
  Raw = List (A × ℕ)

  less : A → A → Bool
  less a b with P.compare a b
  ... | inj₁ _ = true
  ... | inj₂ _ = false

  sound : ∀ {a b} → T (less a b) → a P.< b
  sound {a} {b} q with P.compare a b
  ... | inj₁ p = p
  ... | inj₂ _ = ⊥-elim q

  complete : ∀ {a b} → a P.< b → T (less a b)
  complete {a} {b} p with P.compare a b
  ... | inj₁ _ = tt
  ... | inj₂ (inj₁ refl) = P.irrefl a p
  ... | inj₂ (inj₂ q) = P.irrefl a (P.trans p q)

  Valid : Raw → Set
  Valid [] = ⊤
  Valid (_ ∷ []) = ⊤
  Valid ((a , _) ∷ (b , n) ∷ xs) = T (less b a) × Valid ((b , n) ∷ xs)

  tail-valid : ∀ {a n xs} → Valid ((a , n) ∷ xs) → Valid xs
  tail-valid {xs = []} _ = tt
  tail-valid {xs = _ ∷ _} q = proj₂ q

  private
    unique-T : ∀ {b} (p q : T b) → p ≡ q
    unique-T {true} tt tt = refl
    unique-T {false} ()

  unique : (xs : Raw) (p q : Valid xs) → p ≡ q
  unique [] tt tt = refl
  unique (_ ∷ []) tt tt = refl
  unique (_ ∷ y ∷ xs) (p , r) (q , s) =
    cong₂ _,_ (unique-T p q) (unique (y ∷ xs) r s)

  check : (xs : Raw) → Dec (Valid xs)
  check [] = yes tt
  check (_ ∷ []) = yes tt
  check ((a , m) ∷ ys@((b , n) ∷ xs)) with check ys | less b a
  ... | _ | false = no proj₁
  ... | yes q | true = yes (tt , q)
  ... | no q | true = no (λ p → q (proj₂ p))

  Term : Set
  Term = Σ Raw Valid

  raw : Term → Raw
  raw = proj₁

  equal : ∀ {x y : Term} → raw x ≡ raw y → x ≡ y
  equal {xs , p} {.xs , q} refl = cong (xs ,_) (unique xs p q)

  zero : Term
  zero = [] , tt

  single : A → ℕ → Term
  single a n = (a , n) ∷ [] , tt

  -- The exponents of a support, from the leading one down: its finite
  -- support in the base order.
  exponents : Term → List A
  exponents x = List.map proj₁ (raw x)

  ----------------------------------------------------------------------
  -- Lexicographic comparison: the empty support is least, a first difference
  -- decides, and a common head passes to the tails.

  infix 4 _≺_ _<_

  data _≺_ : Raw → Raw → Set where
    empty : ∀ {x xs} → [] ≺ (x ∷ xs)
    head : ∀ {x y xs ys} → x Pair.< y → (x ∷ xs) ≺ (y ∷ ys)
    tail : ∀ {x xs ys} → xs ≺ ys → (x ∷ xs) ≺ (x ∷ ys)

  _<_ : Term → Term → Set
  x < y = raw x ≺ raw y

  trans : ∀ {xs ys zs} → xs ≺ ys → ys ≺ zs → xs ≺ zs
  trans empty (head q) = empty
  trans empty (tail q) = empty
  trans (head p) (head q) = head (Order.Order.trans Pair.order p q)
  trans (head p) (tail q) = head p
  trans (tail p) (head q) = head q
  trans (tail p) (tail q) = tail (trans p q)

  compare-raw : (xs ys : Raw) → xs ≺ ys ⊎ (xs ≡ ys ⊎ ys ≺ xs)
  compare-raw [] [] = inj₂ (inj₁ refl)
  compare-raw [] (_ ∷ _) = inj₁ empty
  compare-raw (_ ∷ _) [] = inj₂ (inj₂ empty)
  compare-raw (x ∷ xs) (y ∷ ys) with Order.Order.compare Pair.order x y
  ... | inj₁ p = inj₁ (head p)
  ... | inj₂ (inj₂ p) = inj₂ (inj₂ (head p))
  ... | inj₂ (inj₁ refl) with compare-raw xs ys
  ...   | inj₁ p = inj₁ (tail p)
  ...   | inj₂ (inj₁ p) = inj₂ (inj₁ (cong (x ∷_) p))
  ...   | inj₂ (inj₂ p) = inj₂ (inj₂ (tail p))

  compare : (x y : Term) → x < y ⊎ (x ≡ y ⊎ y < x)
  compare x y with compare-raw (raw x) (raw y)
  ... | inj₁ p = inj₁ p
  ... | inj₂ (inj₁ p) = inj₂ (inj₁ (equal p))
  ... | inj₂ (inj₂ p) = inj₂ (inj₂ p)

  least : (x : Term) → x < zero → ⊥
  least x ()

  single-preserve : ∀ {a b n} → a P.< b → single a n < single b n
  single-preserve p = head (Pair.earlier p)

  single-pair-reflect : ∀ {a b m n}
    → single a m < single b n → (a , m) Pair.< (b , n)
  single-pair-reflect (head p) = p
  single-pair-reflect (tail ())

  single-reflect : ∀ {a b n} → single a n < single b n → a P.< b
  single-reflect {n = n} q with single-pair-reflect q
  ... | Pair.earlier p = p
  ... | Pair.within _ p = ⊥-elim (Order.Order.irrefl Order.natural n p)

  ----------------------------------------------------------------------
  -- The predecessors of a support.

  Pred : Term → Set
  Pred y = Σ Term (λ x → x < y)

  Parts : Raw → Set
  Parts [] = ⊥
  Parts (y ∷ ys) = ⊤ ⊎
    (Σ (A × ℕ) (λ x → Σ Raw (λ xs → Valid (x ∷ xs) × (x Pair.< y))) ⊎
     Σ Raw (λ xs → Valid (y ∷ xs) × (xs ≺ ys)))

  split : (y : Term) → Pred y → Parts (raw y)
  split ([] , _) (x , ())
  split (_ ∷ _ , _) (([] , tt) , empty) = inj₁ tt
  split (_ ∷ _ , _) (((x ∷ xs) , p) , head q) = inj₂ (inj₁ (x , xs , p , q))
  split (_ ∷ _ , _) (((_ ∷ xs) , p) , tail q) = inj₂ (inj₂ (xs , p , q))

  join : (y : Term) → Parts (raw y) → Pred y
  join ([] , _) ()
  join (_ ∷ _ , _) (inj₁ tt) = zero , empty
  join (_ ∷ _ , _) (inj₂ (inj₁ (x , xs , p , q))) = (x ∷ xs , p) , head q
  join (y ∷ _ , _) (inj₂ (inj₂ (xs , p , q))) = (y ∷ xs , p) , tail q

  join-split : (y : Term) (p : Pred y) → join y (split y p) ≡ p
  join-split ([] , _) (x , ())
  join-split (_ ∷ _ , _) (([] , tt) , empty) = refl
  join-split (_ ∷ _ , _) (((_ ∷ _) , _) , head _) = refl
  join-split (_ ∷ _ , _) (((_ ∷ _) , _) , tail _) = refl

  split-join : (y : Term) (p : Parts (raw y)) → split y (join y p) ≡ p
  split-join ([] , _) ()
  split-join (_ ∷ _ , _) (inj₁ tt) = refl
  split-join (_ ∷ _ , _) (inj₂ (inj₁ (_ , _ , _ , _))) = refl
  split-join (_ ∷ _ , _) (inj₂ (inj₂ (_ , _ , _))) = refl
