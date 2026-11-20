{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.Support where

-- Supports of ω^P for an exact order P: finite lists of exponent and
-- coefficient pairs with strictly decreasing exponents, their validity
-- check, and their lexicographic order.

open import SPT.Cubical.Base hiding (zero)
open import SPT.Cubical.Foundation.Two.Truth using (is-₁)

import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order

-- A coefficient n stands for n + 1 copies.  Validity is a finite Boolean
-- check of the decreasing exponents; its witnesses are unique even when
-- those of P are not.
module Power {A : Set} (P : Order.Order A) where

  module P = Order.Order P
  module Pair = Order.Sum P (λ _ → Order.natural)

  Raw : Set
  Raw = List (A × ℕ)

  less : A → A → 𝟚
  less a b with P.compare a b
  ... | inl _ = ₁
  ... | inr _ = ₀

  sound : ∀ {a b} → is-₁ (less a b) → a P.< b
  sound {a} {b} q with P.compare a b
  ... | inl p = p
  ... | inr _ = 𝟘-elim q

  complete : ∀ {a b} → a P.< b → is-₁ (less a b)
  complete {a} {b} p with P.compare a b
  ... | inl _ = ⋆
  ... | inr (inl refl) = P.irrefl a p
  ... | inr (inr q) = P.irrefl a (P.trans p q)

  Valid : Raw → Set
  Valid [] = 𝟙
  Valid (_ ∷ []) = 𝟙
  Valid ((a , _) ∷ (b , n) ∷ xs) = is-₁ (less b a) × Valid ((b , n) ∷ xs)

  tail-valid : ∀ {a n xs} → Valid ((a , n) ∷ xs) → Valid xs
  tail-valid {xs = []} _ = ⋆
  tail-valid {xs = _ ∷ _} q = pr₂ q

  private
    unique-T : ∀ {b} (p q : is-₁ b) → p ＝ q
    unique-T {₁} ⋆ ⋆ = refl
    unique-T {₀} ()

  unique : (xs : Raw) (p q : Valid xs) → p ＝ q
  unique [] ⋆ ⋆ = refl
  unique (_ ∷ []) ⋆ ⋆ = refl
  unique (_ ∷ y ∷ xs) (p , r) (q , s) =
    ap₂ _,_ (unique-T p q) (unique (y ∷ xs) r s)

  check : (xs : Raw) → is-decidable (Valid xs)
  check [] = inl ⋆
  check (_ ∷ []) = inl ⋆
  check ((a , m) ∷ ys@((b , n) ∷ xs)) with check ys | less b a
  ... | _ | ₀ = inr pr₁
  ... | inl q | ₁ = inl (⋆ , q)
  ... | inr q | ₁ = inr (λ p → q (pr₂ p))

  Term : Set
  Term = Σ Raw Valid

  raw : Term → Raw
  raw = pr₁

  equal : ∀ {x y : Term} → raw x ＝ raw y → x ＝ y
  equal {xs , p} {.xs , q} refl = ap (xs ,_) (unique xs p q)

  zero : Term
  zero = [] , ⋆

  single : A → ℕ → Term
  single a n = (a , n) ∷ [] , ⋆

  -- The exponents of a support, from the leading one down: its finite
  -- support in the base order.
  exponents : Term → List A
  exponents x = list-map pr₁ (raw x)

  ----------------------------------------------------------------------
  -- Lexicographic comparison: the empty support is least, a first difference
  -- decides, and a common head passes to the tails.

  infix 30 _≺_ _<_

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

  compare-raw : (xs ys : Raw) → xs ≺ ys ⊎ ((xs ＝ ys) ⊎ ys ≺ xs)
  compare-raw [] [] = inr (inl refl)
  compare-raw [] (_ ∷ _) = inl empty
  compare-raw (_ ∷ _) [] = inr (inr empty)
  compare-raw (x ∷ xs) (y ∷ ys) with Order.Order.compare Pair.order x y
  ... | inl p = inl (head p)
  ... | inr (inr p) = inr (inr (head p))
  ... | inr (inl refl) with compare-raw xs ys
  ...   | inl p = inl (tail p)
  ...   | inr (inl p) = inr (inl (ap (x ∷_) p))
  ...   | inr (inr p) = inr (inr (tail p))

  compare : (x y : Term) → x < y ⊎ ((x ＝ y) ⊎ y < x)
  compare x y with compare-raw (raw x) (raw y)
  ... | inl p = inl p
  ... | inr (inl p) = inr (inl (equal p))
  ... | inr (inr p) = inr (inr p)

  least : (x : Term) → x < zero → 𝟘
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
  ... | Pair.within _ p = 𝟘-elim (Order.Order.irrefl Order.natural n p)

  ----------------------------------------------------------------------
  -- The predecessors of a support.

  Pred : Term → Set
  Pred y = Σ Term (λ x → x < y)

  Parts : Raw → Set
  Parts [] = 𝟘
  Parts (y ∷ ys) = 𝟙 ⊎
    (Σ (A × ℕ) (λ x → Σ Raw (λ xs → Valid (x ∷ xs) × (x Pair.< y))) ⊎
     Σ Raw (λ xs → Valid (y ∷ xs) × (xs ≺ ys)))

  split : (y : Term) → Pred y → Parts (raw y)
  split ([] , _) (x , ())
  split (_ ∷ _ , _) (([] , ⋆) , empty) = inl ⋆
  split (_ ∷ _ , _) (((x ∷ xs) , p) , head q) = inr (inl (x , xs , p , q))
  split (_ ∷ _ , _) (((_ ∷ xs) , p) , tail q) = inr (inr (xs , p , q))

  join : (y : Term) → Parts (raw y) → Pred y
  join ([] , _) ()
  join (_ ∷ _ , _) (inl ⋆) = zero , empty
  join (_ ∷ _ , _) (inr (inl (x , xs , p , q))) = (x ∷ xs , p) , head q
  join (y ∷ _ , _) (inr (inr (xs , p , q))) = (y ∷ xs , p) , tail q

  join-split : (y : Term) (p : Pred y) → join y (split y p) ＝ p
  join-split ([] , _) (x , ())
  join-split (_ ∷ _ , _) (([] , ⋆) , empty) = refl
  join-split (_ ∷ _ , _) (((_ ∷ _) , _) , head _) = refl
  join-split (_ ∷ _ , _) (((_ ∷ _) , _) , tail _) = refl

  split-join : (y : Term) (p : Parts (raw y)) → split y (join y p) ＝ p
  split-join ([] , _) ()
  split-join (_ ∷ _ , _) (inl ⋆) = refl
  split-join (_ ∷ _ , _) (inr (inl (_ , _ , _ , _))) = refl
  split-join (_ ∷ _ , _) (inr (inr (_ , _ , _))) = refl
