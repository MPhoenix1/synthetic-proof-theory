{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.Boundary where

-- Principal supports of ω^P. The supports below ω^a are exactly those that
-- are empty or lead with an exponent below a, with both inverse laws, and
-- then every exponent lies below a. Natural calibrates ℕ as exactly the
-- segment below ω¹ in ω^ℕ.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Isomorphisms using (_≅_; ≅-sym; ≅-trans)
open import SPT.Cubical.Foundation.Nat.Arithmetic using (≤ℕˢ-is-proposition)

import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order
import SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.Support as Support

module Power {A : Set} (P : Order.Order A) where

  module Supports = Support.Power P
  module P = Order.Order P

  principal : A → Supports.Term
  principal a = Supports.single a zero

  -- Below ωᵃ, a support is empty or leads with an exponent below a; since
  -- supports decrease, every later exponent is then below a as well.
  Bound : A → Supports.Term → Set
  Bound a ([] , _) = 𝟙
  Bound a (((b , _) ∷ _) , _) = b P.< a

  below : (a : A) (x : Supports.Term) → Bound a x → x Supports.< principal a
  below a ([] , ⋆) ⋆ = Supports.empty
  below a (((b , n) ∷ xs) , q) p = Supports.head (Supports.Pair.earlier p)

  bound : (a : A) (x : Supports.Term) → x Supports.< principal a → Bound a x
  bound a ([] , ⋆) Supports.empty = ⋆
  bound a (((b , n) ∷ xs) , q) (Supports.head (Supports.Pair.earlier p)) = p
  bound a (((.a , n) ∷ xs) , q) (Supports.head (Supports.Pair.within .a ()))
  bound a (((.a , .zero) ∷ xs) , q) (Supports.tail ())

  below-bound : (a : A) (x : Supports.Term) (p : x Supports.< principal a)
    → below a x (bound a x p) ＝ p
  below-bound a ([] , ⋆) Supports.empty = refl
  below-bound a (((b , n) ∷ xs) , q)
    (Supports.head (Supports.Pair.earlier p)) = refl
  below-bound a (((.a , n) ∷ xs) , q)
    (Supports.head (Supports.Pair.within .a ()))
  below-bound a (((.a , .zero) ∷ xs) , q) (Supports.tail ())

  bound-below : (a : A) (x : Supports.Term) (p : Bound a x)
    → bound a x (below a x p) ＝ p
  bound-below a ([] , ⋆) ⋆ = refl
  bound-below a (((b , n) ∷ xs) , q) p = refl

  exact : (a : A)
    → Supports.Pred (principal a) ≅ Σ Supports.Term (Bound a)
  exact a = record
    { forward = λ { (x , p) → x , bound a x p }
    ; backward = λ { (x , p) → x , below a x p }
    ; backward-forward = λ { (x , p) → ap (x ,_) (below-bound a x p) }
    ; forward-backward = λ { (x , p) → ap (x ,_) (bound-below a x p) }
    }

  All : A → Supports.Raw → Set
  All a [] = 𝟙
  All a ((b , _) ∷ xs) = (b P.< a) × All a xs

  all : (a : A) (x : Supports.Term) → Bound a x → All a (Supports.raw x)
  all a ([] , ⋆) ⋆ = ⋆
  all a (((b , n) ∷ []) , ⋆) p = p , ⋆
  all a (((b , n) ∷ ys@((c , m) ∷ xs)) , (q , r)) p =
    p , all a (ys , r) (P.trans (Supports.sound q) p)

------------------------------------------------------------------------
-- An independent calibration: ℕ is exactly the segment below ω¹

module Natural where

  module Powerℕ = Power Order.natural
  module Supports = Powerℕ.Supports

  finite : ℕ → Supports.Term
  finite zero = Supports.zero
  finite (suc n) = Supports.single zero n

  cut : Supports.Term
  cut = Powerℕ.principal (suc zero)

  bounded : (n : ℕ) → Powerℕ.Bound (suc zero) (finite n)
  bounded zero = ⋆
  bounded (suc n) = s≤s z≤n

  below : (n : ℕ) → finite n Supports.< cut
  below n = Powerℕ.below (suc zero) (finite n) (bounded n)

  private
    impossible : ∀ {n} → n <ℕˢ zero → 𝟘
    impossible ()

    read : Σ Supports.Term (Powerℕ.Bound (suc zero)) → ℕ
    read (([] , ⋆) , ⋆) = zero
    read ((((a , n) ∷ []) , ⋆) , p) = suc n
    read ((((a , n) ∷ (b , m) ∷ xs) , (q , r)) , p)
      with below-one-is-zero a p
    ... | refl = 𝟘-elim (impossible (Supports.sound q))

    write : ℕ → Σ Supports.Term (Powerℕ.Bound (suc zero))
    write n = finite n , bounded n

    read-write : (n : ℕ) → read (write n) ＝ n
    read-write zero = refl
    read-write (suc n) = refl

    write-read : (x : Σ Supports.Term (Powerℕ.Bound (suc zero)))
      → write (read x) ＝ x
    write-read (([] , ⋆) , ⋆) = refl
    write-read ((((a , n) ∷ []) , ⋆) , p) with below-one-is-zero a p
    ... | refl =
      ap (Supports.single zero n ,_) (≤ℕˢ-is-proposition (s≤s z≤n) p)
    write-read ((((a , n) ∷ (b , m) ∷ xs) , (q , r)) , p)
      with below-one-is-zero a p
    ... | refl = 𝟘-elim (impossible (Supports.sound q))

    bounded-exact :
      ℕ ≅ Σ Supports.Term (Powerℕ.Bound (suc zero))
    bounded-exact = record
      { forward = write
      ; backward = read
      ; backward-forward = read-write
      ; forward-backward = write-read
      }

  exact : ℕ ≅ Supports.Pred cut
  exact = ≅-trans bounded-exact (≅-sym (Powerℕ.exact (suc zero)))

  preserve : ∀ {m n} → m <ℕˢ n → finite m Supports.< finite n
  preserve {zero} {suc n} p = Supports.empty
  preserve {suc m} {suc n} (s≤s p) = Supports.head (Supports.Pair.within zero p)

  reflect : ∀ {m n} → finite m Supports.< finite n → m <ℕˢ n
  reflect {zero} {zero} ()
  reflect {zero} {suc n} p = s≤s z≤n
  reflect {suc m} {zero} ()
  reflect {suc m} {suc n} p with Supports.single-pair-reflect p
  ... | Supports.Pair.earlier ()
  ... | Supports.Pair.within .zero q = s≤s q

  proper : (n : ℕ) → finite n ＝ cut → 𝟘
  proper zero ()
  proper (suc n) ()
