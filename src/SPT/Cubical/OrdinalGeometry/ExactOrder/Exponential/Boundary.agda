{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.Boundary where

-- Principal supports of ω^P. The supports below ω^a are exactly those that
-- are empty or lead with an exponent below a, with both inverse laws, and
-- then every exponent lies below a. Natural calibrates ℕ as exactly the
-- segment below ω¹ in ω^ℕ.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s)
import Data.Nat.Base as Nat
import Data.Nat.Properties as Nat
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import SPT.Cubical.Core.Equality.Isomorphism using (_≅_; ≅-sym; ≅-trans)
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
  Bound a ([] , _) = ⊤
  Bound a (((b , _) ∷ _) , _) = b P.< a

  below : (a : A) (x : Supports.Term) → Bound a x → x Supports.< principal a
  below a ([] , tt) tt = Supports.empty
  below a (((b , n) ∷ xs) , q) p = Supports.head (Supports.Pair.earlier p)

  bound : (a : A) (x : Supports.Term) → x Supports.< principal a → Bound a x
  bound a ([] , tt) Supports.empty = tt
  bound a (((b , n) ∷ xs) , q) (Supports.head (Supports.Pair.earlier p)) = p
  bound a (((.a , n) ∷ xs) , q) (Supports.head (Supports.Pair.within .a ()))
  bound a (((.a , .zero) ∷ xs) , q) (Supports.tail ())

  below-bound : (a : A) (x : Supports.Term) (p : x Supports.< principal a)
    → below a x (bound a x p) ≡ p
  below-bound a ([] , tt) Supports.empty = refl
  below-bound a (((b , n) ∷ xs) , q)
    (Supports.head (Supports.Pair.earlier p)) = refl
  below-bound a (((.a , n) ∷ xs) , q)
    (Supports.head (Supports.Pair.within .a ()))
  below-bound a (((.a , .zero) ∷ xs) , q) (Supports.tail ())

  bound-below : (a : A) (x : Supports.Term) (p : Bound a x)
    → bound a x (below a x p) ≡ p
  bound-below a ([] , tt) tt = refl
  bound-below a (((b , n) ∷ xs) , q) p = refl

  exact : (a : A)
    → Supports.Pred (principal a) ≅ Σ Supports.Term (Bound a)
  exact a = record
    { forward = λ { (x , p) → x , bound a x p }
    ; backward = λ { (x , p) → x , below a x p }
    ; backward-forward = λ { (x , p) → cong (x ,_) (below-bound a x p) }
    ; forward-backward = λ { (x , p) → cong (x ,_) (bound-below a x p) }
    }

  All : A → Supports.Raw → Set
  All a [] = ⊤
  All a ((b , _) ∷ xs) = (b P.< a) × All a xs

  all : (a : A) (x : Supports.Term) → Bound a x → All a (Supports.raw x)
  all a ([] , tt) tt = tt
  all a (((b , n) ∷ []) , tt) p = p , tt
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
  bounded zero = tt
  bounded (suc n) = s≤s z≤n

  below : (n : ℕ) → finite n Supports.< cut
  below n = Powerℕ.below (suc zero) (finite n) (bounded n)

  private
    impossible : ∀ {n} → n Nat.< zero → ⊥
    impossible ()

    read : Σ Supports.Term (Powerℕ.Bound (suc zero)) → ℕ
    read (([] , tt) , tt) = zero
    read ((((a , n) ∷ []) , tt) , p) = suc n
    read ((((a , n) ∷ (b , m) ∷ xs) , (q , r)) , p)
      with Nat.n<1⇒n≡0 p
    ... | refl = ⊥-elim (impossible (Supports.sound q))

    write : ℕ → Σ Supports.Term (Powerℕ.Bound (suc zero))
    write n = finite n , bounded n

    read-write : (n : ℕ) → read (write n) ≡ n
    read-write zero = refl
    read-write (suc n) = refl

    write-read : (x : Σ Supports.Term (Powerℕ.Bound (suc zero)))
      → write (read x) ≡ x
    write-read (([] , tt) , tt) = refl
    write-read ((((a , n) ∷ []) , tt) , p) with Nat.n<1⇒n≡0 p
    ... | refl = cong (Supports.single zero n ,_) (Nat.≤-irrelevant (s≤s z≤n) p)
    write-read ((((a , n) ∷ (b , m) ∷ xs) , (q , r)) , p)
      with Nat.n<1⇒n≡0 p
    ... | refl = ⊥-elim (impossible (Supports.sound q))

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

  preserve : ∀ {m n} → m Nat.< n → finite m Supports.< finite n
  preserve {zero} {suc n} p = Supports.empty
  preserve {suc m} {suc n} (s≤s p) = Supports.head (Supports.Pair.within zero p)

  reflect : ∀ {m n} → finite m Supports.< finite n → m Nat.< n
  reflect {zero} {zero} ()
  reflect {zero} {suc n} p = s≤s z≤n
  reflect {suc m} {zero} ()
  reflect {suc m} {suc n} p with Supports.single-pair-reflect p
  ... | Supports.Pair.earlier ()
  ... | Supports.Pair.within .zero q = s≤s q

  proper : (n : ℕ) → finite n ≡ cut → ⊥
  proper zero ()
  proper (suc n) ()
