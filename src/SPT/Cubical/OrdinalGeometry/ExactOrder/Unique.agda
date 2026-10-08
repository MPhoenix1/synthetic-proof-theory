{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.ExactOrder.Unique where

-- Uniqueness of strict-order witnesses for an exact order, as a
-- hypothesis.  Under it, predecessors are recovered from their endpoints,
-- isomorphisms act on predecessors, and ordered sums over ℕ keep it.

open import Agda.Primitive using (Level)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; _<_)
import Data.Nat.Properties as Nat
open import Data.Product using (Σ; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; sym; trans; subst; subst₂)

open import SPT.Cubical.Core.Equality.Isomorphism using (_≅_)
import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order
import SPT.Cubical.OrdinalGeometry.ExactOrder.Maps as Maps

-- Any two witnesses of x < y are equal.  It is a hypothesis, not a field
-- of Order: the comparison witnesses of an order need not be unique.
Unique : ∀ {ℓ} {A : Set ℓ} → Order.Order A → Set ℓ
Unique P = ∀ {x y} (p q : Order.Order._<_ P x y) → p ≡ q

module Pred {ℓ : Level} {A : Set ℓ} (P : Order.Order A)
  (unique : Unique P) where

  module P = Order.Order P

  equal : {x : A} {u v : P.Pred x} → proj₁ u ≡ proj₁ v → u ≡ v
  equal {u = y , p} {v = .y , q} refl = cong (y ,_) (unique p q)

module Along {ℓ : Level} {A B : Set ℓ}
  {P : Order.Order A} {Q : Order.Order B}
  (f : Maps.Initial P Q) (p : Unique P) (q : Unique Q) where

  module P = Order.Order P
  module Q = Order.Order Q
  module F = Maps.Initial f
  module Left = Pred P p
  module Right = Pred Q q

  to : (x : A) → P.Pred x → Q.Pred (F.map x)
  to x (y , r) = F.map y , F.strict r

  from : (x : A) → Q.Pred (F.map x) → P.Pred x
  from x (b , r) with F.lower x b r
  ... | a , s = a , F.reflect (subst (λ y → y Q.< F.map x) (sym s) r)

  point : (x : A) (z : Q.Pred (F.map x)) → F.map (proj₁ (from x z)) ≡ proj₁ z
  point x (b , r) with F.lower x b r
  ... | a , s = s

  exact : (x : A) → P.Pred x ≅ Q.Pred (F.map x)
  exact x = record
    { forward = to x ; backward = from x
    ; backward-forward = λ z → Left.equal (F.injective (point x (to x z)))
    ; forward-backward = λ z → Right.equal (point x z)
    }

  strict : {x : A} {u v : P.Pred x} → proj₁ u P.< proj₁ v
    → proj₁ (to x u) Q.< proj₁ (to x v)
  strict = F.strict

  reflect : {x : A} {u v : P.Pred x}
    → proj₁ (to x u) Q.< proj₁ (to x v) → proj₁ u P.< proj₁ v
  reflect = F.reflect

  inverse-strict : {x : A} {u v : Q.Pred (F.map x)} → proj₁ u Q.< proj₁ v
    → proj₁ (from x u) P.< proj₁ (from x v)
  inverse-strict {x} {u} {v} r = F.reflect
    (subst₂ Q._<_ (sym (point x u)) (sym (point x v)) r)

-- An ordered sum over ℕ has unique witnesses when every block does.
module Sum {A : ℕ → Set} (P : (n : ℕ) → Order.Order (A n))
  (unique : (n : ℕ) → Unique (P n)) where

  module S = Order.Sum Order.natural P

  private
    Cell : Σ ℕ A → Σ ℕ A → Set
    Cell (n , x) (m , y) = n < m ⊎
      Σ (n ≡ m) (λ r → Order.Order._<_ (P m) (subst A r x) y)

    to : ∀ {x y} → x S.< y → Cell x y
    to (S.earlier p) = inj₁ p
    to (S.within n p) = inj₂ (refl , p)

    from : ∀ {x y} → Cell x y → x S.< y
    from (inj₁ p) = S.earlier p
    from {n , x} (inj₂ (refl , p)) = S.within n p

    recover : ∀ {x y} (p : x S.< y) → from (to p) ≡ p
    recover (S.earlier p) = refl
    recover (S.within n p) = refl

    equal : ∀ {n m} {x : A n} {y : A m}
      {u v : Σ (n ≡ m) (λ r → Order.Order._<_ (P m) (subst A r x) y)}
      → proj₁ u ≡ proj₁ v → u ≡ v
    equal {m = m} {u = r , p} {v = .r , q} refl = cong (r ,_) (unique m p q)

    cells : ∀ {x y} (p q : Cell x y) → p ≡ q
    cells (inj₁ p) (inj₁ q) = cong inj₁ (Nat.≤-irrelevant p q)
    cells (inj₁ p) (inj₂ (r , q)) = ⊥-elim (Nat.<-irrefl r p)
    cells (inj₂ (r , p)) (inj₁ q) = ⊥-elim (Nat.<-irrefl r q)
    cells (inj₂ (r , p)) (inj₂ (s , q)) =
      cong inj₂ (equal (Nat.≡-irrelevant r s))

  witnesses : Unique S.order
  witnesses p q = trans (sym (recover p))
    (trans (cong from (cells (to p) (to q))) (recover q))
