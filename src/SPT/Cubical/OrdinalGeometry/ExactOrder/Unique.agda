{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.ExactOrder.Unique where

-- Uniqueness of strict-order witnesses for an exact order, as a
-- hypothesis.  Under it, predecessors are recovered from their endpoints,
-- isomorphisms act on predecessors, and ordered sums over ℕ keep it.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Isomorphisms using (_≅_)
open import SPT.Cubical.Foundation.Nat.Arithmetic using (≤ℕˢ-is-proposition)
open import SPT.Cubical.Foundation.Nat.Identifications using
  ( ℕ-identifications-agree )

import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order
import SPT.Cubical.OrdinalGeometry.ExactOrder.Maps as Maps

-- Any two witnesses of x < y are equal.  It is a hypothesis, not a field
-- of Order: the comparison witnesses of an order need not be unique.
Unique : ∀ {ℓ} {A : Set ℓ} → Order.Order A → Set ℓ
Unique P = ∀ {x y} (p q : Order.Order._<_ P x y) → p ＝ q

module Pred {ℓ : Level} {A : Set ℓ} (P : Order.Order A)
  (unique : Unique P) where

  module P = Order.Order P

  equal : {x : A} {u v : P.Pred x} → pr₁ u ＝ pr₁ v → u ＝ v
  equal {u = y , p} {v = .y , q} refl = ap (y ,_) (unique p q)

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
  ... | a , s = a , F.reflect (transport (λ y → y Q.< F.map x) (s ⁻¹) r)

  point : (x : A) (z : Q.Pred (F.map x)) → F.map (pr₁ (from x z)) ＝ pr₁ z
  point x (b , r) with F.lower x b r
  ... | a , s = s

  exact : (x : A) → P.Pred x ≅ Q.Pred (F.map x)
  exact x = record
    { forward = to x ; backward = from x
    ; backward-forward = λ z → Left.equal (F.injective (point x (to x z)))
    ; forward-backward = λ z → Right.equal (point x z)
    }

  strict : {x : A} {u v : P.Pred x} → pr₁ u P.< pr₁ v
    → pr₁ (to x u) Q.< pr₁ (to x v)
  strict = F.strict

  reflect : {x : A} {u v : P.Pred x}
    → pr₁ (to x u) Q.< pr₁ (to x v) → pr₁ u P.< pr₁ v
  reflect = F.reflect

  inverse-strict : {x : A} {u v : Q.Pred (F.map x)} → pr₁ u Q.< pr₁ v
    → pr₁ (from x u) P.< pr₁ (from x v)
  inverse-strict {x} {u} {v} r = F.reflect
    (transport₂ Q._<_ (point x u ⁻¹) (point x v ⁻¹) r)

-- An ordered sum over ℕ has unique witnesses when every block does.
module Sum {A : ℕ → Set} (P : (n : ℕ) → Order.Order (A n))
  (unique : (n : ℕ) → Unique (P n)) where

  module S = Order.Sum Order.natural P

  private
    Cell : Σ ℕ A → Σ ℕ A → Set
    Cell (n , x) (m , y) = n <ℕˢ m ⊎
      Σ (n ＝ m) (λ r → Order.Order._<_ (P m) (transport A r x) y)

    to : ∀ {x y} → x S.< y → Cell x y
    to (S.earlier p) = inl p
    to (S.within n p) = inr (refl , p)

    from : ∀ {x y} → Cell x y → x S.< y
    from (inl p) = S.earlier p
    from {n , x} (inr (refl , p)) = S.within n p

    recover : ∀ {x y} (p : x S.< y) → from (to p) ＝ p
    recover (S.earlier p) = refl
    recover (S.within n p) = refl

    equal : ∀ {n m} {x : A n} {y : A m}
      {u v : Σ (n ＝ m) (λ r → Order.Order._<_ (P m) (transport A r x) y)}
      → pr₁ u ＝ pr₁ v → u ＝ v
    equal {m = m} {u = r , p} {v = .r , q} refl = ap (r ,_) (unique m p q)

    cells : ∀ {x y} (p q : Cell x y) → p ＝ q
    cells (inl p) (inl q) = ap inl (≤ℕˢ-is-proposition p q)
    cells {n , x} {m , y} (inl p) (inr (r , q)) =
      𝟘-elim (<ℕˢ-irrefl m (transport (λ k → k <ℕˢ m) r p))
    cells {n , x} {m , y} (inr (r , p)) (inl q) =
      𝟘-elim (<ℕˢ-irrefl m (transport (λ k → k <ℕˢ m) r q))
    cells (inr (r , p)) (inr (s , q)) =
      ap inr (equal (ℕ-identifications-agree r s))

  witnesses : Unique S.order
  witnesses p q = recover p ⁻¹
    ∙ (ap from (cells (to p) (to q)) ∙ recover q)
