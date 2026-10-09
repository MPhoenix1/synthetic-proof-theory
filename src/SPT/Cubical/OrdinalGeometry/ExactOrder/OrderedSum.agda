{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.ExactOrder.OrderedSum where

-- Exact countable ordinals and their dependent ordered sums. The sum keeps
-- its index and fiber point literally; its predecessors split into earlier
-- complete fibers and predecessors within the current fiber. Fiberwise
-- order equivalences lift through sums, including an equivalent new index
-- order with corresponding dependent fibers.

open import Agda.Primitive using (Level; lsuc)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ; zero)
open import Data.Product using (Σ; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Level using (Lift; lift; lower)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; sym; subst)

open import SPT.Cubical.Core.WellFounded using (Acc; acc)
import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order
import SPT.Cubical.OrdinalGeometry.ExactOrder.Maps as Maps

private
  variable
    ℓ : Level

record Ordinal (ℓ : Level) : Set (lsuc ℓ) where
  constructor ordinal
  field
    Carrier : Set ℓ
    order : Order.Order Carrier

open Ordinal public

empty : Ordinal ℓ
empty = ordinal ⊥ record
  { _<_ = λ _ _ → ⊥
  ; trans = λ ()
  ; wf = λ ()
  ; compare = λ ()
  ; enum = λ _ → nothing
  ; covers = λ ()
  }

unit : Ordinal ℓ
unit = ordinal ⊤ record
  { _<_ = λ _ _ → ⊥
  ; trans = λ ()
  ; wf = λ _ → acc (λ _ ())
  ; compare = λ { tt tt → inj₂ (inj₁ refl) }
  ; enum = λ _ → just tt
  ; covers = λ { tt → zero , refl }
  }

natural : Ordinal ℓ
natural {ℓ} = ordinal (Lift ℓ ℕ) record
  { _<_ = _<_
  ; trans = λ p q → lift
      (Order.Order.trans Order.natural (lower p) (lower q))
  ; wf = λ { (lift n) → accessible n (Order.Order.wf Order.natural n) }
  ; compare = compare
  ; enum = λ n → just (lift n)
  ; covers = λ { (lift n) → n , refl }
  }
  where
  _<_ : Lift ℓ ℕ → Lift ℓ ℕ → Set ℓ
  x < y = Lift ℓ (Order.Order._<_ Order.natural (lower x) (lower y))

  accessible : (n : ℕ) → Acc (Order.Order._<_ Order.natural) n
    → Acc _<_ (lift n)
  accessible n (acc smaller) = acc λ { (lift m) (lift p) →
    accessible m (smaller m p) }

  compare : (x y : Lift ℓ ℕ) → x < y ⊎ (x ≡ y ⊎ y < x)
  compare (lift m) (lift n) with Order.Order.compare Order.natural m n
  ... | inj₁ p = inj₁ (lift p)
  ... | inj₂ (inj₁ p) = inj₂ (inj₁ (cong lift p))
  ... | inj₂ (inj₂ p) = inj₂ (inj₂ (lift p))

sum : (P : Ordinal ℓ) → (Carrier P → Ordinal ℓ) → Ordinal ℓ
sum P Q = ordinal (Σ (Carrier P) (λ a → Carrier (Q a)))
  (Order.Sum.order (order P) (λ a → order (Q a)))

------------------------------------------------------------------------
-- Exact predecessor decomposition

Pred : (P : Ordinal ℓ) → Carrier P → Set ℓ
Pred P = Order.Order.Pred (order P)

Parts : (P : Ordinal ℓ) (Q : Carrier P → Ordinal ℓ)
  → Carrier (sum P Q) → Set ℓ
Parts P Q = Order.Sum.Parts (order P) (λ a → order (Q a))

split : (P : Ordinal ℓ) (Q : Carrier P → Ordinal ℓ)
  (z : Carrier (sum P Q)) → Pred (sum P Q) z → Parts P Q z
split P Q = Order.Sum.split (order P) (λ a → order (Q a))

join : (P : Ordinal ℓ) (Q : Carrier P → Ordinal ℓ)
  (z : Carrier (sum P Q)) → Parts P Q z → Pred (sum P Q) z
join P Q = Order.Sum.join (order P) (λ a → order (Q a))

join-split : (P : Ordinal ℓ) (Q : Carrier P → Ordinal ℓ)
  (z : Carrier (sum P Q)) (p : Pred (sum P Q) z)
  → join P Q z (split P Q z p) ≡ p
join-split P Q = Order.Sum.join-split (order P) (λ a → order (Q a))

split-join : (P : Ordinal ℓ) (Q : Carrier P → Ordinal ℓ)
  (z : Carrier (sum P Q)) (p : Parts P Q z)
  → split P Q z (join P Q z p) ≡ p
split-join P Q = Order.Sum.split-join (order P) (λ a → order (Q a))

------------------------------------------------------------------------
-- Equivalences keeping the sum index

identity : (P : Ordinal ℓ) → Maps.Iso (order P) (order P)
identity P = record
  { equivalence = Maps.from-inverses (λ x → x) (λ x → x)
      (λ _ → refl) (λ _ → refl)
  ; strict = λ p → p
  }

iso : (P : Ordinal ℓ) (Q R : Carrier P → Ordinal ℓ)
  → ((a : Carrier P) → Maps.Iso (order (Q a)) (order (R a)))
  → Maps.Iso (order (sum P Q)) (order (sum P R))
iso P Q R e = record
  { equivalence = Maps.from-inverses to from from-to to-from
  ; strict = strict
  }
  where
  module Source = Order.Sum (order P) (λ a → order (Q a))
  module Target = Order.Sum (order P) (λ a → order (R a))

  to : Carrier (sum P Q) → Carrier (sum P R)
  to (a , b) = a , Maps.Iso.forward (e a) b

  from : Carrier (sum P R) → Carrier (sum P Q)
  from (a , b) = a , Maps.Iso.backward (e a) b

  from-to : (x : Carrier (sum P Q)) → from (to x) ≡ x
  from-to (a , b) = cong (a ,_) (Maps.Iso.backward-forward (e a) b)

  to-from : (x : Carrier (sum P R)) → to (from x) ≡ x
  to-from (a , b) = cong (a ,_) (Maps.Iso.forward-backward (e a) b)

  strict : ∀ {x y} → x Source.< y → to x Target.< to y
  strict (Source.earlier p) = Target.earlier p
  strict (Source.within a p) = Target.within a (Maps.Iso.strict (e a) p)

iso-index : (P : Ordinal ℓ) (Q R : Carrier P → Ordinal ℓ)
  (e : (a : Carrier P) → Maps.Iso (order (Q a)) (order (R a)))
  (x : Carrier (sum P Q))
  → proj₁ (Maps.Iso.forward (iso P Q R e) x) ≡ proj₁ x
iso-index P Q R e (a , b) = refl

------------------------------------------------------------------------
-- Equivalences changing the sum index

-- The index equivalence determines where each complete fiber is compared.
-- Strictness and coverage of the resulting pair map give its equivalence.
congruence : (P Q : Ordinal ℓ) (e : Maps.Iso (order P) (order Q))
  (R : Carrier P → Ordinal ℓ) (S : Carrier Q → Ordinal ℓ)
  → ((x : Carrier P) → Maps.Iso
      (order (R x)) (order (S (Maps.Iso.forward e x))))
  → Maps.Iso (order (sum P R)) (order (sum Q S))
congruence P Q e R S d = record
  { equivalence = Increasing.Onto.exact covers
  ; strict = strict
  }
  where
  module Source = Order.Sum (order P) (λ x → order (R x))
  module Target = Order.Sum (order Q) (λ y → order (S y))

  to : Carrier (sum P R) → Carrier (sum Q S)
  to (x , z) = Maps.Iso.forward e x , Maps.Iso.forward (d x) z

  strict : ∀ {x y} → x Source.< y → to x Target.< to y
  strict (Source.earlier p) = Target.earlier (Maps.Iso.strict e p)
  strict (Source.within x p) = Target.within (Maps.Iso.forward e x)
    (Maps.Iso.strict (d x) p)

  module Increasing = Maps.Strict
    (order (sum P R)) (order (sum Q S)) to strict

  cover : (x : Carrier P) (y : Carrier Q) → Maps.Iso.forward e x ≡ y
    → (w : Carrier (S y))
    → Σ (Carrier (sum P R)) (λ z → to z ≡ (y , w))
  cover x .(Maps.Iso.forward e x) refl w =
    (x , Maps.Iso.backward (d x) w) ,
    cong (Maps.Iso.forward e x ,_) (Maps.Iso.forward-backward (d x) w)

  covers : (w : Carrier (sum Q S))
    → Σ (Carrier (sum P R)) (λ z → to z ≡ w)
  covers (y , w) = cover (Maps.Iso.backward e y) y
    (Maps.Iso.forward-backward e y) w

congruence-β : (P Q : Ordinal ℓ) (e : Maps.Iso (order P) (order Q))
  (R : Carrier P → Ordinal ℓ) (S : Carrier Q → Ordinal ℓ)
  (d : (x : Carrier P) → Maps.Iso
    (order (R x)) (order (S (Maps.Iso.forward e x))))
  (x : Carrier P) (z : Carrier (R x))
  → Maps.Iso.forward (congruence P Q e R S d) (x , z)
    ≡ (Maps.Iso.forward e x , Maps.Iso.forward (d x) z)
congruence-β P Q e R S d x z = refl

congruence-index : (P Q : Ordinal ℓ) (e : Maps.Iso (order P) (order Q))
  (R : Carrier P → Ordinal ℓ) (S : Carrier Q → Ordinal ℓ)
  (d : (x : Carrier P) → Maps.Iso
    (order (R x)) (order (S (Maps.Iso.forward e x))))
  (z : Carrier (sum P R))
  → proj₁ (Maps.Iso.forward (congruence P Q e R S d) z)
    ≡ Maps.Iso.forward e (proj₁ z)
congruence-index P Q e R S d (x , z) = refl

-- Pulling the entire family back along the inverse preserves its sum.
reindex : (P Q : Ordinal ℓ) (e : Maps.Iso (order P) (order Q))
  (R : Carrier P → Ordinal ℓ)
  → Maps.Iso (order (sum P R))
      (order (sum Q (λ y → R (Maps.Iso.backward e y))))
reindex P Q e R = congruence P Q e R
  (λ y → R (Maps.Iso.backward e y))
  (λ x → subst (λ y → Maps.Iso (order (R x)) (order (R y)))
    (sym (Maps.Iso.backward-forward e x)) (identity (R x)))
