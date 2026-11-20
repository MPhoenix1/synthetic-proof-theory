{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.ExactOrder.Base where

-- Exact orders: countable strict well-orders compared up to equality of
-- points, with an enumeration of all points.  The natural numbers, and
-- dependent ordered sums with their decomposition of predecessors.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Accessibility using
  ( accessible-points-have-no-loops; is-well-founded )
open import SPT.Cubical.Foundation.Nat.WellFounded using (wfℕˢ)
open import SPT.Cubical.Foundation.WellFounded.Lexicographic using
  ( dependent-lexicographic; dependent-lexicographic-is-transitive
  ; dependent-lexicographic-is-well-founded )

-- A countable strict well-order on a type A: comparison is trichotomy up
-- to equality in A, so a family over A can be used without transport
-- along an equivalence, and the enumeration lists every point.
record Order {ℓ : Level} (A : Set ℓ) : Set (lsuc ℓ) where
  infix 30 _<_
  field
    _<_ : A → A → Set ℓ
    trans : ∀ {x y z} → x < y → y < z → x < z
    wf : is-well-founded _<_
    compare : (x y : A) → Trichotomy _＝_ _<_ x y
    enum : ℕ → Maybe A
    covers : (x : A) → Σ ℕ (λ n → enum n ＝ just x)

  Pred : A → Set ℓ
  Pred x = Σ A (λ y → y < x)

  irrefl : (x : A) → x < x → 𝟘
  irrefl x = accessible-points-have-no-loops (wf x)

  Least : A → Set ℓ
  Least x = (y : A) → y < x → 𝟘

natural : Order ℕ
natural = record
  { _<_ = _<ℕˢ_
  ; trans = <ℕˢ-trans
  ; wf = wfℕˢ
  ; compare = <ℕˢ-trichotomy
  ; enum = just
  ; covers = λ n → n , refl
  }

------------------------------------------------------------------------
-- Dependent ordered sums and their exact predecessor decomposition

module Sum {ℓ : Level} {A : Set ℓ} {B : A → Set ℓ}
  (P : Order A) (Q : (a : A) → Order (B a)) where

  infix 30 _<_

  _<_ : Σ A B → Σ A B → Set ℓ
  _<_ = dependent-lexicographic B (Order._<_ P) (λ a → Order._<_ (Q a))

  open SPT.Cubical.Foundation.WellFounded.Lexicographic public using
    (earlier; within)

  private
    compare : (x y : Σ A B) → Trichotomy _＝_ _<_ x y
    compare (a , x) (b , y) with Order.compare P a b
    ... | inl p = inl (earlier p)
    ... | inr (inr p) = inr (inr (earlier p))
    ... | inr (inl refl) with Order.compare (Q a) x y
    ...   | inl p = inl (within a p)
    ...   | inr (inl p) = inr (inl (ap (a ,_) p))
    ...   | inr (inr p) = inr (inr (within a p))

    at : ℕ → ℕ → Maybe (Σ A B)
    at m n with Order.enum P m
    ... | nothing = nothing
    ... | just a with Order.enum (Q a) n
    ...   | nothing = nothing
    ...   | just b = just (a , b)

    hit : (a : A) (b : B a) (m n : ℕ)
      → Order.enum P m ＝ just a → Order.enum (Q a) n ＝ just b
      → at m n ＝ just (a , b)
    hit a b m n p q rewrite p | q = refl

    enum : ℕ → Maybe (Σ A B)
    enum n = at (pr₁ (ℕ-unpair n)) (pr₂ (ℕ-unpair n))

    covers : (x : Σ A B) → Σ ℕ (λ n → enum n ＝ just x)
    covers (a , b) with Order.covers P a | Order.covers (Q a) b
    ... | m , p | n , q = ℕ-pair m n , found
      where
      found : enum (ℕ-pair m n) ＝ just (a , b)
      found rewrite ℕ-unpair-pair m n = hit a b m n p q

  abstract
    well-founded : is-well-founded _<_
    well-founded =
      dependent-lexicographic-is-well-founded B (Order._<_ P)
        (λ a → Order._<_ (Q a)) (Order.wf P) (λ a → Order.wf (Q a))

  order : Order (Σ A B)
  order = record
    { _<_ = _<_
    ; trans =
        dependent-lexicographic-is-transitive B (Order._<_ P)
          (λ a → Order._<_ (Q a)) (Order.trans P) (λ a → Order.trans (Q a))
    ; wf = well-founded
    ; compare = compare
    ; enum = enum
    ; covers = covers
    }

  -- A predecessor of (a , b) lies in an earlier block or below b in the
  -- same block; `split` and `join` are mutually inverse.
  Parts : (z : Σ A B) → Set ℓ
  Parts (a , b) =
    Σ (Order.Pred P a) (λ p → B (pr₁ p)) ⊎ Order.Pred (Q a) b

  split : (z : Σ A B) → Order.Pred order z → Parts z
  split (a , b) ((a′ , b′) , earlier p) = inl ((a′ , p) , b′)
  split (a , b) ((.a , b′) , within .a p) = inr (b′ , p)

  join : (z : Σ A B) → Parts z → Order.Pred order z
  join (a , b) (inl ((a′ , p) , b′)) = (a′ , b′) , earlier p
  join (a , b) (inr (b′ , p)) = (a , b′) , within a p

  join-split : (z : Σ A B) (p : Order.Pred order z) → join z (split z p) ＝ p
  join-split (a , b) ((a′ , b′) , earlier p) = refl
  join-split (a , b) ((.a , b′) , within .a p) = refl

  split-join : (z : Σ A B) (p : Parts z) → split z (join z p) ＝ p
  split-join (a , b) (inl ((a′ , p) , b′)) = refl
  split-join (a , b) (inr (b′ , p)) = refl
