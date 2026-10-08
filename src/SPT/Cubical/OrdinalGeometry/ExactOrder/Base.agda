{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.ExactOrder.Base where

-- Exact orders: countable strict well-orders compared up to equality of
-- points, with an enumeration of all points.  The natural numbers, and
-- dependent ordered sums with their decomposition of predecessors.

open import Agda.Primitive using (Level; lsuc)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ)
import Data.Nat.Base as Nat
import Data.Nat.Properties as Nat
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import SPT.Cubical.Core.WellFounded using (WellFounded; acc↛loop)
import SPT.Cubical.Core.WellFounded.Lex as Lex
open import SPT.Cubical.Core.Nat.WellFounded using (wfℕˢ)
open import SPT.Cubical.Core.Nat.Pairing using (pair; unpair; unpair-pair)

-- A countable strict well-order on a type A: comparison is trichotomy up
-- to equality in A, so a family over A can be used without transport
-- along an equivalence, and the enumeration lists every point.
record Order {ℓ : Level} (A : Set ℓ) : Set (lsuc ℓ) where
  infix 4 _<_
  field
    _<_ : A → A → Set ℓ
    trans : ∀ {x y z} → x < y → y < z → x < z
    wf : WellFounded _<_
    compare : (x y : A) → x < y ⊎ (x ≡ y ⊎ y < x)
    enum : ℕ → Maybe A
    covers : (x : A) → Σ ℕ (λ n → enum n ≡ just x)

  Pred : A → Set ℓ
  Pred x = Σ A (λ y → y < x)

  irrefl : (x : A) → x < x → ⊥
  irrefl x = acc↛loop (wf x)

  Least : A → Set ℓ
  Least x = (y : A) → y < x → ⊥

natural : Order ℕ
natural = record
  { _<_ = Nat._<_
  ; trans = Nat.<-trans
  ; wf = wfℕˢ
  ; compare = compare
  ; enum = just
  ; covers = λ n → n , refl
  }
  where
  compare : (m n : ℕ) → m Nat.< n ⊎ (m ≡ n ⊎ n Nat.< m)
  compare m n with Nat.<-cmp m n
  ... | tri< p _ _ = inj₁ p
  ... | tri≈ _ p _ = inj₂ (inj₁ p)
  ... | tri> _ _ p = inj₂ (inj₂ p)

------------------------------------------------------------------------
-- Dependent ordered sums and their exact predecessor decomposition

module Sum {ℓ : Level} {A : Set ℓ} {B : A → Set ℓ}
  (P : Order A) (Q : (a : A) → Order (B a)) where

  module L = Lex.Dependent B (Order._<_ P) (λ a → Order._<_ (Q a))
  open L public using (_<_; earlier; within)

  private
    compare : (x y : Σ A B) → x < y ⊎ (x ≡ y ⊎ y < x)
    compare (a , x) (b , y) with Order.compare P a b
    ... | inj₁ p = inj₁ (earlier p)
    ... | inj₂ (inj₂ p) = inj₂ (inj₂ (earlier p))
    ... | inj₂ (inj₁ refl) with Order.compare (Q a) x y
    ...   | inj₁ p = inj₁ (within a p)
    ...   | inj₂ (inj₁ p) = inj₂ (inj₁ (cong (a ,_) p))
    ...   | inj₂ (inj₂ p) = inj₂ (inj₂ (within a p))

    at : ℕ → ℕ → Maybe (Σ A B)
    at m n with Order.enum P m
    ... | nothing = nothing
    ... | just a with Order.enum (Q a) n
    ...   | nothing = nothing
    ...   | just b = just (a , b)

    hit : (a : A) (b : B a) (m n : ℕ)
      → Order.enum P m ≡ just a → Order.enum (Q a) n ≡ just b
      → at m n ≡ just (a , b)
    hit a b m n p q rewrite p | q = refl

    enum : ℕ → Maybe (Σ A B)
    enum n = at (proj₁ (unpair n)) (proj₂ (unpair n))

    covers : (x : Σ A B) → Σ ℕ (λ n → enum n ≡ just x)
    covers (a , b) with Order.covers P a | Order.covers (Q a) b
    ... | m , p | n , q = pair m n , found
      where
      found : enum (pair m n) ≡ just (a , b)
      found rewrite unpair-pair m n = hit a b m n p q

  abstract
    well-founded : WellFounded _<_
    well-founded = L.wf (Order.wf P) (λ a → Order.wf (Q a))

  order : Order (Σ A B)
  order = record
    { _<_ = _<_
    ; trans = L.trans (Order.trans P) (λ a → Order.trans (Q a))
    ; wf = well-founded
    ; compare = compare
    ; enum = enum
    ; covers = covers
    }

  -- A predecessor of (a , b) lies in an earlier block or below b in the
  -- same block; `split` and `join` are mutually inverse.
  Parts : (z : Σ A B) → Set ℓ
  Parts (a , b) =
    Σ (Order.Pred P a) (λ p → B (proj₁ p)) ⊎ Order.Pred (Q a) b

  split : (z : Σ A B) → Order.Pred order z → Parts z
  split (a , b) ((a′ , b′) , earlier p) = inj₁ ((a′ , p) , b′)
  split (a , b) ((.a , b′) , within .a p) = inj₂ (b′ , p)

  join : (z : Σ A B) → Parts z → Order.Pred order z
  join (a , b) (inj₁ ((a′ , p) , b′)) = (a′ , b′) , earlier p
  join (a , b) (inj₂ (b′ , p)) = (a , b′) , within a p

  join-split : (z : Σ A B) (p : Order.Pred order z) → join z (split z p) ≡ p
  join-split (a , b) ((a′ , b′) , earlier p) = refl
  join-split (a , b) ((.a , b′) , within .a p) = refl

  split-join : (z : Σ A B) (p : Parts z) → split z (join z p) ≡ p
  split-join (a , b) (inj₁ ((a′ , p) , b′)) = refl
  split-join (a , b) (inj₂ (b′ , p)) = refl
