{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.ExactOrder.Lower where

-- The points below x of an exact order with unique witnesses, as an exact
-- order: its enumeration, its unique witnesses, and its initial map into
-- the original order.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Accessibility using (is-well-founded)
open import SPT.Cubical.Foundation.WellFounded.Pullback using
  ( pullback-is-well-founded )

import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order
import SPT.Cubical.OrdinalGeometry.ExactOrder.Maps as Maps
import SPT.Cubical.OrdinalGeometry.ExactOrder.Unique as Unique

-- The carrier is Σ y. y < x, compared up to equality: by uniqueness of
-- witnesses, two predecessors with the same endpoint are equal.  The order
-- is the original order on endpoints.
module Segments {A : Set} (P : Order.Order A) (unique : Unique.Unique P) where

  module P = Order.Order P
  module Equality = Unique.Pred P unique

  module Below (x : A) where

    Carrier : Set
    Carrier = P.Pred x

    infix 30 _<_
    _<_ : Carrier → Carrier → Set
    u < v = pr₁ u P.< pr₁ v

    private
      compare : (u v : Carrier) → u < v ⊎ ((u ＝ v) ⊎ v < u)
      compare u v with P.compare (pr₁ u) (pr₁ v)
      ... | inl p = inl p
      ... | inr (inl p) = inr (inl (Equality.equal p))
      ... | inr (inr p) = inr (inr p)

      select : A → Maybe Carrier
      select y with P.compare y x
      ... | inl p = just (y , p)
      ... | inr _ = nothing

      selected : (u : Carrier) → select (pr₁ u) ＝ just u
      selected (y , p) with P.compare y x
      ... | inl q = ap just (Equality.equal refl)
      ... | inr (inl q) = 𝟘-elim
        (P.irrefl x (transport (λ z → z P.< x) q p))
      ... | inr (inr q) = 𝟘-elim (P.irrefl x (P.trans q p))

    enum : ℕ → Maybe Carrier
    enum n with P.enum n
    ... | nothing = nothing
    ... | just y = select y

    covers : (u : Carrier) → Σ ℕ (λ n → enum n ＝ just u)
    covers (y , p) with P.covers y
    ... | n , q = n , found
      where
      found : enum n ＝ just (y , p)
      found rewrite q = selected (y , p)

    abstract
      well-founded : is-well-founded _<_
      well-founded = pullback-is-well-founded pr₁ P._<_ P.wf

    order : Order.Order Carrier
    order = record
      { _<_ = _<_ ; trans = P.trans ; wf = well-founded
      ; compare = compare ; enum = enum ; covers = covers
      }

    witnesses : Unique.Unique order
    witnesses = unique

    initial : Maps.Initial order P
    initial = record
      { map = pr₁ ; strict = λ p → p
      ; lower = λ u y p → (y , P.trans p (pr₂ u)) , refl
      }
