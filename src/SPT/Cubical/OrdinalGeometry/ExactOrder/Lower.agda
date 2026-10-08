{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.ExactOrder.Lower where

-- The points below x of an exact order with unique witnesses, as an exact
-- order: its enumeration, its unique witnesses, and its initial map into
-- the original order.

open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; subst)

open import SPT.Cubical.Core.WellFounded using (WellFounded)
open import SPT.Cubical.Core.WellFounded.Pullback using (pullback-wf)
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

    infix 4 _<_
    _<_ : Carrier → Carrier → Set
    u < v = proj₁ u P.< proj₁ v

    private
      compare : (u v : Carrier) → u < v ⊎ (u ≡ v ⊎ v < u)
      compare u v with P.compare (proj₁ u) (proj₁ v)
      ... | inj₁ p = inj₁ p
      ... | inj₂ (inj₁ p) = inj₂ (inj₁ (Equality.equal p))
      ... | inj₂ (inj₂ p) = inj₂ (inj₂ p)

      select : A → Maybe Carrier
      select y with P.compare y x
      ... | inj₁ p = just (y , p)
      ... | inj₂ _ = nothing

      selected : (u : Carrier) → select (proj₁ u) ≡ just u
      selected (y , p) with P.compare y x
      ... | inj₁ q = cong just (Equality.equal refl)
      ... | inj₂ (inj₁ q) = ⊥-elim
        (P.irrefl x (subst (λ z → z P.< x) q p))
      ... | inj₂ (inj₂ q) = ⊥-elim (P.irrefl x (P.trans q p))

    enum : ℕ → Maybe Carrier
    enum n with P.enum n
    ... | nothing = nothing
    ... | just y = select y

    covers : (u : Carrier) → Σ ℕ (λ n → enum n ≡ just u)
    covers (y , p) with P.covers y
    ... | n , q = n , found
      where
      found : enum n ≡ just (y , p)
      found rewrite q = selected (y , p)

    abstract
      well-founded : WellFounded _<_
      well-founded = pullback-wf {rank = proj₁} P.wf

    order : Order.Order Carrier
    order = record
      { _<_ = _<_ ; trans = P.trans ; wf = well-founded
      ; compare = compare ; enum = enum ; covers = covers
      }

    witnesses : Unique.Unique order
    witnesses = unique

    initial : Maps.Initial order P
    initial = record
      { map = proj₁ ; strict = λ p → p
      ; lower = λ u y p → (y , P.trans p (proj₂ u)) , refl
      }
