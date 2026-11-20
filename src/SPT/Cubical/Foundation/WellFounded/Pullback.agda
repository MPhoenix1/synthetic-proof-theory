{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.WellFounded.Pullback where

-- The pullback of a relation `_<_` on `B` along a map `f : A → B` relates `y`
-- to `x` when `f y < f x`. The pullback of a well-founded relation is
-- well-founded, since `x` is accessible in the pullback when `f x` is
-- accessible (`accessible-in-pullback`). This gives a second proof that a
-- rewrite system with a rank terminates: its reversed steps form a subrelation
-- of the pullback of the well-founded relation along the rank
-- (`rank-steps-descend`).

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Accessibility using
  ( is-accessible; acc; is-well-founded; Well-Founded-Relation; below
  ; below-is-well-founded )
open import SPT.Cubical.Foundation.WellFounded.Subrelation using
  (_⊆_; subrelations-are-well-founded)
open import SPT.Cubical.Foundation.WellFounded.Rewriting using
  (Rewrite-System; predecessor; terminates; Rank; rank-of; decreases)

module _ {ℓ κ μ : Level} {A : Set ℓ} {B : Set κ} (f : A → B)
  (_<_ : B → B → Set μ) where

  pullback-relation : A → A → Set μ
  pullback-relation y x = f y < f x

------------------------------------------------------------------------
-- Properties

module _ {ℓ κ μ : Level} {A : Set ℓ} {B : Set κ} (f : A → B)
  (_<_ : B → B → Set μ) where

  accessible-in-pullback : (x : A) → is-accessible _<_ (f x) →
    is-accessible (pullback-relation f _<_) x
  accessible-in-pullback x (acc smaller) =
    acc (λ y y<x → accessible-in-pullback y (smaller (f y) y<x))

  pullback-is-well-founded : is-well-founded _<_ →
    is-well-founded (pullback-relation f _<_)
  pullback-is-well-founded well-founded x =
    accessible-in-pullback x (well-founded (f x))

------------------------------------------------------------------------
-- Termination through the pullback

module _ {ℓ κ ℓ′ κ′ : Level} {R : Rewrite-System ℓ κ}
  {O : Well-Founded-Relation ℓ′ κ′} where

  rank-steps-descend : (r : Rank R O) →
    predecessor R ⊆ pullback-relation (rank-of r) (below O)
  rank-steps-descend r {y} {x} step = decreases r x y step

  terminates-by-rank-via-pullback : Rank R O → terminates R
  terminates-by-rank-via-pullback r =
    subrelations-are-well-founded (rank-steps-descend r)
      (pullback-is-well-founded (rank-of r) (below O)
        (below-is-well-founded O))
