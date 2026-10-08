{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.WellFounded.Pullback where

-- The pullback of a relation along a map, its well-foundedness, and
-- termination of a rewrite system from a rank into a well-founded relation.

open import Agda.Primitive using (Level)

open import SPT.Cubical.Core.WellFounded
open import SPT.Cubical.Core.WellFounded.Rewrite
open import SPT.Cubical.Core.WellFounded.Termination
open import SPT.Cubical.Core.WellFounded.Rank
open import SPT.Cubical.Core.WellFounded.Subrelation

------------------------------------------------------------------------
-- Pullback relations

PullbackRel :
  {ℓA ℓB ℓr : Level}
  {A : Set ℓA}
  {B : Set ℓB} →
  (rank : A → B) →
  (B → B → Set ℓr) →
  A → A → Set ℓr
PullbackRel rank _<_ y x = rank y < rank x

-- The pullback of a well-founded relation is well founded.

pullback-wf :
  {ℓA ℓB ℓr : Level}
  {A : Set ℓA}
  {B : Set ℓB}
  {rank : A → B}
  {_<_ : B → B → Set ℓr} →
  WellFounded _<_ →
  WellFounded (PullbackRel rank _<_)
pullback-wf {rank = rank} {_<_ = _<_} wf x = go x (wf (rank x))
  where
    go : ∀ x → Acc _<_ (rank x) → Acc (PullbackRel rank _<_) x
    go x (acc smaller) =
      acc λ y ρy<ρx →
        go y (smaller (rank y) ρy<ρx)

-- A rank decreasing along every step gives termination: each step lies in
-- the pullback of the well-founded order along the rank.

rank→term-via-pullback :
  {ℓA ℓR ℓO ℓ< : Level}
  {R : Rewrite ℓA ℓR}
  {O : WFRel ℓO ℓ<} →
  Rank R O → Termination.Term R
rank→term-via-pullback {R = R} {O = O} rank =
  subrel-wf step⊆pullback
    (pullback-wf {rank = K.ρ} {_<_ = WO._<_} WO.wf)
  where
    module TR = Termination R
    module WO = WFRel O
    module K  = Rank rank

    step⊆pullback : SubRel TR._≺_ (PullbackRel K.ρ WO._<_)
    step⊆pullback {x = small} {y = big} big↝small =
      K.decreases big small big↝small
