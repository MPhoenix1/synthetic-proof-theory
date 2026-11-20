{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Linear.Exponential where

-- An exponential layer `L` gives exponents and coefficients, a predicate `Good`
-- of admissible coefficients, and an order on each. An exponential normal form
-- over `L` is a finite sequential history whose steps prepend a pair (exponent,
-- coefficient) whose exponent exceeds the exponent of the previous head: its
-- support decreases. The state after `n` steps records the current leading
-- pair; the history below it records the tail. Normal forms are built from the
-- empty one by `prepend`, which requires the tail to lie below the new head
-- (`TailBelow`).
--
-- Pairs are compared lexicographically, as the constant-fiber case of the
-- dependent lexicographic order (`PairLess`). Normal forms presented by
-- `prepend` are compared by the formation order `_≺ᴱ_`: the empty form lies
-- below every nonempty one, a smaller leading pair decides, and equal leading
-- pairs pass to the tails. Its transitivity and well-foundedness are proved in
-- `Exponential.Order`, for a variant that reads the final node of the history
-- directly.

open import SPT.Base hiding (length)
open import SPT.Foundation.WellFounded.Lexicographic using
  ( dependent-lexicographic; earlier; within
  ; dependent-lexicographic-is-transitive )
open import SPT.Foundation.Linear.History using
  (SequentialHistory; sequential-seed-history; sequential-next-history)

------------------------------------------------------------------------
-- Layers

record Layer (ℓe ℓc ℓg ℓre ℓrc : Level) :
  Set (lsuc (ℓe ⊔ ℓc ⊔ ℓg ⊔ ℓre ⊔ ℓrc)) where
  constructor layer
  infix 30 _≺e_ _≺c_
  field
    Exponent : Set ℓe
    Coefficient : Set ℓc
    Good : Coefficient → Set ℓg
    _≺e_ : Exponent → Exponent → Set ℓre
    _≺c_ : Coefficient → Coefficient → Set ℓrc

------------------------------------------------------------------------
-- Normal forms of one layer

module _ {ℓe ℓc ℓg ℓre ℓrc : Level} (L : Layer ℓe ℓc ℓg ℓre ℓrc) where

  open Layer L

  data State : ℕ → Set (ℓe ⊔ ℓc) where
    empty-state : State zero
    head-state : {n : ℕ} → Exponent → Coefficient → State (suc n)

  data Step : (n : ℕ) → State n → State (suc n) →
    Set (ℓe ⊔ ℓc ⊔ ℓg ⊔ ℓre) where
    first-step : (exponent : Exponent) (coefficient : Coefficient) →
      Good coefficient →
      Step zero empty-state (head-state exponent coefficient)
    prepend-step : {n : ℕ} (head-exponent tail-exponent : Exponent)
      (head-coefficient tail-coefficient : Coefficient) →
      Good head-coefficient → tail-exponent ≺e head-exponent →
      Step (suc n) (head-state tail-exponent tail-coefficient)
        (head-state head-exponent head-coefficient)

  record Exponential : Set (ℓe ⊔ ℓc ⊔ ℓg ⊔ ℓre) where
    constructor exponential
    field
      length : ℕ
      endpoint : State length
      support : SequentialHistory Step empty-state length endpoint

  open Exponential public

  zeroᴱ : Exponential
  zeroᴱ =
    exponential zero empty-state (sequential-seed-history Step empty-state)

------------------------------------------------------------------------
-- Formation by prepend

  data TailBelow (head : Exponent) : Exponential →
    Set (ℓe ⊔ ℓc ⊔ ℓg ⊔ ℓre) where
    below-empty :
      (history : SequentialHistory Step empty-state zero empty-state) →
      TailBelow head (exponential zero empty-state history)
    below-head : {n : ℕ} (tail-exponent : Exponent)
      (tail-coefficient : Coefficient)
      (history : SequentialHistory Step empty-state (suc n)
        (head-state tail-exponent tail-coefficient)) →
      tail-exponent ≺e head →
      TailBelow head
        (exponential (suc n) (head-state tail-exponent tail-coefficient)
          history)

  prepend : (head : Exponent) (coefficient : Coefficient) →
    Good coefficient → (tail : Exponential) → TailBelow head tail →
    Exponential
  prepend head coefficient good .(exponential zero empty-state history)
    (below-empty history) =
    exponential (suc zero) (head-state head coefficient)
      (sequential-next-history Step history
        (first-step head coefficient good))
  prepend head coefficient good
    .(exponential (suc n) (head-state tail-exponent tail-coefficient)
      history)
    (below-head {n} tail-exponent tail-coefficient history decrease) =
    exponential (suc (suc n)) (head-state head coefficient)
      (sequential-next-history Step history
        (prepend-step head tail-exponent coefficient tail-coefficient good
          decrease))

  singleton : (exponent : Exponent) (coefficient : Coefficient) →
    Good coefficient → Exponential
  singleton exponent coefficient good =
    prepend exponent coefficient good zeroᴱ
      (below-empty (sequential-seed-history Step empty-state))

------------------------------------------------------------------------
-- Comparison of pairs

  PairLess : Exponent → Coefficient → Exponent → Coefficient →
    Set (ℓe ⊔ ℓc ⊔ ℓre ⊔ ℓrc)
  PairLess left left-coefficient right right-coefficient =
    dependent-lexicographic (λ (_ : Exponent) → Coefficient) _≺e_
      (λ _ → _≺c_) (left , left-coefficient) (right , right-coefficient)

pattern exponent-less decrease = earlier decrease
pattern coefficient-less exponent decrease = within exponent decrease

------------------------------------------------------------------------
-- The formation order

module _ {ℓe ℓc ℓg ℓre ℓrc : Level} {L : Layer ℓe ℓc ℓg ℓre ℓrc} where

  open Layer L

  infix 30 _≺ᴱ_

  data _≺ᴱ_ : Exponential L → Exponential L →
    Set (ℓe ⊔ ℓc ⊔ ℓg ⊔ ℓre ⊔ ℓrc) where
    proper-prefix :
      (left-empty : SequentialHistory (Step L) empty-state zero
        empty-state)
      (right-head : Exponent) (right-coefficient : Coefficient)
      (right-good : Good right-coefficient) (right-tail : Exponential L)
      (right-below : TailBelow L right-head right-tail) →
      exponential zero empty-state left-empty
        ≺ᴱ prepend L right-head right-coefficient right-good right-tail
          right-below
    first-difference : (left-head right-head : Exponent)
      (left-coefficient right-coefficient : Coefficient)
      (left-tail right-tail : Exponential L)
      (left-good : Good left-coefficient)
      (right-good : Good right-coefficient)
      (left-below : TailBelow L left-head left-tail)
      (right-below : TailBelow L right-head right-tail) →
      PairLess L left-head left-coefficient right-head right-coefficient →
      prepend L left-head left-coefficient left-good left-tail left-below
        ≺ᴱ prepend L right-head right-coefficient right-good right-tail
          right-below
    common-head : (head : Exponent) (coefficient : Coefficient)
      (left-tail right-tail : Exponential L)
      (left-good right-good : Good coefficient)
      (left-below : TailBelow L head left-tail)
      (right-below : TailBelow L head right-tail) →
      left-tail ≺ᴱ right-tail →
      prepend L head coefficient left-good left-tail left-below
        ≺ᴱ prepend L head coefficient right-good right-tail right-below

------------------------------------------------------------------------
-- Properties

module _ {ℓe ℓc ℓg ℓre ℓrc : Level} (L : Layer ℓe ℓc ℓg ℓre ℓrc) where

  open Layer L

  zero-below-singleton : (exponent : Exponent)
    (coefficient : Coefficient) (good : Good coefficient) →
    zeroᴱ L ≺ᴱ singleton L exponent coefficient good
  zero-below-singleton exponent coefficient good =
    proper-prefix (sequential-seed-history (Step L) empty-state)
      exponent coefficient good (zeroᴱ L)
      (below-empty (sequential-seed-history (Step L) empty-state))

  pair-trans :
    ({left middle right : Exponent} →
      left ≺e middle → middle ≺e right → left ≺e right) →
    ({left middle right : Coefficient} →
      left ≺c middle → middle ≺c right → left ≺c right) →
    {left-exponent middle-exponent right-exponent : Exponent}
    {left-coefficient middle-coefficient right-coefficient : Coefficient} →
    PairLess L left-exponent left-coefficient middle-exponent
      middle-coefficient →
    PairLess L middle-exponent middle-coefficient right-exponent
      right-coefficient →
    PairLess L left-exponent left-coefficient right-exponent
      right-coefficient
  pair-trans trans-exponent trans-coefficient =
    dependent-lexicographic-is-transitive (λ (_ : Exponent) → Coefficient)
      _≺e_ (λ _ → _≺c_) trans-exponent (λ _ → trans-coefficient)
