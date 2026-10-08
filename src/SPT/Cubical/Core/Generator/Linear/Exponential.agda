{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.Generator.Linear.Exponential where

-- Exponential normal forms with decreasing support, stored as finite
-- sequential histories: each step prepends a pair (exponent, coefficient)
-- whose exponent exceeds the previous head.  Formation by `prepend`, and
-- the lexicographic comparison of normal forms presented by `prepend`.

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Sigma using (_,_)
open import Data.Nat using (ℕ; zero; suc)

open import SPT.Cubical.Core.Generator.Linear.History using
  (SequentialHistory; sequential-seed-history; sequential-next-history)
import SPT.Cubical.Core.WellFounded.Lex as Lex

------------------------------------------------------------------------
-- One exponential layer

module Layer
    {ℓe ℓc ℓg ℓre ℓrc : Level}
    (Exponent : Set ℓe)
    (Coefficient : Set ℓc)
    (Good : Coefficient → Set ℓg)
    (_≺e_ : Exponent → Exponent → Set ℓre)
    (_≺c_ : Coefficient → Coefficient → Set ℓrc)
  where

  -- The state after n steps records the current leading pair; the history
  -- below it records the tail.
  data State : ℕ → Set (ℓe ⊔ ℓc) where
    empty-state : State zero
    head-state : {n : ℕ} → Exponent → Coefficient → State (suc n)

  data Step : (n : ℕ) → State n → State (suc n) →
      Set (ℓe ⊔ ℓc ⊔ ℓg ⊔ ℓre) where
    first-step :
        (exponent : Exponent)
        (coefficient : Coefficient)
      → Good coefficient
      → Step zero empty-state (head-state exponent coefficient)

    prepend-step :
        {n : ℕ}
        (head-exponent tail-exponent : Exponent)
        (head-coefficient tail-coefficient : Coefficient)
      → Good head-coefficient
      → tail-exponent ≺e head-exponent
      → Step
          (suc n)
          (head-state tail-exponent tail-coefficient)
          (head-state head-exponent head-coefficient)

  -- A normal form is a finite history whose root is the leading pair; every
  -- later pair has a strictly smaller exponent.
  record Exponential : Set (ℓe ⊔ ℓc ⊔ ℓg ⊔ ℓre) where
    constructor exponential
    field
      length : ℕ
      endpoint : State length
      support : SequentialHistory
        {State = State} {Step = Step}
        empty-state length endpoint

  open Exponential public

  zeroᴱ : Exponential
  zeroᴱ = exponential
    zero
    empty-state
    (sequential-seed-history empty-state)

  -- `TailBelow head tail`: the leading exponent of `tail`, if any, lies
  -- below `head`, so that `prepend` may extend it.
  data TailBelow (head : Exponent) : Exponential →
      Set (ℓe ⊔ ℓc ⊔ ℓg ⊔ ℓre) where
    below-empty :
        (history : SequentialHistory
          {State = State} {Step = Step}
          empty-state zero empty-state)
      → TailBelow head (exponential zero empty-state history)

    below-head :
        {n : ℕ}
        (tail-exponent : Exponent)
        (tail-coefficient : Coefficient)
        (history : SequentialHistory
          {State = State} {Step = Step}
          empty-state (suc n)
          (head-state tail-exponent tail-coefficient))
      → tail-exponent ≺e head
      → TailBelow head
          (exponential
            (suc n)
            (head-state tail-exponent tail-coefficient)
            history)

  prepend :
      (head : Exponent)
      (coefficient : Coefficient)
    → Good coefficient
    → (tail : Exponential)
    → TailBelow head tail
    → Exponential
  prepend head coefficient good
      .(exponential zero empty-state history)
      (below-empty history) =
    exponential
      (suc zero)
      (head-state head coefficient)
      (sequential-next-history
        history
        (first-step head coefficient good))
  prepend head coefficient good
      .(exponential
        (suc n)
        (head-state tail-exponent tail-coefficient)
        history)
      (below-head {n = n}
        tail-exponent tail-coefficient history decrease) =
    exponential
      (suc (suc n))
      (head-state head coefficient)
      (sequential-next-history
        history
        (prepend-step
          head tail-exponent coefficient tail-coefficient
          good decrease))

  singleton :
      (exponent : Exponent)
      (coefficient : Coefficient)
    → Good coefficient
    → Exponential
  singleton exponent coefficient good =
    prepend
      exponent coefficient good
      zeroᴱ
      (below-empty (sequential-seed-history empty-state))

  ----------------------------------------------------------------------
  -- Lexicographic comparison

  module Pair =
    Lex.Dependent
      (λ (_ : Exponent) → Coefficient)
      _≺e_
      (λ _ → _≺c_)

  -- Pairs are compared lexicographically, as the constant-fiber case of
  -- `Lex.Dependent`.
  PairLess :
      Exponent → Coefficient → Exponent → Coefficient →
      Set (ℓe ⊔ ℓc ⊔ ℓre ⊔ ℓrc)
  PairLess left left-coefficient right right-coefficient =
    Pair._<_
      (left , left-coefficient)
      (right , right-coefficient)

  pattern exponent-less decrease = Pair.earlier decrease
  pattern coefficient-less exponent decrease =
    Pair.within exponent decrease

  infix 4 _≺ᴱ_

  -- Comparison of normal forms presented by `prepend`: the empty form is
  -- below every nonempty one, a smaller leading pair decides, and equal
  -- leading pairs pass to the tails.  Transitivity and well-foundedness are
  -- proved in Exponential.Order, for a variant reading the final node of the
  -- history directly.
  data _≺ᴱ_ : Exponential → Exponential →
      Set (ℓe ⊔ ℓc ⊔ ℓg ⊔ ℓre ⊔ ℓrc) where
    proper-prefix :
        (left-empty : SequentialHistory
          {State = State} {Step = Step}
          empty-state zero empty-state)
        (right-head : Exponent)
        (right-coefficient : Coefficient)
        (right-good : Good right-coefficient)
        (right-tail : Exponential)
        (right-below : TailBelow right-head right-tail)
      → exponential zero empty-state left-empty ≺ᴱ
          prepend
            right-head right-coefficient right-good
            right-tail right-below

    first-difference :
        {left-head right-head : Exponent}
        {left-coefficient right-coefficient : Coefficient}
        {left-tail right-tail : Exponential}
      → (left-good : Good left-coefficient)
      → (right-good : Good right-coefficient)
      → (left-below : TailBelow left-head left-tail)
      → (right-below : TailBelow right-head right-tail)
      → PairLess
          left-head left-coefficient
          right-head right-coefficient
      → prepend
          left-head left-coefficient left-good
          left-tail left-below
        ≺ᴱ
        prepend
          right-head right-coefficient right-good
          right-tail right-below

    common-head :
        (head : Exponent)
        (coefficient : Coefficient)
        {left-tail right-tail : Exponential}
      → (left-good : Good coefficient)
      → (right-good : Good coefficient)
      → (left-below : TailBelow head left-tail)
      → (right-below : TailBelow head right-tail)
      → left-tail ≺ᴱ right-tail
      → prepend
          head coefficient left-good
          left-tail left-below
        ≺ᴱ
        prepend
          head coefficient right-good
          right-tail right-below

  zero-below-singleton :
      (exponent : Exponent)
      (coefficient : Coefficient)
      (good : Good coefficient)
    → zeroᴱ ≺ᴱ singleton exponent coefficient good
  zero-below-singleton exponent coefficient good =
    proper-prefix
      (sequential-seed-history empty-state)
      exponent coefficient good
      zeroᴱ
      (below-empty (sequential-seed-history empty-state))

  pair-trans :
      (∀ {left middle right} →
        left ≺e middle → middle ≺e right → left ≺e right)
    → (∀ {left middle right} →
        left ≺c middle → middle ≺c right → left ≺c right)
    → ∀ {left-exponent middle-exponent right-exponent}
        {left-coefficient middle-coefficient right-coefficient}
    → PairLess
        left-exponent left-coefficient
        middle-exponent middle-coefficient
    → PairLess
        middle-exponent middle-coefficient
        right-exponent right-coefficient
    → PairLess
        left-exponent left-coefficient
        right-exponent right-coefficient
  pair-trans trans-exponent trans-coefficient =
    Pair.trans
      trans-exponent
      (λ _ → trans-coefficient)
