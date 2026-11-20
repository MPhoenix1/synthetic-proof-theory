{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.WellFounded where

-- Well-foundedness of the support order of ω^P: supports embed, preserving
-- and reflecting order, into exponential normal forms over Linear
-- histories (Foundation.Linear.Exponential), whose order is well founded
-- (Foundation.Linear.Exponential.Order).

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Accessibility using (is-well-founded)
open import SPT.Cubical.Foundation.Linear.History using
  ( SequentialHistory; only-child; sequential-next-history
  ; sequential-seed-history )
open import SPT.Cubical.Foundation.Linear.Signature using
  ( sequential-next; sequential-seed; unary-position )
open import SPT.Cubical.Foundation.Tree using (hole; node)
open import SPT.Cubical.Foundation.WellFounded.Pullback using
  ( pullback-is-well-founded )
open import SPT.Cubical.Foundation.WellFounded.Subrelation using
  ( subrelations-are-well-founded )

import SPT.Cubical.Foundation.Linear.Exponential as Terms
import SPT.Cubical.Foundation.Linear.Exponential.Order as Linear
import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order
import SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.Support as Support

-- Each valid support gives a Linear history.  The map preserves and
-- reflects the order, so well-foundedness pulls back along it.
module Power {A : Set} (P : Order.Order A) where

  module Supports = Support.Power P

  -- The layer of ω^P: exponents in P, coefficients in ℕ, every coefficient
  -- admissible.
  L : Terms.Layer lzero lzero lzero lzero lzero
  L = Terms.layer A ℕ (λ _ → 𝟙) (Order.Order._<_ P) _<ℕˢ_

  private
    state : (xs : Supports.Raw) → Terms.State L (length xs)
    state [] = Terms.empty-state
    state ((a , n) ∷ xs) = Terms.head-state a n

    run : (xs : Supports.Raw) → Supports.Valid xs →
      SequentialHistory (Terms.Step L) Terms.empty-state (length xs)
        (state xs)
    run [] ⋆ = sequential-seed-history (Terms.Step L) Terms.empty-state
    run ((a , n) ∷ []) ⋆ = sequential-next-history (Terms.Step L)
      (sequential-seed-history (Terms.Step L) Terms.empty-state)
      (Terms.first-step a n ⋆)
    run ((a , n) ∷ ys@((b , m) ∷ xs)) (p , q) =
      sequential-next-history (Terms.Step L) (run ys q)
        (Terms.prepend-step a b n m ⋆ (Supports.sound p))

  history : Supports.Term → Terms.Exponential L
  history (xs , q) = Terms.exponential (length xs) (state xs) (run xs q)

  snoc : (a : A) (n : ℕ) (xs : Supports.Raw)
    (q : Supports.Valid ((a , n) ∷ xs))
    → Linear.Snoc L a n (history (xs , Supports.tail-valid q))
        (history ((a , n) ∷ xs , q))
  snoc a n [] ⋆ =
    Linear.first-node a n ⋆
      (only-child (Terms.Step L) (Terms.first-step a n ⋆)
        (sequential-seed-history (Terms.Step L) Terms.empty-state))
  snoc a n ((b , m) ∷ xs) (p , q) =
    Linear.later-node a b n m ⋆ (Supports.sound p)
      (only-child (Terms.Step L)
        (Terms.prepend-step a b n m ⋆ (Supports.sound p))
        (run ((b , m) ∷ xs) q))

  preserve : ∀ {x y} → x Supports.< y → history x Linear.≺ᴱ history y
  preserve {[] , ⋆} {((a , n) ∷ xs) , q} Supports.empty =
    Linear.proper-prefix
      (Linear.empty-view L
        (sequential-seed-history (Terms.Step L) Terms.empty-state))
      (snoc a n xs q)
  preserve {((a , n) ∷ xs) , p} {((b , m) ∷ ys) , q} (Supports.head r) =
    Linear.first-difference (snoc a n xs p) (snoc b m ys q) r
  preserve {((a , n) ∷ xs) , p} {((.a , .n) ∷ ys) , q} (Supports.tail r) =
    Linear.common-head (snoc a n xs p) (snoc a n ys q)
      (preserve {xs , Supports.tail-valid p} {ys , Supports.tail-valid q} r)

  private
    trace-run : ∀ {n s} →
      SequentialHistory (Terms.Step L) Terms.empty-state n s →
      Supports.Raw
    trace-run (hole ())
    trace-run (node sequential-seed children) = []
    trace-run (node (sequential-next (Terms.first-step a n good)) children) =
      (a , n) ∷ trace-run (children unary-position)
    trace-run (node (sequential-next
        (Terms.prepend-step a b n m good decrease)) children) =
      (a , n) ∷ trace-run (children unary-position)

  trace : Terms.Exponential L → Supports.Raw
  trace h = trace-run (Terms.support h)

  trace-snoc : ∀ {a n tail whole} → Linear.Snoc L a n tail whole
    → trace whole ＝ (a , n) ∷ trace tail
  trace-snoc (Linear.first-node a n good children) = refl
  trace-snoc (Linear.later-node a b n m good decrease children) = refl

  trace-history : (x : Supports.Term) → trace (history x) ＝ Supports.raw x
  trace-history ([] , ⋆) = refl
  trace-history (((a , n) ∷ []) , ⋆) = refl
  trace-history (((a , n) ∷ ys@(_ ∷ _)) , (p , q)) =
    ap ((a , n) ∷_) (trace-history (ys , q))

  trace-preserve : ∀ {x y} → x Linear.≺ᴱ y → trace x Supports.≺ trace y
  trace-preserve (Linear.proper-prefix (Linear.empty-node children) r)
    rewrite trace-snoc r = Supports.empty
  trace-preserve (Linear.first-difference l r p)
    rewrite trace-snoc l | trace-snoc r = Supports.head p
  trace-preserve (Linear.common-head l r p)
    rewrite trace-snoc l | trace-snoc r = Supports.tail (trace-preserve p)

  reflect : ∀ {x y} → history x Linear.≺ᴱ history y → x Supports.< y
  reflect {x} {y} p =
    transport₂ Supports._≺_ (trace-history x) (trace-history y)
      (trace-preserve p)

  abstract
    well-founded : is-well-founded Supports._<_
    well-founded = subrelations-are-well-founded preserve
      (pullback-is-well-founded history Linear._≺ᴱ_
        (Linear.well-founded (Order.Order.wf P)
          (λ n _ → Order.Order.wf Order.natural n)))
