{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.WellFounded where

-- Well-foundedness of the support order of ω^P: supports embed, preserving
-- and reflecting order, into exponential normal forms over Linear
-- histories (Core.Generator.Linear.Exponential), whose order is well
-- founded.

open import Data.List using ([]; _∷_; length)
open import Data.Nat using (ℕ)
import Data.Nat.Base as Nat
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst₂)

open import SPT.Cubical.Core.WellFounded using (WellFounded)
open import SPT.Cubical.Core.WellFounded.Pullback using (pullback-wf)
open import SPT.Cubical.Core.WellFounded.Subrelation using (subrel-wf)
open import SPT.Cubical.Core.Generator.Linear.History using
  (SequentialHistory; sequential-seed-history; sequential-next-history)
open import SPT.Cubical.Core.Generator.Linear.Signature using
  (sequential-seed; sequential-next; unary-position)
open import SPT.Cubical.Core.Generator.Tree using (hole; node)
import SPT.Cubical.Core.Generator.Linear.Exponential.Order as Linear
import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order
import SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.Support as Support

-- Each valid support gives a Linear history.  The map preserves and
-- reflects the order, so well-foundedness pulls back along it.
module Power {A : Set} (P : Order.Order A) where

  module Supports = Support.Power P
  module Layer = Linear.Layer A ℕ (λ _ → ⊤) (Order.Order._<_ P) Nat._<_
  module Terms = Layer.Terms

  private
    state : (xs : Supports.Raw) → Terms.State (length xs)
    state [] = Terms.empty-state
    state ((a , n) ∷ xs) = Terms.head-state a n

    run : (xs : Supports.Raw) → Supports.Valid xs → SequentialHistory
      {State = Terms.State} {Step = Terms.Step}
      Terms.empty-state (length xs) (state xs)
    run [] tt = sequential-seed-history Terms.empty-state
    run ((a , n) ∷ []) tt = sequential-next-history
      (sequential-seed-history Terms.empty-state) (Terms.first-step a n tt)
    run ((a , n) ∷ ys@((b , m) ∷ xs)) (p , q) = sequential-next-history
      (run ys q) (Terms.prepend-step a b n m tt (Supports.sound p))

  history : Supports.Term → Terms.Exponential
  history (xs , q) = Terms.exponential (length xs) (state xs) (run xs q)

  snoc : (a : A) (n : ℕ) (xs : Supports.Raw) (q : Supports.Valid ((a , n) ∷ xs))
    → Layer.Snoc a n (history (xs , Supports.tail-valid q))
        (history ((a , n) ∷ xs , q))
  snoc a n [] tt = Layer.first-node a n tt
  snoc a n ((b , m) ∷ xs) (p , q) =
    Layer.later-node a b n m tt (Supports.sound p)

  preserve : ∀ {x y} → x Supports.< y → history x Layer.≺ᴱ history y
  preserve {[] , tt} {((a , n) ∷ xs) , q} Supports.empty =
    Layer.proper-prefix (Layer.empty-node _) (snoc a n xs q)
  preserve {((a , n) ∷ xs) , p} {((b , m) ∷ ys) , q} (Supports.head r) =
    Layer.first-difference (snoc a n xs p) (snoc b m ys q) r
  preserve {((a , n) ∷ xs) , p} {((.a , .n) ∷ ys) , q} (Supports.tail r) =
    Layer.common-head (snoc a n xs p) (snoc a n ys q)
      (preserve {xs , Supports.tail-valid p} {ys , Supports.tail-valid q} r)

  private
    trace-run : ∀ {n s} → SequentialHistory
      {State = Terms.State} {Step = Terms.Step} Terms.empty-state n s
      → Supports.Raw
    trace-run (hole ())
    trace-run (node sequential-seed children) = []
    trace-run (node (sequential-next (Terms.first-step a n good)) children) =
      (a , n) ∷ trace-run (children unary-position)
    trace-run (node (sequential-next
        (Terms.prepend-step a b n m good decrease)) children) =
      (a , n) ∷ trace-run (children unary-position)

  trace : Terms.Exponential → Supports.Raw
  trace h = trace-run (Terms.support h)

  trace-snoc : ∀ {a n tail whole} → Layer.Snoc a n tail whole
    → trace whole ≡ (a , n) ∷ trace tail
  trace-snoc (Layer.first-node a n good) = refl
  trace-snoc (Layer.later-node a b n m good decrease) = refl

  trace-history : (x : Supports.Term) → trace (history x) ≡ Supports.raw x
  trace-history ([] , tt) = refl
  trace-history (((a , n) ∷ []) , tt) = refl
  trace-history (((a , n) ∷ ys@(_ ∷ _)) , (p , q)) =
    cong ((a , n) ∷_) (trace-history (ys , q))

  trace-preserve : ∀ {x y} → x Layer.≺ᴱ y → trace x Supports.≺ trace y
  trace-preserve (Layer.proper-prefix (Layer.empty-node children) r)
    rewrite trace-snoc r = Supports.empty
  trace-preserve (Layer.first-difference l r p)
    rewrite trace-snoc l | trace-snoc r = Supports.head p
  trace-preserve (Layer.common-head l r p)
    rewrite trace-snoc l | trace-snoc r = Supports.tail (trace-preserve p)

  reflect : ∀ {x y} → history x Layer.≺ᴱ history y → x Supports.< y
  reflect {x} {y} p = subst₂ Supports._≺_ (trace-history x) (trace-history y)
    (trace-preserve p)

  abstract
    well-founded : WellFounded Supports._<_
    well-founded = subrel-wf preserve
      (pullback-wf {rank = history} {_<_ = Layer._≺ᴱ_}
        (Layer.well-founded (Order.Order.wf P)
          (λ n _ → Order.Order.wf Order.natural n)))
