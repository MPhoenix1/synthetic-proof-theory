{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Linear.History where

-- A sequential history of a step relation is a closed tree in its sequential
-- signature: one seed node followed by one node for each step,
--
--   SequentialHistory initial n x
--     = History (sequentialSignature Step initial) (n , x).
--
-- The children of the two kinds of node are named once: the seed has none
-- (`no-children`), and a step node has the history before it as its only child
-- (`only-child`). Every construction that rebuilds a node uses these names, so
-- two constructions of the same node are the same term.

open import SPT.Base
open import SPT.Foundation.Tree using (History; Pos; boundary; node)
open import SPT.Foundation.Linear.Signature using
  ( sequential-seed; sequential-next; unary-position
  ; sequentialSignature )

module _ {ℓs ℓe : Level} {State : ℕ → Set ℓs}
  (Step : (n : ℕ) → State n → State (suc n) → Set ℓe) where

  SequentialHistory : State zero → (n : ℕ) → State n → Set (ℓs ⊔ ℓe)
  SequentialHistory initial n x =
    History (sequentialSignature Step initial) (n , x)

  no-children : (initial : State zero)
    (p : Pos (sequentialSignature Step initial) sequential-seed) →
    History (sequentialSignature Step initial)
      (boundary (sequentialSignature Step initial) sequential-seed p)
  no-children initial ()

  only-child : {initial : State zero} {n : ℕ} {x : State n}
    {y : State (suc n)} (edge : Step n x y) →
    SequentialHistory initial n x →
    (p : Pos (sequentialSignature Step initial) (sequential-next edge)) →
    History (sequentialSignature Step initial)
      (boundary (sequentialSignature Step initial) (sequential-next edge) p)
  only-child edge history unary-position = history

  sequential-seed-history : (initial : State zero) →
    SequentialHistory initial zero initial
  sequential-seed-history initial =
    node sequential-seed (no-children initial)

  sequential-next-history : {initial : State zero} {n : ℕ} {x : State n}
    {y : State (suc n)} → SequentialHistory initial n x → Step n x y →
    SequentialHistory initial (suc n) y
  sequential-next-history history edge =
    node (sequential-next edge) (only-child edge history)
