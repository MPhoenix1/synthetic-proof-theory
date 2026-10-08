{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.Generator.Linear.History where

-- Histories in the sequential signature of a step relation: one seed
-- node followed by one node for every step.

open import Agda.Primitive using (_⊔_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)

open import SPT.Cubical.Core.Generator.Linear.Signature
  using
    ( sequential-seed
    ; sequential-next
    ; unary-position
    ; sequentialSignature
    )
open import SPT.Cubical.Core.Generator.Tree
  using (History; node)

--   SequentialHistory(initial,n,x)
--     = History(sequentialSignature(Step,initial),(n,x)).

SequentialHistory :
    ∀ {ℓs ℓe}
      {State : ℕ → Set ℓs}
      {Step :
        (n : ℕ) → State n → State (suc n) → Set ℓe}
  → State zero
  → (n : ℕ)
  → State n
  → Set (ℓs ⊔ ℓe)
SequentialHistory {Step = Step} initial n x =
  History (sequentialSignature Step initial) (n , x)

sequential-seed-history :
    ∀ {ℓs ℓe}
      {State : ℕ → Set ℓs}
      {Step :
        (n : ℕ) → State n → State (suc n) → Set ℓe}
  → (initial : State zero)
  → SequentialHistory
      {Step = Step}
      initial zero initial
sequential-seed-history initial =
  node
    sequential-seed
    (λ ())

sequential-next-history :
    ∀ {ℓs ℓe}
      {State : ℕ → Set ℓs}
      {Step :
        (n : ℕ) → State n → State (suc n) → Set ℓe}
      {initial : State zero}
      {n : ℕ}
      {x : State n}
      {y : State (suc n)}
  → SequentialHistory
      {Step = Step}
      initial n x
  → Step n x y
  → SequentialHistory
      {Step = Step}
      initial (suc n) y
sequential-next-history history edge =
  node
    (sequential-next edge)
    (λ { unary-position → history })
