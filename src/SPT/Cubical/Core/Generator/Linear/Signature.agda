{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.Generator.Linear.Signature where

-- Linear signatures, whose operations have at most one child; recognition
-- of an arbitrary signature as linear; and the sequential signature of a
-- step relation along ℕ.

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import SPT.Cubical.Core.Generator.Signature
  using (Signature; Judgment; Op; Pos)

------------------------------------------------------------------------
-- Arities zero and one

-- LinearArity = 0 + 1, with LinearPosition(0) = 0 and LinearPosition(1) = 1.
-- The arity decides by computation whether an operation has a child.

data LinearArity : Set where
  nullary unary : LinearArity

data LinearPosition : LinearArity → Set where
  unary-position : LinearPosition unary

------------------------------------------------------------------------
-- Linear signatures

--   L = (J, Op, arity, ∂),   arity(o) : 0 + 1,
--   ∂(o,-) : LinearPosition(arity(o)) → J.
--
-- `toSignature` computes the positions of the underlying signature from
-- the arity.

record LinearSignature
    (ℓj ℓo : Level)
    : Set (lsuc (ℓj ⊔ ℓo))
  where
  field
    LinearJudgment :
      Set ℓj

    LinearOp :
      LinearJudgment
      → Set ℓo

    operation-arity :
        {j : LinearJudgment}
      → LinearOp j
      → LinearArity

    linear-boundary :
        {j : LinearJudgment}
      → (o : LinearOp j)
      → LinearPosition (operation-arity o)
      → LinearJudgment

open LinearSignature public

toSignature :
    ∀ {ℓj ℓo}
  → LinearSignature ℓj ℓo
  → Signature ℓj ℓo lzero
toSignature L =
  record
    { Judgment = LinearJudgment L
    ; Op = LinearOp L
    ; Pos = λ o → LinearPosition (operation-arity L o)
    ; boundary = linear-boundary L
    }

------------------------------------------------------------------------
-- Recognizing a signature as linear

-- Maps both ways between two position types with pointwise inverse laws.

record PositionEquivalence
    {ℓa ℓb : Level}
    (A : Set ℓa)
    (B : Set ℓb)
    : Set (ℓa ⊔ ℓb)
  where
  field
    position-to :
      A → B

    position-from :
      B → A

    position-from-to :
        (a : A)
      → position-from (position-to a) ≡ a

    position-to-from :
        (b : B)
      → position-to (position-from b) ≡ b

open PositionEquivalence public

-- A recognition of a signature as linear: an arity for every operation and
-- an equivalence of its positions with LinearPosition of that arity,
--
--   IsLinear(Σ) = (arity : Π(j,o). 0 + 1)
--               × Π(j,o). Pos(o) ≃ LinearPosition(arity(o)).
--
-- This is structure, not a proposition.

record IsLinear
    {ℓj ℓo ℓp : Level}
    (Σ : Signature ℓj ℓo ℓp)
    : Set (ℓj ⊔ ℓo ⊔ ℓp)
  where
  field
    recognized-arity :
        {j : Judgment Σ}
      → (o : Op Σ j)
      → LinearArity

    position-equivalence :
        {j : Judgment Σ}
      → (o : Op Σ j)
      → PositionEquivalence
          (Pos Σ o)
          (LinearPosition (recognized-arity o))

open IsLinear public

canonical-is-linear :
    ∀ {ℓj ℓo}
  → (L : LinearSignature ℓj ℓo)
  → IsLinear (toSignature L)
canonical-is-linear L =
  record
    { recognized-arity =
        operation-arity L
    ; position-equivalence =
        λ o →
          record
            { position-to = λ p → p
            ; position-from = λ p → p
            ; position-from-to = λ p → refl
            ; position-to-from = λ p → refl
            }
    }

------------------------------------------------------------------------
-- Sequential signatures

SequentialJudgment :
    ∀ {ℓs}
  → (State : ℕ → Set ℓs)
  → Set ℓs
SequentialJudgment State =
  Σ ℕ State

-- The operations of a step relation along ℕ: a seed at (0, initial), and
-- for every step e : Step(n,x,y) an operation at (n+1, y) whose one child
-- is (n, x).

data SequentialOperation
    {ℓs ℓe : Level}
    {State : ℕ → Set ℓs}
    (Step :
      (n : ℕ) → State n → State (suc n) → Set ℓe)
    (initial : State zero)
    : SequentialJudgment State
    → Set (ℓs ⊔ ℓe)
  where
  sequential-seed :
    SequentialOperation Step initial (zero , initial)

  sequential-next :
      ∀ {n x y}
    → Step n x y
    → SequentialOperation Step initial (suc n , y)

sequential-arity :
    ∀ {ℓs ℓe}
      {State : ℕ → Set ℓs}
      {Step :
        (n : ℕ) → State n → State (suc n) → Set ℓe}
      {initial : State zero}
      {judgment : SequentialJudgment State}
  → SequentialOperation Step initial judgment
  → LinearArity
sequential-arity sequential-seed =
  nullary
sequential-arity (sequential-next edge) =
  unary

sequential-boundary :
    ∀ {ℓs ℓe}
      {State : ℕ → Set ℓs}
      {Step :
        (n : ℕ) → State n → State (suc n) → Set ℓe}
      {initial : State zero}
      {judgment : SequentialJudgment State}
  → (operation : SequentialOperation Step initial judgment)
  → LinearPosition (sequential-arity operation)
  → SequentialJudgment State
sequential-boundary
    (sequential-next {n = n} {x = x} edge)
    unary-position =
  n , x

-- The sequential signature: judgments Σ(n : ℕ). State(n), the seed of
-- arity 0, and one operation of arity 1 for every step.

sequentialLinearSignature :
    ∀ {ℓs ℓe}
      {State : ℕ → Set ℓs}
  → (Step :
      (n : ℕ) → State n → State (suc n) → Set ℓe)
  → State zero
  → LinearSignature ℓs (ℓs ⊔ ℓe)
sequentialLinearSignature Step initial =
  record
    { LinearJudgment = SequentialJudgment _
    ; LinearOp = SequentialOperation Step initial
    ; operation-arity = sequential-arity
    ; linear-boundary = sequential-boundary
    }

sequentialSignature :
    ∀ {ℓs ℓe}
      {State : ℕ → Set ℓs}
  → (Step :
      (n : ℕ) → State n → State (suc n) → Set ℓe)
  → State zero
  → Signature ℓs (ℓs ⊔ ℓe) lzero
sequentialSignature Step initial =
  toSignature (sequentialLinearSignature Step initial)

sequential-is-linear :
    ∀ {ℓs ℓe}
      {State : ℕ → Set ℓs}
  → (Step :
      (n : ℕ) → State n → State (suc n) → Set ℓe)
  → (initial : State zero)
  → IsLinear (sequentialSignature Step initial)
sequential-is-linear Step initial =
  canonical-is-linear
    (sequentialLinearSignature Step initial)
