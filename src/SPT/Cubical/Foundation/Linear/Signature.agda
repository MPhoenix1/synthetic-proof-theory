{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Linear.Signature where

-- A linear signature is one whose operations have at most one child: each
-- operation has an arity, nullary or unary, which decides by computation
-- whether it has a child, and `toSignature` computes the positions of the
-- underlying signature from the arity. An arbitrary signature is recognized as
-- linear by an arity for each operation and an isomorphism of its positions
-- with those of that arity. This is structure, not a proposition.
--
-- The sequential signature of a step relation along ℕ has judgments `(n , x)`
-- with `x : State n`: a seed of arity zero at `(0 , initial)`, and for each
-- step `e : Step n x y` an operation of arity one at `(n + 1 , y)` whose one
-- child is `(n , x)`. The seed is the only operation at stage zero, so no
-- operation there has a position (`zero-operation-has-no-position`).

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Isomorphisms using (_≅_; ≅-refl)
open import SPT.Cubical.Foundation.Signature
  using (Signature; Judgment; Op; Pos)

------------------------------------------------------------------------
-- Arities zero and one

data LinearArity : Set where
  nullary unary : LinearArity

data LinearPosition : LinearArity → Set where
  unary-position : LinearPosition unary

------------------------------------------------------------------------
-- Linear signatures

record LinearSignature (ℓj ℓo : Level) : Set (lsuc (ℓj ⊔ ℓo)) where
  field
    LinearJudgment : Set ℓj
    LinearOp : LinearJudgment → Set ℓo
    operation-arity : {j : LinearJudgment} → LinearOp j → LinearArity
    linear-boundary : {j : LinearJudgment} (o : LinearOp j) →
      LinearPosition (operation-arity o) → LinearJudgment

open LinearSignature public

toSignature : {ℓj ℓo : Level} → LinearSignature ℓj ℓo →
  Signature ℓj ℓo lzero
toSignature L = record
  { Judgment = LinearJudgment L
  ; Op = LinearOp L
  ; Pos = λ o → LinearPosition (operation-arity L o)
  ; boundary = linear-boundary L
  }

------------------------------------------------------------------------
-- Recognizing a signature as linear

record IsLinear {ℓj ℓo ℓp : Level} (S : Signature ℓj ℓo ℓp) :
  Set (ℓj ⊔ ℓo ⊔ ℓp) where
  field
    recognized-arity : {j : Judgment S} (o : Op S j) → LinearArity
    position-equivalence : {j : Judgment S} (o : Op S j) →
      Pos S o ≅ LinearPosition (recognized-arity o)

open IsLinear public

canonical-is-linear : {ℓj ℓo : Level} (L : LinearSignature ℓj ℓo) →
  IsLinear (toSignature L)
canonical-is-linear L = record
  { recognized-arity = operation-arity L
  ; position-equivalence = λ o → ≅-refl
  }

------------------------------------------------------------------------
-- Sequential signatures

module _ {ℓs : Level} (State : ℕ → Set ℓs) where

  SequentialJudgment : Set ℓs
  SequentialJudgment = Σ ℕ State

module _ {ℓs ℓe : Level} {State : ℕ → Set ℓs}
  (Step : (n : ℕ) → State n → State (suc n) → Set ℓe)
  (initial : State zero) where

  data SequentialOperation : SequentialJudgment State → Set (ℓs ⊔ ℓe)
    where
    sequential-seed : SequentialOperation (zero , initial)
    sequential-next : {n : ℕ} {x : State n} {y : State (suc n)} →
      Step n x y → SequentialOperation (suc n , y)

module _ {ℓs ℓe : Level} {State : ℕ → Set ℓs}
  {Step : (n : ℕ) → State n → State (suc n) → Set ℓe}
  {initial : State zero} where

  sequential-arity : {judgment : SequentialJudgment State} →
    SequentialOperation Step initial judgment → LinearArity
  sequential-arity sequential-seed = nullary
  sequential-arity (sequential-next edge) = unary

  sequential-boundary : {judgment : SequentialJudgment State}
    (operation : SequentialOperation Step initial judgment) →
    LinearPosition (sequential-arity operation) → SequentialJudgment State
  sequential-boundary (sequential-next {n} {x} edge) unary-position = n , x

module _ {ℓs ℓe : Level} {State : ℕ → Set ℓs}
  (Step : (n : ℕ) → State n → State (suc n) → Set ℓe)
  (initial : State zero) where

  sequentialLinearSignature : LinearSignature ℓs (ℓs ⊔ ℓe)
  sequentialLinearSignature = record
    { LinearJudgment = SequentialJudgment State
    ; LinearOp = SequentialOperation Step initial
    ; operation-arity = sequential-arity
    ; linear-boundary = sequential-boundary
    }

  sequentialSignature : Signature ℓs (ℓs ⊔ ℓe) lzero
  sequentialSignature = toSignature sequentialLinearSignature

  sequential-is-linear : IsLinear sequentialSignature
  sequential-is-linear = canonical-is-linear sequentialLinearSignature

module _ {ℓs ℓe : Level} {State : ℕ → Set ℓs}
  {Step : (n : ℕ) → State n → State (suc n) → Set ℓe}
  {initial : State zero} where

  zero-operation-has-no-position : {x : State zero}
    (operation : SequentialOperation Step initial (zero , x)) →
    ¬ Pos (sequentialSignature Step initial) operation
  zero-operation-has-no-position sequential-seed ()
