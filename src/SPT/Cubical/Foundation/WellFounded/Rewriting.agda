{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.WellFounded.Rewriting where

-- A rewrite system is a type of states with a type-valued step relation `x ↝⟨ R
-- ⟩ y`. A state is strongly normalizing when it is accessible for the reversed
-- steps, `y ≺⟨ R ⟩ x` meaning `x ↝⟨ R ⟩ y`: induction along every sequence of
-- steps from it is available. The system terminates when every state is
-- strongly normalizing. Equivalently, the projection from the strongly
-- normalizing states to the states has a point in each fiber, and a point of
-- the fiber over `x` gives the normalization of `x` (`normalizing-from-fiber`).
--
-- A relation `_<_` gives the rewrite system that runs it backwards: a step from
-- a parent to a child is a witness that the child lies below the parent.
--
-- A rank of a rewrite system in a well-founded relation sends states to the
-- carrier so that every step goes strictly down. A rewrite system with a rank
-- terminates: a state whose rank is accessible is strongly normalizing
-- (`accessible-rank-gives-normalizing`).

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Fibers using (fiber)
open import SPT.Cubical.Foundation.Accessibility using
  ( is-accessible; acc; Well-Founded-Relation; Carrier; below
  ; below-is-well-founded )

------------------------------------------------------------------------
-- Rewrite systems

record Rewrite-System (ℓ κ : Level) : Set (lsuc (ℓ ⊔ κ)) where
  constructor rewrite-system
  field
    states : Set ℓ
    steps : states → states → Set κ

module _ {ℓ κ : Level} (R : Rewrite-System ℓ κ) where

  State : Set ℓ
  State = Rewrite-System.states R

rewrites : {ℓ κ : Level} (R : Rewrite-System ℓ κ) →
  State R → State R → Set κ
rewrites R = Rewrite-System.steps R

infix 30 rewrites
syntax rewrites R x y = x ↝⟨ R ⟩ y

predecessor : {ℓ κ : Level} (R : Rewrite-System ℓ κ) →
  State R → State R → Set κ
predecessor R y x = x ↝⟨ R ⟩ y

infix 30 predecessor
syntax predecessor R y x = y ≺⟨ R ⟩ x

------------------------------------------------------------------------
-- The reversed relation

module _ {ℓ κ : Level} {A : Set ℓ} where

  reversed : (A → A → Set κ) → Rewrite-System ℓ κ
  reversed _<_ = rewrite-system A (λ parent child → child < parent)

------------------------------------------------------------------------
-- Strong normalization and termination

module _ {ℓ κ : Level} (R : Rewrite-System ℓ κ) where

  is-strongly-normalizing : State R → Set (ℓ ⊔ κ)
  is-strongly-normalizing = is-accessible (predecessor R)

  terminates : Set (ℓ ⊔ κ)
  terminates = (x : State R) → is-strongly-normalizing x

  Normalizing-State : Set (ℓ ⊔ κ)
  Normalizing-State = Σ (State R) (λ x → is-strongly-normalizing x)

  normalized : Normalizing-State → State R
  normalized (x , _) = x

------------------------------------------------------------------------
-- Ranks

module _ {ℓ κ ℓ′ κ′ : Level} where

  record Rank (R : Rewrite-System ℓ κ) (O : Well-Founded-Relation ℓ′ κ′) :
    Set (ℓ ⊔ κ ⊔ ℓ′ ⊔ κ′) where
    constructor rank
    field
      rank-of : State R → Carrier O
      decreases : (x y : State R) → x ↝⟨ R ⟩ y →
        rank-of y <⟨ O ⟩ rank-of x

  open Rank public

------------------------------------------------------------------------
-- Termination is a section of the normalizing states

module _ {ℓ κ : Level} (R : Rewrite-System ℓ κ) where

  termination-gives-sections : terminates R →
    (x : State R) → fiber (normalized R) x
  termination-gives-sections normalizing x = (x , normalizing x) , refl

  normalizing-from-fiber : (x : State R) → fiber (normalized R) x →
    is-strongly-normalizing R x
  normalizing-from-fiber x ((.x , normalizing) , refl) = normalizing

  sections-give-termination :
    ((x : State R) → fiber (normalized R) x) → terminates R
  sections-give-termination section x =
    normalizing-from-fiber x (section x)

------------------------------------------------------------------------
-- A rank gives termination

module _ {ℓ κ ℓ′ κ′ : Level} {R : Rewrite-System ℓ κ}
  {O : Well-Founded-Relation ℓ′ κ′} where

  accessible-rank-gives-normalizing : (r : Rank R O) (x : State R) →
    is-accessible (below O) (rank-of r x) → is-strongly-normalizing R x
  accessible-rank-gives-normalizing r x (acc smaller) =
    acc (λ y step →
      accessible-rank-gives-normalizing r y
        (smaller (rank-of r y) (decreases r x y step)))

  terminates-by-rank : Rank R O → terminates R
  terminates-by-rank r x =
    accessible-rank-gives-normalizing r x
      (below-is-well-founded O (rank-of r x))
