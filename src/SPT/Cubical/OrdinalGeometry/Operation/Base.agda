{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Operation.Base where

-- Operations on presented ordinals that act on initial maps, that is on
-- inclusions of predecessor domains. Iterating an operation from a seed
-- gives a tower of initial maps. Its completion includes into every
-- prefixed point into which the seed includes, and is a fixed point when
-- the operation commutes with chain completions. From the empty ordinal
-- the seed is free. Completions of ℕ × ℕ grids of initial maps may be
-- taken in either order.

open import Agda.Primitive using (Level; lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_)
import Data.Nat.Properties as Nat
open import Data.Product using (_,_)
open import Level using (lower)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Limit as Limit
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization.Presentation
  as Exact
import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- Operations and continuity

-- An object map with an action on initial maps. The functor laws hold
-- pointwise up to ≈, since initial maps are unique (Maps.Uniqueness).
record Operation (ℓ : Level) : Set (lsuc ℓ) where
  field
    apply : 𝒫 ℓ → 𝒫 ℓ
    act : {P Q : 𝒫 ℓ} → Maps.Initial P Q → Maps.Initial (apply P) (apply Q)

chain : Operation ℓ → Limit.Chain ℓ → Limit.Chain ℓ
chain F C = record
  { stage = λ n → Operation.apply F (Limit.Chain.stage C n)
  ; edge = λ n → Operation.act F (Limit.Chain.edge C n)
  }

-- Mathematical shape: sup F(Cₙ) ≃ F(sup Cₙ) for every chain C.
Continuous : Operation ℓ → Set (lsuc ℓ)
Continuous {ℓ} F = (C : Limit.Chain ℓ)
  → Limit.completion (chain F C)
    Presented.≃𝒫 Operation.apply F (Limit.completion C)

respect : (F : Operation ℓ) {P Q : 𝒫 ℓ} → P Presented.≃𝒫 Q
  → Operation.apply F P Presented.≃𝒫 Operation.apply F Q
respect F e = Maps.antisymmetry
  (Operation.act F (Maps.equivalence e))
  (Operation.act F (Maps.equivalence (Presented.≃𝒫-sym e)))

------------------------------------------------------------------------
-- Towers above a seed

level : Operation ℓ → 𝒫 ℓ → ℕ → 𝒫 ℓ
level F P zero = P
level F P (suc n) = Operation.apply F (level F P n)

edge : (F : Operation ℓ) (P : 𝒫 ℓ) → Maps.Initial P (Operation.apply F P)
  → (n : ℕ) → Maps.Initial (level F P n) (level F P (suc n))
edge F P e zero = e
edge F P e (suc n) = Operation.act F (edge F P e n)

tower : (F : Operation ℓ) (P : 𝒫 ℓ)
  → Maps.Initial P (Operation.apply F P) → Limit.Chain ℓ
tower F P e = record { stage = level F P ; edge = edge F P e }

-- Limit.coverage captures every predecessor of the boundary at one finite
-- level of the tower; the boundary has no top point.
boundary : (F : Operation ℓ) (P : 𝒫 ℓ)
  → Maps.Initial P (Operation.apply F P) → 𝒫 ℓ
boundary F P e = Limit.completion (tower F P e)

above : (F : Operation ℓ) (P : 𝒫 ℓ) (e : Maps.Initial P (Operation.apply F P))
  → Maps.Initial P (boundary F P e)
above F P e = Limit.stage (tower F P e) zero

-- Mathematical shape: P ⊆ Q and F(Q) ⊆ Q give boundary(P) ⊆ Q.
least : (F : Operation ℓ) (P : 𝒫 ℓ) (e : Maps.Initial P (Operation.apply F P))
  → (Q : 𝒫 ℓ) → Maps.Initial (Operation.apply F Q) Q → Maps.Initial P Q
  → Maps.Initial (boundary F P e) Q
least F P e Q prefixed f = Limit.least (tower F P e) Q into
  where
  into : (n : ℕ) → Maps.Initial (level F P n) Q
  into zero = f
  into (suc n) = Maps.compose (Operation.act F (into n)) prefixed

-- F of the tower is the tower shifted by one level, a cofinal subchain.
fixed : (F : Operation ℓ) → Continuous F
  → (P : 𝒫 ℓ) (e : Maps.Initial P (Operation.apply F P))
  → Operation.apply F (boundary F P e) Presented.≃𝒫 boundary F P e
fixed F continuous P e =
  Presented.≃𝒫-trans (Presented.≃𝒫-sym (continuous (tower F P e)))
    (Presented.≃𝒫-trans
      (Limit.equivalence (chain F (tower F P e)) shifted
        (λ n → Presented.≃𝒫-refl (level F P (suc n))))
      (Limit.cofinal (tower F P e) suc ascending (λ n → n , Nat.n≤1+n n)))
  where
  ascending : (n : ℕ) → suc n ≤ suc (suc n)
  ascending n = Nat.n≤1+n (suc n)

  shifted : Limit.Chain _
  shifted = Limit.subsequence (tower F P e) suc ascending

------------------------------------------------------------------------
-- From the empty ordinal

private
  emptyOrder : Order.Order ⊥
  emptyOrder = record
    { _<_ = λ ()
    ; trans = λ {x} → ⊥-elim x
    ; wf = λ ()
    ; compare = λ ()
    ; enum = λ _ → nothing
    ; covers = λ ()
    }

empty : 𝒫 ℓ
empty = Exact.presentation emptyOrder

from-empty : (Q : 𝒫 ℓ) → Maps.Initial empty Q
from-empty Q = record
  { map = λ x → ⊥-elim (lower x)
  ; resp = λ {x} → ⊥-elim (lower x)
  ; strict = λ {x} → ⊥-elim (lower x)
  ; lower = λ x → ⊥-elim (lower x)
  }

-- The tower of F from the empty ordinal needs no seed.
bottom : Operation ℓ → 𝒫 ℓ
bottom F = boundary F empty (from-empty (Operation.apply F empty))

bottomTower : Operation ℓ → Limit.Chain ℓ
bottomTower F = tower F empty (from-empty (Operation.apply F empty))

bottom-least : (F : Operation ℓ) (Q : 𝒫 ℓ)
  → Maps.Initial (Operation.apply F Q) Q → Maps.Initial (bottom F) Q
bottom-least F Q prefixed =
  least F empty (from-empty (Operation.apply F empty)) Q prefixed
    (from-empty Q)

bottom-fixed : (F : Operation ℓ) → Continuous F
  → Operation.apply F (bottom F) Presented.≃𝒫 bottom F
bottom-fixed F continuous =
  fixed F continuous empty (from-empty (Operation.apply F empty))

-- An initial map from each F-value to the matching G-value.
Transformation : Operation ℓ → Operation ℓ → Set (lsuc ℓ)
Transformation {ℓ} F G = {P Q : 𝒫 ℓ} → Maps.Initial P Q
  → Maps.Initial (Operation.apply F P) (Operation.apply G Q)

levelMap : (F G : Operation ℓ) → Transformation F G
  → (n : ℕ) → Maps.Initial (level F empty n) (level G empty n)
levelMap F G α zero = Maps.identity empty
levelMap F G α (suc n) = α (levelMap F G α n)

induced : (F G : Operation ℓ) → Transformation F G
  → Maps.Initial (bottom F) (bottom G)
induced F G α = Limit.least (bottomTower F) (bottom G) λ n →
  Maps.compose (levelMap F G α n) (Limit.stage (bottomTower G) n)

------------------------------------------------------------------------
-- Grids of initial maps

-- Rows are indexed by j, and each row is a chain in k.
record Grid (ℓ : Level) : Set (lsuc ℓ) where
  field
    point : ℕ → ℕ → 𝒫 ℓ
    right : (j k : ℕ) → Maps.Initial (point j k) (point j (suc k))
    down : (j k : ℕ) → Maps.Initial (point j k) (point (suc j) k)

row : Grid ℓ → ℕ → Limit.Chain ℓ
row G j = record
  { stage = Grid.point G j
  ; edge = Grid.right G j
  }

column : Grid ℓ → ℕ → Limit.Chain ℓ
column G k = record
  { stage = λ j → Grid.point G j k
  ; edge = λ j → Grid.down G j k
  }

rows : Grid ℓ → Limit.Chain ℓ
rows G = record
  { stage = λ j → Limit.completion (row G j)
  ; edge = λ j → Limit.least (row G j) (Limit.completion (row G (suc j)))
      λ k → Maps.compose (Grid.down G j k) (Limit.stage (row G (suc j)) k)
  }

columns : Grid ℓ → Limit.Chain ℓ
columns G = record
  { stage = λ k → Limit.completion (column G k)
  ; edge = λ k → Limit.least (column G k)
      (Limit.completion (column G (suc k)))
      λ j → Maps.compose (Grid.right G j k)
        (Limit.stage (column G (suc k)) j)
  }

-- Both iterated completions include into each other through their stage
-- maps; initial maps in both directions give an equivalence.
interchange : (G : Grid ℓ)
  → Limit.completion (rows G) Presented.≃𝒫 Limit.completion (columns G)
interchange G = Maps.antisymmetry
  (Limit.least (rows G) (Limit.completion (columns G)) λ j →
    Limit.least (row G j) (Limit.completion (columns G)) λ k →
      Maps.compose (Limit.stage (column G k) j)
        (Limit.stage (columns G) k))
  (Limit.least (columns G) (Limit.completion (rows G)) λ k →
    Limit.least (column G k) (Limit.completion (rows G)) λ j →
      Maps.compose (Limit.stage (row G j) k) (Limit.stage (rows G) j))
