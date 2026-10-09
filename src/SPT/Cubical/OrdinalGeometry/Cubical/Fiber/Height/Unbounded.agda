{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Height.Unbounded where

-- Unbounded higher structure in the fibers of rank.  Translations of
-- HigherType = Πₙ K(ℤ,n) are automorphisms of that type, so HigherType is
-- a pointed retract of the loops of the merely inhabited types at
-- HigherType itself, and each cell of HigherType gives a nontrivial cell
-- there, at every level.  The cells survive every pointed split embedding
-- of the merely inhabited types.  So the fiber of rank over α + 1 has no
-- finite h-level, and neither has rank as a map.

open import Agda.Primitive using (Level)
open import Data.Empty using (⊥)
open import Level using (Lift; lift; lower)
import Data.Nat.Base as Nat

import Cubical.Algebra.AbGroup.Instances.Int as IntegerAbGroup
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Isomorphism as Isomorphism
import Cubical.Foundations.Prelude as Cubical
import Cubical.Foundations.Univalence as Univalence
import Cubical.HITs.PropositionalTruncation as Truncation
open Truncation using (∣_∣₁)
import Cubical.Homotopy.EilenbergMacLane.GroupStructure as EMGroup
import Cubical.Relation.Binary.Order.Woset.Base as Woset

open import SPT.Cubical.OrdinalGeometry.Cubical.Height.Rank using (rank)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Ordinals using
  (successor)
open import SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Height using
  (InhabitedType; type-path; Fiber; retain; embedding; leaf)
open import SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.HigherType
  using (HigherType; higherTypePoint; higherCell; higherCell-nontrivial)
open import
  SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.PointedUniverse
  using (higherTranslationIso; higherTranslation-zero-input)
open import SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.IteratedLoop
  using
    ( Loop
    ; IteratedLoop
    ; iteratedLoopPoint
    ; PointedSplitEmbedding
    ; pointed-split-embedding
    ; iteratedLoopEmbedding
    ; iteratedLoopEmbedding-nonbase
    ; iteratedLoop-isProp
    )
import SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.SplitEmbedding
  as Split

private
  variable
    ℓ ℓ′ : Level

------------------------------------------------------------------------
-- Translations as loops

-- HigherType at level ℓ, merely inhabited by 0.
Higher : (ℓ : Level) → Set ℓ
Higher ℓ = Lift ℓ HigherType

base : InhabitedType ℓ
base {ℓ} = Higher ℓ Cubical., ∣ lift higherTypePoint ∣₁

-- shift t (x) = x + t, coordinatewise.
shift-iso : HigherType → Isomorphism.Iso (Higher ℓ) (Higher ℓ)
Isomorphism.Iso.fun (shift-iso t) x =
  lift (Isomorphism.Iso.fun (higherTranslationIso t) (lower x))
Isomorphism.Iso.inv (shift-iso t) x =
  lift (Isomorphism.Iso.inv (higherTranslationIso t) (lower x))
Isomorphism.Iso.rightInv (shift-iso t) x =
  Cubical.cong lift
    (Isomorphism.Iso.rightInv (higherTranslationIso t) (lower x))
Isomorphism.Iso.leftInv (shift-iso t) x =
  Cubical.cong lift
    (Isomorphism.Iso.leftInv (higherTranslationIso t) (lower x))

shift : HigherType → Higher ℓ Equiv.≃ Higher ℓ
shift t = Isomorphism.isoToEquiv (shift-iso t)

-- The loop at base given by univalence for shift t.
shift-loop : HigherType → Loop (InhabitedType ℓ) base
shift-loop t = type-path (Univalence.ua (shift t))

-- A loop at base moves 0 to a point of HigherType.
translation : Loop (InhabitedType ℓ) base → HigherType
translation q =
  lower
    (Cubical.transport (Cubical.cong Cubical.fst q) (lift higherTypePoint))

-- Mathematical shape: translation (shift-loop t) = 0 + t = t.
translation-shift : (t : HigherType)
  → translation (shift-loop {ℓ} t) Cubical.≡ t
translation-shift {ℓ} t =
  Cubical.cong (lower {ℓ = ℓ})
    (Univalence.uaβ (shift t) (lift higherTypePoint))
  Cubical.∙
  higherTranslation-zero-input t

-- The zero shift is the identity, so its loop is refl.
shift-zero-function :
  Equiv.equivFun (shift {ℓ} higherTypePoint) Cubical.≡ (λ x → x)
shift-zero-function i x =
  lift λ n →
    EMGroup.rUnitₖ {G = IntegerAbGroup.ℤAbGroup} n (lower x n) i

shift-zero : shift-loop {ℓ} higherTypePoint Cubical.≡ Cubical.refl
shift-zero =
  HLevels.ΣSquareSet (λ _ → Cubical.isProp→isSet Truncation.squash₁)
    (Cubical.cong Univalence.ua (Equiv.equivEq shift-zero-function)
    Cubical.∙
    Univalence.uaIdEquiv)

-- (HigherType , 0) ◁∗ (Loop (InhabitedType ℓ) base , refl).
shift-embedding :
  PointedSplitEmbedding HigherType higherTypePoint
    (Loop (InhabitedType ℓ) base) Cubical.refl
shift-embedding {ℓ} =
  pointed-split-embedding
    (Split.split-embedding shift-loop translation (translation-shift {ℓ}))
    shift-zero

------------------------------------------------------------------------
-- Cells of the merely inhabited types

-- universe-cell n : Ω^(n+1)(InhabitedType ℓ, base) is not refl.
universe-cell : (n : Nat.ℕ)
  → IteratedLoop (Nat.suc n) (InhabitedType ℓ) base
universe-cell n =
  Split.include (iteratedLoopEmbedding n shift-embedding) (higherCell n)

universe-cell-nontrivial : (n : Nat.ℕ)
  → universe-cell {ℓ} n Cubical.≡
      iteratedLoopPoint (Nat.suc n) (InhabitedType ℓ) base
  → ⊥
universe-cell-nontrivial n =
  iteratedLoopEmbedding-nonbase n shift-embedding
    (higherCell n) (higherCell-nontrivial n)

------------------------------------------------------------------------
-- Through a pointed split embedding

-- cell e n : Ω^(n+1)(B, b) is not refl, for e : (InhabitedType ℓ, base)
-- ◁∗ (B, b).
cell : {B : Set ℓ′} {b : B}
  → PointedSplitEmbedding (InhabitedType ℓ) base B b
  → (n : Nat.ℕ) → IteratedLoop (Nat.suc n) B b
cell e n =
  Split.include (iteratedLoopEmbedding (Nat.suc n) e) (universe-cell n)

cell-nontrivial : {B : Set ℓ′} {b : B}
    (e : PointedSplitEmbedding (InhabitedType ℓ) base B b) (n : Nat.ℕ)
  → cell e n Cubical.≡ iteratedLoopPoint (Nat.suc n) B b → ⊥
cell-nontrivial e n =
  iteratedLoopEmbedding-nonbase (Nat.suc n) e
    (universe-cell n) (universe-cell-nontrivial n)

not-hlevel : {B : Set ℓ′} {b : B}
    (e : PointedSplitEmbedding (InhabitedType ℓ) base B b) (n : Nat.ℕ)
  → HLevels.isOfHLevel (Nat.suc (Nat.suc n)) B → ⊥
not-hlevel {b = b} e n hlevel =
  cell-nontrivial e n
    (iteratedLoop-isProp n b hlevel (cell e n) _)

-- B has no finite h-level: from two on the cells refute it, and zero and
-- one would give two.
not-finite-hlevel : {B : Set ℓ′} {b : B}
    (e : PointedSplitEmbedding (InhabitedType ℓ) base B b) (n : Nat.ℕ)
  → HLevels.isOfHLevel n B → ⊥
not-finite-hlevel e Nat.zero contractible =
  not-hlevel e Nat.zero
    (HLevels.isOfHLevelSuc 1 (HLevels.isOfHLevelSuc 0 contractible))
not-finite-hlevel e (Nat.suc Nat.zero) prop =
  not-hlevel e Nat.zero (HLevels.isOfHLevelSuc 1 prop)
not-finite-hlevel e (Nat.suc (Nat.suc n)) =
  not-hlevel e n

------------------------------------------------------------------------
-- The fibers of rank

-- (InhabitedType ℓ, base) ◁∗ (Fiber α, retain α base).
fiber-embedding : (α : Woset.Woset ℓ ℓ)
  → PointedSplitEmbedding (InhabitedType ℓ) base (Fiber α) (retain α base)
fiber-embedding α = pointed-split-embedding (embedding α) Cubical.refl

fiber-not-finite-hlevel : (α : Woset.Woset ℓ ℓ) (n : Nat.ℕ)
  → HLevels.isOfHLevel n (Fiber α) → ⊥
fiber-not-finite-hlevel α = not-finite-hlevel (fiber-embedding α)

-- Mathematical shape: rank has no finite h-level as a map; its fiber over
-- 1 = rank leaf + 1 has none.
rank-not-finite-hlevel : (n : Nat.ℕ)
  → HLevels.isOfHLevelFun n (rank {ℓ}) → ⊥
rank-not-finite-hlevel {ℓ} n hlevel =
  fiber-not-finite-hlevel (rank (leaf {ℓ})) n
    (hlevel (successor (rank leaf)))
