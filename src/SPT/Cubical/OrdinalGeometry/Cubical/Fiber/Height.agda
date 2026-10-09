{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Height where

-- What rank forgets at heights.  For every well-order α, the fiber of
-- rank over α + 1 contains the merely inhabited types Σ A. ∥A∥ as a split
-- retract: A goes to the node labelled A whose children all have rank α,
-- and recovery reads the root label, merely inhabited because the rank of
-- the root has a point.  Negation on 𝟐 gives a nontrivial loop, so that
-- fiber is not a set and rank is not an embedding, at every level.  Over
-- an empty well-order the fiber is contractible: the leaf is the only
-- height of rank 0.

open import Agda.Primitive using (Level; lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Level using (Lift; lift; lower)

import Cubical.Data.Bool as Bool
open Bool using (Bool; true; false; not)
import Cubical.Data.Empty as Empty
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Isomorphism as Isomorphism
import Cubical.Foundations.Prelude as Cubical
import Cubical.Foundations.Univalence as Univalence
import Cubical.Functions.Embedding as Embedding
import Cubical.HITs.PropositionalTruncation as Truncation
open Truncation using (∥_∥₁; ∣_∣₁)
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

import SPT.Cubical.Core.Generator.Tree as Tree
open import SPT.Cubical.OrdinalGeometry.Height.Ordinals using (Height)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Ordinals using
  (successor; top; successor-strict; successor-least; segments→simulation)
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Supremum.Family
  as Family
open import SPT.Cubical.OrdinalGeometry.Cubical.Height.Rank using
  (rank; child; least; canonical-height; canonical)
import SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.SplitEmbedding
  as Split

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- Merely inhabited types

-- Mathematical shape: InhabitedType(ℓ) = Σ (A : Set ℓ). ∥A∥.
InhabitedType : (ℓ : Level) → Set (lsuc ℓ)
InhabitedType ℓ = Cubical.Σ (Set ℓ) λ A → ∥ A ∥₁

-- A path of types is a path of merely inhabited types.
type-path : {X Y : InhabitedType ℓ}
  → Cubical.fst X Cubical.≡ Cubical.fst Y → X Cubical.≡ Y
type-path {X = X} {Y = Y} p i =
  p i Cubical.,
  Cubical.isProp→PathP {B = λ j → ∥ p j ∥₁} (λ j → Truncation.squash₁)
    (Cubical.snd X) (Cubical.snd Y) i

------------------------------------------------------------------------
-- Labels of ranks

-- A point of rank (node A f) merely gives a point of A: a point of the
-- supremum is merely the class of a point of some member.
inhabited : (A : Set ℓ) (f : A → Height ℓ)
  → Cubical.fst (rank (Tree.node A f)) → ∥ A ∥₁
inhabited A f x =
  Truncation.map Cubical.fst
    (Family.covered (λ a → successor (rank (f a))) x)

------------------------------------------------------------------------
-- The fiber over a successor

-- copies A α = node A (λ _ → canonical-height α): A copies of a height of
-- rank α under one root.
copies : (A : Set ℓ) → Woset.Woset ℓ ℓ → Height ℓ
copies A α = Tree.node A λ _ → canonical-height α

-- Mathematical shape: ∥A∥ → rank (copies A α) = α + 1.
copies-rank : (A : Set ℓ) (α : Woset.Woset ℓ ℓ)
  → ∥ A ∥₁ → rank (copies A α) Cubical.≡ successor α
copies-rank A α =
  Truncation.rec (Woset.isSetWoset _ _) λ a →
    Equiv.equivFun (Woset.WosetPath _ _)
      (Simulation.isAntisym≼Equiv (rank (copies A α)) (successor α)
        (least A (λ _ → canonical-height α) (successor α) λ _ →
          Simulation.≺RespectsEquivL (successor α)
            (Woset.invWosetEquiv (canonical α)) (successor-strict α))
        (successor-least α (rank (copies A α))
          (Simulation.≺RespectsEquivL (rank (copies A α)) (canonical α)
            (child A (λ _ → canonical-height α) a))))

-- Mathematical shape: Fiber(α) = Σ (t : Height ℓ). rank t = α + 1.
Fiber : Woset.Woset ℓ ℓ → Set (lsuc ℓ)
Fiber α = Equiv.fiber rank (successor α)

retain : (α : Woset.Woset ℓ ℓ) → InhabitedType ℓ → Fiber α
retain α (Cubical._,_ A m) = copies A α Cubical., copies-rank A α m

-- Recovery reads the root label.  The path carries the top point of α + 1
-- back to the rank of the root, so the label is merely inhabited.
recover : (α : Woset.Woset ℓ ℓ) → Fiber α → InhabitedType ℓ
recover α (Cubical._,_ (Tree.hole ()) p)
recover α (Cubical._,_ (Tree.node A f) p) =
  A Cubical.,
  inhabited A f
    (Cubical.transport (Cubical.cong Cubical.fst (Cubical.sym p)) (top α))

-- Mathematical shape: recover (retain X) = X, by refl on the type.
recover-retain : (α : Woset.Woset ℓ ℓ) (X : InhabitedType ℓ)
  → recover α (retain α X) Cubical.≡ X
recover-retain α X = type-path Cubical.refl

-- InhabitedType(ℓ) ◁ Fiber(α).
embedding : (α : Woset.Woset ℓ ℓ)
  → Split.SplitEmbedding (InhabitedType ℓ) (Fiber α)
embedding α =
  Split.split-embedding (retain α) (recover α) (recover-retain α)

-- So an h-level bound on the fiber bounds the merely inhabited types.
reflects-hlevel : (n : HLevels.HLevel) (α : Woset.Woset ℓ ℓ)
  → HLevels.isOfHLevel n (Fiber α)
  → HLevels.isOfHLevel n (InhabitedType ℓ)
reflects-hlevel n α =
  HLevels.isOfHLevelRetract n (retain α) (recover α) (recover-retain α)

------------------------------------------------------------------------
-- A nontrivial loop

-- 𝟐 at level ℓ, and its negation.
Two : (ℓ : Level) → Set ℓ
Two ℓ = Lift ℓ Bool

negate : Two ℓ → Two ℓ
negate (lift b) = lift (not b)

negate-negate : (x : Two ℓ) → negate (negate x) Cubical.≡ x
negate-negate (lift b) = Cubical.cong lift (Bool.notnot b)

negation : Two ℓ Equiv.≃ Two ℓ
negation =
  Isomorphism.isoToEquiv
    (Isomorphism.iso negate negate negate-negate negate-negate)

-- 𝟐, merely inhabited by true.  No base point has to be fixed, so 𝟐
-- suffices where the pointed universe needs 𝟐 × 𝟐.
two : InhabitedType ℓ
two {ℓ} = Two ℓ Cubical., ∣ lift true ∣₁

-- Mathematical shape: two = two, by univalence for negation.
negation-loop : two {ℓ} Cubical.≡ two
negation-loop = type-path (Univalence.ua negation)

-- It is not refl: transport along it moves true to false.
negation-loop-not-refl : negation-loop {ℓ} Cubical.≡ Cubical.refl → ⊥
negation-loop-not-refl {ℓ} loop=refl =
  Empty.rec (Bool.false≢true (Cubical.cong lower moved))
  where
    type-loop : Univalence.ua (negation {ℓ}) Cubical.≡ Cubical.refl
    type-loop = Cubical.cong (Cubical.cong Cubical.fst) loop=refl

    moved : Cubical._≡_ {A = Two ℓ} (lift false) (lift true)
    moved =
      Cubical.sym (Univalence.uaβ negation (lift true))
      Cubical.∙
      Cubical.cong (λ q → Cubical.transport q (lift true)) type-loop
      Cubical.∙
      Cubical.transportRefl (lift true)

not-set : Cubical.isSet (InhabitedType ℓ) → ⊥
not-set set = negation-loop-not-refl (set two two negation-loop Cubical.refl)

-- So no fiber of rank over a successor is a set, or a proposition.
fiber-not-set : (α : Woset.Woset ℓ ℓ) → Cubical.isSet (Fiber α) → ⊥
fiber-not-set α set = not-set (reflects-hlevel 2 α set)

fiber-not-prop : (α : Woset.Woset ℓ ℓ) → Cubical.isProp (Fiber α) → ⊥
fiber-not-prop α prop = fiber-not-set α (Cubical.isProp→isSet prop)

------------------------------------------------------------------------
-- The fiber over 0

-- The leaf, node ⊥ (λ ()), has no children.
no-children : Empty.⊥* {ℓ} → Height ℓ
no-children ()

leaf : Height ℓ
leaf = Tree.node Empty.⊥* no-children

-- Mathematical shape: rank is not an embedding: its fiber over 1 = 0 + 1
-- is not a proposition.
not-embedding : Embedding.isEmbedding (rank {ℓ}) → ⊥
not-embedding {ℓ} rank-embedding =
  fiber-not-prop (rank (leaf {ℓ}))
    (Embedding.isEmbedding→hasPropFibers rank-embedding
      (successor (rank leaf)))

-- Mathematical shape: (|Z| → ⊥) → isContr (Σ t. rank t = Z).  A height
-- of rank Z has an empty root label, since each child places a point in
-- its rank, and by univalence every empty label is ⊥.
empty-fiber : (Z : Woset.Woset ℓ ℓ) → (Cubical.fst Z → ⊥)
  → Cubical.isContr (Equiv.fiber rank Z)
empty-fiber {ℓ} Z empty = (leaf Cubical., leaf-rank) Cubical., contraction
  where
    leaf-rank : rank leaf Cubical.≡ Z
    leaf-rank =
      Equiv.equivFun (Woset.WosetPath _ _)
        (Simulation.isAntisym≼Equiv (rank leaf) Z
          (least Empty.⊥* no-children Z λ ())
          (segments→simulation {H = Z} {K = rank leaf} λ z →
            ⊥-elim (empty z)))

    contraction : (y : Equiv.fiber rank Z) → (leaf Cubical., leaf-rank)
      Cubical.≡ y
    contraction (Cubical._,_ (Tree.hole ()) p)
    contraction (Cubical._,_ (Tree.node A f) p) i =
      shape i Cubical.,
      Cubical.isProp→PathP {B = λ j → rank (shape j) Cubical.≡ Z}
        (λ j → Woset.isSetWoset _ _) leaf-rank p i
      where
        no-label : A → ⊥
        no-label a =
          empty
            (Cubical.transport (Cubical.cong Cubical.fst p)
              (Cubical.fst (child A f a)))

        label : Empty.⊥* Equiv.≃ A
        label = Empty.uninhabEquiv (λ ()) λ a → ⊥-elim (no-label a)

        shape : leaf Cubical.≡ Tree.node A f
        shape j =
          Tree.node (Univalence.ua label j)
            (Univalence.ua→ {e = label} {B = λ _ → Height ℓ}
              {f₀ = no-children} {f₁ = f} (λ ()) j)
