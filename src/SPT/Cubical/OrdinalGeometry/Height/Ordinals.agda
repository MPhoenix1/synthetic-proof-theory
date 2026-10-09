{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Height.Ordinals where

-- The ordinal of ordinals as a height: the ω₁ geometry one level up, with
-- all heights in place of presentations.  A height of level ℓ is a closed
-- Core tree whose labels are the types of level ℓ, each node branching
-- over its label.  Ord(ℓ) is the height of level ℓ + 1 whose children are
-- exactly the heights of level ℓ, lifted.  Every height lies below it as a
-- child (upper), everything below it lies below a height (bounded), and it
-- is least (least).  Every small family of heights has its fan as an exact
-- upper bound (fan), no small family is cofinal (not-cofinal), and so
-- Ord(ℓ) lies below no height of level ℓ (not-small): the Burali-Forti
-- argument for heights.  Every small well-founded relation has a canonical
-- height, strictly monotone (rank), whose whole lies below Ord(ℓ).

open import Agda.Primitive using (Level; lsuc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Level using (Lift; lift; lower)
open import Relation.Nullary.Negation using (¬_)

open import SPT.Cubical.Core.WellFounded using (Acc; acc; WellFounded)
import SPT.Cubical.Core.Generator.Tree as Tree
open import SPT.Cubical.Core.Generator.Tree.Child using (node-child)
open import SPT.Cubical.Core.Generator.Tree.Relation using (node-rel)
open import SPT.Cubical.OrdinalGeometry.Height.Simulation using
  (Closed; _◃_; _⊑_; _⊏_; _≈_; below; under; ◃→⊏; ⊏-⊑-trans; ⊏-irrefl;
   ≈→⊑)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- Heights of a universe

-- Mathematical shape: Height(ℓ) = W (A : Set ℓ). A, closed Core trees.
Height : (ℓ : Level) → Set (lsuc ℓ)
Height ℓ = Closed (Set ℓ) (λ A → A)

-- A height of level ℓ, read at level ℓ + 1: each label A becomes Lift A,
-- with the same children.
lift-height : Height ℓ → Height (lsuc ℓ)
lift-height {ℓ} (Tree.hole ())
lift-height {ℓ} (Tree.node A f) =
  Tree.node (Lift (lsuc ℓ) A) (λ a → lift-height (f (lower a)))

mutual
  lift-⊑ : {x y : Height ℓ} → x ⊑ y → lift-height x ⊑ lift-height y
  lift-⊑ (below p) = below λ a → lift-⊏ (p (lower a))

  lift-⊏ : {x y : Height ℓ} → x ⊏ y → lift-height x ⊏ lift-height y
  lift-⊏ (under z p) = under (lift z) (lift-⊑ p)

------------------------------------------------------------------------
-- The ordinal of ordinals

-- Mathematical shape: Ord(ℓ) = node (Height ℓ) lift-height : Height(ℓ+1).
Ord : (ℓ : Level) → Height (lsuc ℓ)
Ord ℓ = Tree.node (Height ℓ) lift-height

-- Every height of level ℓ is a child of Ord(ℓ).
upper : (t : Height ℓ) → lift-height t ◃ Ord ℓ
upper t = node-child t

-- Everything below Ord(ℓ) lies below a height of level ℓ.
bounded : {x : Height (lsuc ℓ)} → x ⊏ Ord ℓ
  → Σ (Height ℓ) λ t → x ⊑ lift-height t
bounded (under t p) = t , p

-- Ord(ℓ) is least among heights above every height of level ℓ.
least : (x : Height (lsuc ℓ))
  → ((t : Height ℓ) → lift-height t ⊏ x) → Ord ℓ ⊑ x
least x above = below above

------------------------------------------------------------------------
-- Fans, cofinality, and Burali-Forti

-- Every small family of heights has its fan as an exact upper bound: each
-- member is a child of the fan.
fan : (A : Set ℓ) (F : A → Height ℓ)
  → Σ (Height ℓ) λ t → (a : A) → F a ◃ t
fan A F = Tree.node A F , node-child

-- No small family of heights is cofinal: its fan would lie below a member,
-- which is a child of the fan.
not-cofinal : (A : Set ℓ) (F : A → Height ℓ)
  → ¬ ((t : Height ℓ) → Σ A λ a → t ⊑ F a)
not-cofinal A F cofinal =
  let (a , p) = cofinal (Tree.node A F)
  in ⊏-irrefl (F a) (⊏-⊑-trans (◃→⊏ (node-child a)) p)

-- Ord(ℓ) lies below no height of level ℓ: the lift of that height is a
-- child of Ord(ℓ).
not-small : (t : Height ℓ) → ¬ (Ord ℓ ⊑ lift-height t)
not-small t p =
  ⊏-irrefl (lift-height t) (⊏-⊑-trans (◃→⊏ (upper t)) p)

------------------------------------------------------------------------
-- Canonical heights of small well-founded relations

module _ {A : Set ℓ} (_<_ : A → A → Set ℓ) where

  -- Mathematical shape: rank(x) = node (Σ y. y < x) (rank ∘ proj₁).
  rankAt : (x : A) → Acc _<_ x → Height ℓ
  rankAt x (acc smaller) =
    Tree.node (Σ A λ y → y < x)
      λ p → rankAt (proj₁ p) (smaller (proj₁ p) (proj₂ p))

  -- Ranks do not depend on the accessibility witness, up to structural
  -- equality.
  rankAt-≈ : (x : A) (a b : Acc _<_ x) → rankAt x a ≈ rankAt x b
  rankAt-≈ x (acc smaller) (acc smaller′) =
    node-rel λ p →
      rankAt-≈ (proj₁ p) (smaller (proj₁ p) (proj₂ p))
        (smaller′ (proj₁ p) (proj₂ p))

  rank : WellFounded _<_ → A → Height ℓ
  rank wf x = rankAt x (wf x)

  -- y < x gives rank y ⊏ rank x: rank y is a child of rank x, up to the
  -- accessibility witness.
  rank-strict : (wf : WellFounded _<_) {x y : A} → y < x
    → rank wf y ⊏ rank wf x
  rank-strict wf {x} {y} p with wf x
  ... | acc smaller =
    under (y , p) (≈→⊑ (rankAt-≈ y (wf y) (smaller y p)))

  -- The height of the whole relation, and its place below Ord(ℓ).
  whole : WellFounded _<_ → Height ℓ
  whole wf = Tree.node A (rank wf)

  whole-below : (wf : WellFounded _<_) → lift-height (whole wf) ◃ Ord ℓ
  whole-below wf = upper (whole wf)
