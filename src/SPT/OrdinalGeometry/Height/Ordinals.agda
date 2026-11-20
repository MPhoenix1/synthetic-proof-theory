{-# OPTIONS --safe --without-K #-}

module SPT.OrdinalGeometry.Height.Ordinals where

-- The ordinal of ordinals as a height: the ω₁ geometry one level up, with
-- all heights in place of presentations. A height of level ℓ is a closed tree
-- whose labels are the types of level ℓ, each node branching over its label.
-- Ord(ℓ) is the height of level ℓ + 1 whose children are exactly the heights
-- of level ℓ, lifted. Every height lies below it as a child (upper),
-- everything below it lies below a height (bounded), and it is least (least).
-- Every small family of heights has its fan as an exact strict upper bound
-- (fan) and its join as a least upper bound (join, join-upper, join-least).
-- A child of a height is its subtree at a position of the root, and a height
-- strictly below it lies below one (child-position, strict-position, and
-- conversely below-child-is-strict); a
-- descendant is that child or below it (descendant-position), and a height
-- equal to t or a descendant of t is the subtree of t at a route
-- (descent-route, through node-height). A
-- family below the children of a fan, with a member strictly above each
-- child, has its join equivalent to the fan (cofinal-join-is-fan). The
-- heights bound their small families (heights-bound-families, an instance of
-- Regularity), so no small family is cofinal (not-cofinal), no small type is
-- isomorphic to the heights (heights-are-not-small), and Ord(ℓ) lies below no
-- height of level ℓ (not-small): the Burali-Forti argument for heights. Every
-- small well-founded relation has a canonical height, strictly monotone
-- (rank), whose whole lies below Ord(ℓ). A closed tree over any labels whose
-- branchings are types of level ℓ is read as a height of level ℓ, its order
-- kept (decoded).
--
--   join A F = node (Σ a. root-label (F a)) (λ (a , y) → child-at (F a) y),
--
--   (Π a. Σ b. F a ⊑ G b),  (Π b. Σ a. G b ⊏ F a)  ⊢  join A F ∼ node B G.

open import SPT.Base
open import SPT.Foundation.Accessibility using
  (is-accessible; acc; is-well-founded)
open import SPT.Foundation.Isomorphisms using
  (_≅_; forward; backward; forward-backward)
import SPT.Foundation.Tree as Tree
import SPT.Foundation.Tree.W as TreeW
open import SPT.Foundation.Tree.Child using (HistoryNode; node-child)
open import SPT.Foundation.Tree.Descendant.Route using (descendant-route)
open import SPT.Foundation.Tree.Relation using (node-rel)
open import SPT.Foundation.Tree.Routes using (Routes; subtree-at)
open import SPT.OrdinalGeometry.Height.Simulation using
  (Closed; _◃_; _<_; _⊑_; _⊏_; _≈_; _∼_; below; under; ◃→⊏; ◃-spectrum;
   <-spectrum; ⊑-refl; ⊑-trans; ⊏→⊑; ⊑-⊏-trans; ⊏-⊑-trans; ⊏-irrefl; ≈→⊑)
open import SPT.OrdinalGeometry.Height.Relabeling using
  (relabel; relabel-⊑; relabel-⊏)
open import SPT.OrdinalGeometry.Regularity using
  (Bounded-Families; no-family-is-cofinal)

------------------------------------------------------------------------
-- Heights of a universe

-- Mathematical shape: Height(ℓ) = W (A : Set ℓ). A, as closed trees.

Height : (ℓ : Level) → Set (lsuc ℓ)
Height ℓ = Closed (Set ℓ) (λ A → A)

module _ {ℓ : Level} where

  -- A height of level ℓ, read at level ℓ + 1: each label A becomes Lift A,
  -- with the same children, a relabeling whose positions are lowered
  -- (Height.Relabeling).
  lift-height : Height ℓ → Height (lsuc ℓ)
  lift-height = relabel (Lift (lsuc ℓ)) (λ A → lower)

  lift-⊑ : {x y : Height ℓ} → x ⊑ y → lift-height x ⊑ lift-height y
  lift-⊑ =
    relabel-⊑ (Lift (lsuc ℓ)) (λ A → lower) (λ A → lift) (λ A y → refl)

  lift-⊏ : {x y : Height ℓ} → x ⊏ y → lift-height x ⊏ lift-height y
  lift-⊏ =
    relabel-⊏ (Lift (lsuc ℓ)) (λ A → lower) (λ A → lift) (λ A y → refl)

module _ {ℓ κ : Level} {C : Set κ} (D : C → Set ℓ) where

  -- Mathematical shape: decoded D (node c f) = node (D c) (decoded D ∘ f).
  -- A closed tree whose branchings are types of level ℓ, read as a height:
  -- each label c becomes its branching D c, with the same children, a
  -- relabeling that keeps every position (Height.Relabeling). The
  -- simulation order compares branchings alone, so it is kept.
  decoded : Closed C D → Height ℓ
  decoded = relabel D (λ c y → y)

  decoded-⊑ : {x y : Closed C D} → x ⊑ y → decoded x ⊑ decoded y
  decoded-⊑ = relabel-⊑ D (λ c y → y) (λ c y → y) (λ c y → refl)

  decoded-⊏ : {x y : Closed C D} → x ⊏ y → decoded x ⊏ decoded y
  decoded-⊏ = relabel-⊏ D (λ c y → y) (λ c y → y) (λ c y → refl)

------------------------------------------------------------------------
-- The ordinal of ordinals

-- Mathematical shape: Ord(ℓ) = node (Height ℓ) lift-height : Height(ℓ+1).

Ord : (ℓ : Level) → Height (lsuc ℓ)
Ord ℓ = Tree.node (Height ℓ) lift-height

module _ {ℓ : Level} where

  -- Every height of level ℓ is a child of Ord(ℓ).
  upper : (t : Height ℓ) → lift-height t ◃ Ord ℓ
  upper t = node-child t

  -- Everything below Ord(ℓ) lies below a height of level ℓ.
  bounded : {x : Height (lsuc ℓ)} → x ⊏ Ord ℓ →
    Σ (Height ℓ) (λ t → x ⊑ lift-height t)
  bounded (under t p) = t , p

  -- Ord(ℓ) is least among heights above every height of level ℓ.
  least : (x : Height (lsuc ℓ)) →
    ((t : Height ℓ) → lift-height t ⊏ x) → Ord ℓ ⊑ x
  least x above = below above

------------------------------------------------------------------------
-- Fans, joins, cofinality and Burali-Forti

module _ {ℓ : Level} where

  -- Every small family of heights has its fan as an exact strict upper
  -- bound: each member is a child of the fan.
  fan : (A : Set ℓ) (F : A → Height ℓ) →
    Σ (Height ℓ) (λ t → (a : A) → F a ◃ t)
  fan A F = Tree.node A F , node-child

  -- The label at the root of a height, and the subtree at a point of it.
  root-label : Height ℓ → Set ℓ
  root-label (Tree.hole ())
  root-label (Tree.node A f) = A

  child-at : (t : Height ℓ) → root-label t → Height ℓ
  child-at (Tree.hole ())
  child-at (Tree.node A f) = f

  -- A height lies below the node over its root label and its subtrees.
  unfolded : (t : Height ℓ) → t ⊑ Tree.node (root-label t) (child-at t)
  unfolded (Tree.hole ())
  unfolded (Tree.node A f) = ⊑-refl (Tree.node A f)

  child-at-below : (s t : Height ℓ) (y : root-label s) → s ⊑ t →
    child-at s y ⊏ t
  child-at-below (Tree.hole ()) t y p
  child-at-below (Tree.node A f) t y (below q) = q y

  -- Mathematical shape: s ◃ t gives a position y of t with s = child-at t y.
  child-position : (s t : Height ℓ) → s ◃ t →
    Σ (root-label t) (λ y → s ＝ child-at t y)
  child-position s (Tree.hole ()) p
  child-position s (Tree.node A f) p = ◃-spectrum p

  -- Mathematical shape: s ⊏ t gives a position y of t with s ⊑ child-at t y.
  strict-position : (s t : Height ℓ) → s ⊏ t →
    Σ (root-label t) (λ y → s ⊑ child-at t y)
  strict-position s (Tree.hole ()) p
  strict-position s (Tree.node A f) (under y p) = y , p

  -- Mathematical shape: s ⊑ child-at t y gives s ⊏ t.
  below-child-is-strict : (s t : Height ℓ) (y : root-label t) →
    s ⊑ child-at t y → s ⊏ t
  below-child-is-strict s (Tree.hole ()) y p
  below-child-is-strict s (Tree.node A f) y p = under y p

  -- Mathematical shape: s < t gives a position y of t with s = child-at t y
  -- or s < child-at t y.
  descendant-position : (s t : Height ℓ) → s < t →
    Σ (root-label t) (λ y → (s ＝ child-at t y) ⊎ (s < child-at t y))
  descendant-position s (Tree.hole ()) p
  descendant-position s (Tree.node A f) p = <-spectrum p

  -- The height at a node of a closed tree of heights.
  node-height : HistoryNode (TreeW.Branching.signature (Set ℓ) (λ A → A)) →
    Height ℓ
  node-height (j , t) = t

  -- Mathematical shape: s = t or s < t gives a route ρ of t whose subtree is
  -- s.
  descent-route : (s t : Height ℓ) → (s ＝ t) ⊎ (s < t) →
    Σ (Routes t) (λ ρ → node-height (subtree-at t ρ) ＝ s)
  descent-route s t (inl e) = inl (lift ⋆) , (e ⁻¹)
  descent-route s t (inr d) =
    inr (pr₁ (descendant-route d)) , ap node-height (pr₂ (descendant-route d))

  -- Mathematical shape: join A F = node (Σ a. root-label (F a)) subtrees.
  -- Every small family of heights has a least upper bound.
  join : (A : Set ℓ) → (A → Height ℓ) → Height ℓ
  join A F =
    Tree.node (Σ A (λ a → root-label (F a)))
      (λ p → child-at (F (pr₁ p)) (pr₂ p))

  join-upper : (A : Set ℓ) (F : A → Height ℓ) (a : A) → F a ⊑ join A F
  join-upper A F a =
    ⊑-trans (unfolded (F a))
      (below (λ y → under (a , y) (⊑-refl (child-at (F a) y))))

  join-least : (A : Set ℓ) (F : A → Height ℓ) (t : Height ℓ) →
    ((a : A) → F a ⊑ t) → join A F ⊑ t
  join-least A F t h =
    below (λ p → child-at-below (F (pr₁ p)) t (pr₂ p) (h (pr₁ p)))

  -- Mathematical shape: join A F ∼ node B G when F and G are cofinal in
  -- each other, G strictly.
  cofinal-join-is-fan : (A B : Set ℓ) (F : A → Height ℓ) (G : B → Height ℓ) →
    ((a : A) → Σ B (λ b → F a ⊑ G b)) →
    ((b : B) → Σ A (λ a → G b ⊏ F a)) →
    join A F ∼ Tree.node B G
  cofinal-join-is-fan A B F G down up =
    join-least A F (Tree.node B G)
      ( λ a →
          ⊏→⊑
            (⊑-⊏-trans (pr₂ (down a)) (◃→⊏ (node-child (pr₁ (down a))))))
    , below (λ b → ⊏-⊑-trans (pr₂ (up b)) (join-upper A F (pr₁ (up b))))

  -- The heights of level ℓ with the families indexed by the types of level
  -- ℓ: an instance of Regularity, the fan of a family as its bound.
  heights-bound-families :
    Bounded-Families (Height ℓ) _⊏_ _⊑_ (Set ℓ) (λ A → A)
  heights-bound-families = record
    { strict-is-irreflexive = ⊏-irrefl
    ; strict-then-weak = ⊏-⊑-trans
    ; upper-bound = λ A F →
        Tree.node A F , (λ a → under a (⊑-refl (F a)))
    }

  -- No small family of heights is cofinal: its fan would lie below a
  -- member, which is a child of the fan.
  not-cofinal : (A : Set ℓ) (F : A → Height ℓ) →
    ¬ ((t : Height ℓ) → Σ A (λ a → t ⊑ F a))
  not-cofinal A F = no-family-is-cofinal heights-bound-families A F

  -- No small type is isomorphic to the heights of its level: its family of
  -- heights would be cofinal.
  heights-are-not-small : (A : Set ℓ) → A ≅ Height ℓ → 𝟘
  heights-are-not-small A E =
    not-cofinal A (forward E)
      ( λ t →
          backward E t
          , transport (λ s → t ⊑ s) (forward-backward E t ⁻¹) (⊑-refl t))

  -- Ord(ℓ) lies below no height of level ℓ: the lift of that height is a
  -- child of Ord(ℓ).
  not-small : (t : Height ℓ) → ¬ (Ord ℓ ⊑ lift-height t)
  not-small t p =
    ⊏-irrefl (lift-height t) (⊏-⊑-trans (◃→⊏ (upper t)) p)

------------------------------------------------------------------------
-- Canonical heights of small well-founded relations

module _ {ℓ : Level} {A : Set ℓ} (less : A → A → Set ℓ) where

  -- Mathematical shape: rank(x) = node (Σ y. y < x) (rank ∘ pr₁).
  rank-at : (x : A) → is-accessible less x → Height ℓ
  rank-at x (acc smaller) =
    Tree.node (Σ A (λ y → less y x))
      (λ p → rank-at (pr₁ p) (smaller (pr₁ p) (pr₂ p)))

  -- Ranks do not depend on the accessibility witness, up to structural
  -- equality.
  rank-at-≈ : (x : A) (a b : is-accessible less x) →
    rank-at x a ≈ rank-at x b
  rank-at-≈ x (acc smaller) (acc smaller′) =
    node-rel (λ p →
      rank-at-≈ (pr₁ p) (smaller (pr₁ p) (pr₂ p))
        (smaller′ (pr₁ p) (pr₂ p)))

  rank : is-well-founded less → A → Height ℓ
  rank wf x = rank-at x (wf x)

  -- y < x gives rank y ⊏ rank x: rank y is a child of rank x, up to the
  -- accessibility witness.
  rank-strict : (wf : is-well-founded less) {x y : A} → less y x →
    rank wf y ⊏ rank wf x
  rank-strict wf {x} {y} p with wf x
  ... | acc smaller =
    under (y , p) (≈→⊑ (rank-at-≈ y (wf y) (smaller y p)))

  -- The height of the whole relation, and its place below Ord(ℓ).
  whole : is-well-founded less → Height ℓ
  whole wf = Tree.node A (rank wf)

  whole-below : (wf : is-well-founded less) →
    lift-height (whole wf) ◃ Ord ℓ
  whole-below wf = upper (whole wf)
