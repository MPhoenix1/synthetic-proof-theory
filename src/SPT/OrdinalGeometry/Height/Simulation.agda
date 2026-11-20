{-# OPTIONS --safe --without-K #-}

module SPT.OrdinalGeometry.Height.Simulation where

-- Closed trees and their relations, for any labels and branchings:
-- structural equality ≈ (equal labels and related children), ancestry ◃ and
-- < (immediate and proper descendants), and the simulation order ⊑ and ⊏
-- with its equivalence ∼. Ancestry describes how a tree is built; the
-- simulation order compares trees by their branching alone. Both strict
-- relations are well-founded, ancestry lies inside the strict simulation
-- order (<→⊏), and structural equality gives equivalence (≈→∼). The shape
-- equivalence ≅ retains an isomorphism of branch types at every node;
-- structural equality gives it (≈→≅) and it gives ∼ (≅→∼). The heights of a
-- universe (Height.Ordinals) and the boundaries of reflections
-- (Height.Reflection) are compared in this order.
--
--     Π y. f y ⊏ t                 x ⊑ h z
--   ---------------- below      ---------------- under z
--     node a f ⊑ t                x ⊏ node b h

open import SPT.Base
open import SPT.Foundation.Accessibility using
  (is-accessible; acc; is-well-founded; accessible-points-have-no-loops)
open import SPT.Foundation.Isomorphisms using (forward; backward)
  renaming (_≅_ to Isomorphic; ≅-refl to isomorphic-refl;
            ≅-sym to isomorphic-sym; ≅-trans to isomorphic-trans)
open import SPT.Foundation.WellFounded.Pullback using
  (pullback-relation; pullback-is-well-founded)
import SPT.Foundation.Tree as Tree
import SPT.Foundation.Tree.W as TreeW
open import SPT.Foundation.Tree.Child using
  (HistoryNode; HistoryChild; node-child; history-child-wf)
open import SPT.Foundation.Tree.Descendant using
  (Descendant; immediate; nested; descendant-trans; descendant-wf)
open import SPT.Foundation.Tree.Relation using
  (TreeRel; hole-rel; node-rel; rel-refl; rel-sym; rel-compose)

------------------------------------------------------------------------
-- Structural equality of closed trees

-- The same-operation relation with identity on the empty hole family:
-- equal operations at every node and related children at every position.
-- It is the identity of trees available without function extensionality.

module _ {ℓo ℓp : Level} {S : Tree.Signature lzero ℓo ℓp}
  {j : Tree.Judgment S} where

  infix 6 _≈_

  _≈_ : Tree.History S j → Tree.History S j → Set (ℓo ⊔ ℓp)
  _≈_ = TreeRel _＝_

  ≈-refl : (x : Tree.History S j) → x ≈ x
  ≈-refl = rel-refl (λ x → refl)

  ≈-sym : {x y : Tree.History S j} → x ≈ y → y ≈ x
  ≈-sym = rel-sym (λ e → e ⁻¹)

  ≈-trans : {x y z : Tree.History S j} → x ≈ y → y ≈ z → x ≈ z
  ≈-trans = rel-compose (λ e d → e ∙ d)

------------------------------------------------------------------------
-- Branching trees and their ancestry

-- Closed L R is the type of closed trees whose nodes are labels a : L
-- branching over R a. Ancestry is the child and descendant relation of
-- trees at the one judgment; it describes the construction.

Closed : {ℓa ℓb : Level} (L : Set ℓa) → (L → Set ℓb) → Set (ℓa ⊔ ℓb)
Closed L R = TreeW.W L R

module _ {ℓa ℓb : Level} {L : Set ℓa} {R : L → Set ℓb} where

  total : Closed L R → HistoryNode (TreeW.Branching.signature L R)
  total x = ⋆ , x

  infix 30 _◃_ _<_

  _◃_ : Closed L R → Closed L R → Set (ℓa ⊔ ℓb)
  _◃_ = pullback-relation total HistoryChild

  _<_ : Closed L R → Closed L R → Set (ℓa ⊔ ℓb)
  _<_ = pullback-relation total Descendant

  ◃-wf : is-well-founded _◃_
  ◃-wf = pullback-is-well-founded total HistoryChild history-child-wf

  <-wf : is-well-founded _<_
  <-wf = pullback-is-well-founded total Descendant descendant-wf

  <-trans : {x y z : Closed L R} → x < y → y < z → x < z
  <-trans = descendant-trans

  <-irrefl : (x : Closed L R) → ¬ (x < x)
  <-irrefl x = accessible-points-have-no-loops (<-wf x)

  -- Every immediate predecessor of a node is one of its literal children;
  -- every strict predecessor is a child or lies below one.
  ◃-spectrum : {a : L} {f : R a → Closed L R} {x : Closed L R} →
    x ◃ Tree.node a f → Σ (R a) (λ y → x ＝ f y)
  ◃-spectrum (node-child y) = y , refl

  <-spectrum : {a : L} {f : R a → Closed L R} {x : Closed L R} →
    x < Tree.node a f → Σ (R a) (λ y → (x ＝ f y) ⊎ (x < f y))
  <-spectrum (immediate (node-child y)) = y , inl refl
  <-spectrum (nested (node-child y) route) = y , inr route

------------------------------------------------------------------------
-- The simulation order

-- Trees are compared by ⊑ and ⊏, which see only branching and never which
-- label produced a node. _∼_ is mutual ⊑. Nonclaim: ⊑ is not total, and ∼
-- does not imply ≈.

infix 30 _⊑_ _⊏_

mutual
  data _⊑_ {ℓ₁ ℓ₂ : Level} {L : Set ℓ₁} {R : L → Set ℓ₂}
    : Closed L R → Closed L R → Set (ℓ₁ ⊔ ℓ₂) where
    below : {a : L} {f : R a → Closed L R} {t : Closed L R} →
      ((y : R a) → f y ⊏ t) → Tree.node a f ⊑ t

  data _⊏_ {ℓ₁ ℓ₂ : Level} {L : Set ℓ₁} {R : L → Set ℓ₂}
    : Closed L R → Closed L R → Set (ℓ₁ ⊔ ℓ₂) where
    under : {x : Closed L R} {b : L} {h : R b → Closed L R}
      (z : R b) → x ⊑ h z → x ⊏ Tree.node b h

module _ {ℓa ℓb : Level} {L : Set ℓa} {R : L → Set ℓb} where

  infix 30 _∼_

  _∼_ : Closed L R → Closed L R → Set (ℓa ⊔ ℓb)
  x ∼ y = (x ⊑ y) × (y ⊑ x)

  ⊑-refl : (x : Closed L R) → x ⊑ x
  ⊑-refl (Tree.hole ())
  ⊑-refl (Tree.node a f) = below (λ y → under y (⊑-refl (f y)))

  ◃→⊏ : {x y : Closed L R} → x ◃ y → x ⊏ y
  ◃→⊏ {x} (node-child p) = under p (⊑-refl x)

  ⊏→⊑ : {x y : Closed L R} → x ⊏ y → x ⊑ y
  ⊏→⊑ (under z (below p)) = below (λ u → under z (⊏→⊑ (p u)))

  mutual
    ⊑-trans : {x y z : Closed L R} → x ⊑ y → y ⊑ z → x ⊑ z
    ⊑-trans (below p) y⊑z = below (λ u → ⊏-⊑-trans (p u) y⊑z)

    ⊏-⊑-trans : {x y z : Closed L R} → x ⊏ y → y ⊑ z → x ⊏ z
    ⊏-⊑-trans (under v x⊑hv) (below q) = ⊑-⊏-trans x⊑hv (q v)

    ⊑-⊏-trans : {x y z : Closed L R} → x ⊑ y → y ⊏ z → x ⊏ z
    ⊑-⊏-trans x⊑y (under w y⊑kw) = under w (⊑-trans x⊑y y⊑kw)

  ⊏-trans : {x y z : Closed L R} → x ⊏ y → y ⊏ z → x ⊏ z
  ⊏-trans x⊏y y⊏z = ⊑-⊏-trans (⊏→⊑ x⊏y) y⊏z

  -- Below a tree t, every tree is accessible.
  ⊏-accessible : (t x : Closed L R) → x ⊏ t → is-accessible _⊏_ x
  ⊏-accessible (Tree.hole ()) x x⊏t
  ⊏-accessible (Tree.node b h) x (under v x⊑hv) =
    acc (λ y y⊏x → ⊏-accessible (h v) y (⊏-⊑-trans y⊏x x⊑hv))

  ⊏-wf : is-well-founded _⊏_
  ⊏-wf t = acc (⊏-accessible t)

  -- In particular no tree lies below itself, so ⊏ is not degenerate.
  ⊏-irrefl : (x : Closed L R) → ¬ (x ⊏ x)
  ⊏-irrefl x = accessible-points-have-no-loops (⊏-wf x)

  <→⊏ : {x y : Closed L R} → x < y → x ⊏ y
  <→⊏ (immediate step) = ◃→⊏ step
  <→⊏ (nested (node-child p) route) =
    ⊑-⊏-trans (⊏→⊑ (<→⊏ route)) (◃→⊏ (node-child p))

  ≈→⊑ : {x y : Closed L R} → x ≈ y → x ⊑ y
  ≈→⊑ (hole-rel {_} {()} r)
  ≈→⊑ (node-rel p) = below (λ u → under u (≈→⊑ (p u)))

  ≈→∼ : {x y : Closed L R} → x ≈ y → x ∼ y
  ≈→∼ p = ≈→⊑ p , ≈→⊑ (≈-sym p)

  ⊏-respˡ-∼ : {x x′ y : Closed L R} → x ∼ x′ → x ⊏ y → x′ ⊏ y
  ⊏-respˡ-∼ x∼x′ x⊏y = ⊑-⊏-trans (pr₂ x∼x′) x⊏y

  ⊏-respʳ-∼ : {x y y′ : Closed L R} → y ∼ y′ → x ⊏ y → x ⊏ y′
  ⊏-respʳ-∼ y∼y′ x⊏y = ⊏-⊑-trans x⊏y (pr₁ y∼y′)

  ∼-refl : (x : Closed L R) → x ∼ x
  ∼-refl x = ⊑-refl x , ⊑-refl x

  ∼-sym : {x y : Closed L R} → x ∼ y → y ∼ x
  ∼-sym (p , q) = q , p

  ∼-trans : {x y z : Closed L R} → x ∼ y → y ∼ z → x ∼ z
  ∼-trans (p , q) (p′ , q′) = ⊑-trans p p′ , ⊑-trans q′ q

  -- Two nodes whose positions correspond in both directions, with each child
  -- below its counterpart: the nodes are equivalent, whatever their labels.
  node-∼ : {a b : L} {f : R a → Closed L R} {h : R b → Closed L R}
    (to : R a → R b) (from : R b → R a) →
    ((y : R a) → f y ⊑ h (to y)) →
    ((z : R b) → h z ⊑ f (from z)) →
    Tree.node a f ∼ Tree.node b h
  node-∼ to from p q =
    below (λ y → under (to y) (p y)) , below (λ z → under (from z) (q z))

  -- Two nodes with one label and pointwise equivalent children.
  fan-∼ : {a : L} {f h : R a → Closed L R} →
    ((y : R a) → f y ∼ h y) → Tree.node a f ∼ Tree.node a h
  fan-∼ p =
    below (λ u → under u (pr₁ (p u))) , below (λ u → under u (pr₂ (p u)))

------------------------------------------------------------------------
-- Shape equivalence: isomorphisms of branch types

-- x ≅ y retains, at every node, an isomorphism E of the two branch types
-- and relates the children along E and along its inverse, both from left to
-- right. The second family is stored rather than transported along an
-- inverse law of E.
--
--     E : R a ≅ R b    Π y. f y ≅ h (E y)    Π z. f (E⁻¹ z) ≅ h z
--   ------------------------------------------------------------- branching
--                          node a f ≅ node b h
--
-- Labels are not compared. Nonclaim: ∼ does not imply ≅. A node over 𝟚 and a
-- node over 𝟙, all of whose children are the leaf over 𝟘, are ∼ but have no
-- isomorphism of branch types.

infix 5 _≅_

data _≅_ {ℓ₁ ℓ₂ : Level} {L : Set ℓ₁} {R : L → Set ℓ₂}
  : Closed L R → Closed L R → Set (ℓ₁ ⊔ ℓ₂) where
  branching : {a b : L} {f : R a → Closed L R} {h : R b → Closed L R}
    (E : Isomorphic (R a) (R b)) →
    ((y : R a) → f y ≅ h (forward E y)) →
    ((z : R b) → f (backward E z) ≅ h z) →
    Tree.node a f ≅ Tree.node b h

module _ {ℓa ℓb : Level} {L : Set ℓa} {R : L → Set ℓb} where

  ≅-refl : (x : Closed L R) → x ≅ x
  ≅-refl (Tree.hole ())
  ≅-refl (Tree.node a f) =
    branching isomorphic-refl (λ y → ≅-refl (f y)) (λ y → ≅-refl (f y))

  ≅-sym : {x y : Closed L R} → x ≅ y → y ≅ x
  ≅-sym (branching E p q) =
    branching (isomorphic-sym E) (λ z → ≅-sym (q z)) (λ y → ≅-sym (p y))

  ≅-trans : {x y z : Closed L R} → x ≅ y → y ≅ z → x ≅ z
  ≅-trans (branching E p q) (branching F p′ q′) =
    branching (isomorphic-trans E F)
      (λ y → ≅-trans (p y) (p′ (forward E y)))
      (λ w → ≅-trans (q (backward F w)) (q′ w))

  ≈→≅ : {x y : Closed L R} → x ≈ y → x ≅ y
  ≈→≅ (hole-rel {_} {()} r)
  ≈→≅ (node-rel p) =
    branching isomorphic-refl (λ u → ≈→≅ (p u)) (λ u → ≈→≅ (p u))

  ≅→⊑ : {x y : Closed L R} → x ≅ y → x ⊑ y
  ≅→⊑ (branching E p q) = below (λ y → under (forward E y) (≅→⊑ (p y)))

  ≅→∼ : {x y : Closed L R} → x ≅ y → x ∼ y
  ≅→∼ p = ≅→⊑ p , ≅→⊑ (≅-sym p)
