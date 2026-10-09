{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Height.Simulation where

-- Closed Core trees and their relations, for any labels and branchings:
-- Core's structural equality ≈ (equal labels and related children), Core
-- ancestry ◃ and < (immediate and proper descendants), and the simulation
-- order ⊑ and ⊏ with its equivalence ∼. Ancestry describes how a tree is
-- built; the simulation order compares trees by their branching alone.
-- Both strict relations are well-founded, ancestry lies inside the strict
-- simulation order (<→⊏), and structural equality gives equivalence (≈→∼).
-- The shape equivalence ≅ retains an exact equivalence of branch types at
-- every node; structural equality gives it (≈→≅) and it gives ∼ (≅→∼).
-- The heights of the ordinal of ordinals (Height.Ordinals) are compared
-- in this order; their ranks among Cubical well-orders are in
-- Cubical.Height.Rank.

open import Agda.Primitive using (Level; lzero; _⊔_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (tt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans)
open import Relation.Nullary.Negation using (¬_)

open import SPT.Cubical.Core.WellFounded using
  (Acc; acc; WellFounded; acc↛loop)
open import SPT.Cubical.Core.Equality.Isomorphism using (forward; backward)
  renaming (_≅_ to Isomorphic; ≅-refl to isomorphic-refl;
            ≅-sym to isomorphic-sym; ≅-trans to isomorphic-trans)
open import SPT.Cubical.Core.WellFounded.Pullback using
  (PullbackRel; pullback-wf)
import SPT.Cubical.Core.Generator.Tree as Tree
import SPT.Cubical.Core.Generator.Tree.W as TreeW
open import SPT.Cubical.Core.Generator.Tree.Child using
  (HistoryNode; HistoryChild; node-child; history-child-wf)
open import SPT.Cubical.Core.Generator.Tree.Descendant using
  (Descendant; immediate;
   nested; descendant-trans;
   descendant-wf)
open import SPT.Cubical.Core.Generator.Tree.Relation using
  (TreeRel; hole-rel; node-rel; rel-refl; rel-sym;
   rel-compose)

------------------------------------------------------------------------
-- Structural equality of closed Core trees

-- Core's same-operation relation with identity on the empty hole family:
-- equal operations at every node and related children at every position.
-- It is the identity of trees available without function extensionality.
infix 4 _≈_

_≈_ : ∀ {ℓo ℓp} {S : Tree.Signature lzero ℓo ℓp} {j} →
  Tree.History S j → Tree.History S j → Set (ℓo ⊔ ℓp)
_≈_ = TreeRel _≡_

≈-refl : ∀ {ℓo ℓp} {S : Tree.Signature lzero ℓo ℓp} {j}
  (x : Tree.History S j) → x ≈ x
≈-refl = rel-refl (λ x → refl)

≈-sym : ∀ {ℓo ℓp} {S : Tree.Signature lzero ℓo ℓp} {j}
  {x y : Tree.History S j} → x ≈ y → y ≈ x
≈-sym = rel-sym sym

≈-trans : ∀ {ℓo ℓp} {S : Tree.Signature lzero ℓo ℓp} {j}
  {x y z : Tree.History S j} → x ≈ y → y ≈ z → x ≈ z
≈-trans = rel-compose trans

------------------------------------------------------------------------
-- Branching trees: Core ancestry and the simulation order

-- Closed L R = Tree.W.Branching.Closed L R is the type of closed Core trees
-- whose nodes are labels a : L branching over R a.  Ancestry is Core's
-- HistoryChild and Descendant read at the one judgment; it
-- describes the construction.  Trees are compared by the simulation order
-- ⊑ and ⊏, which sees only branching and never which label produced a
-- node.
--
--     Π y. f y ⊏ t                 x ⊑ h z
--   ---------------- below      ---------------- under z
--     node a f ⊑ t                x ⊏ node b h
--
-- _∼_ is mutual ⊑.  Nonclaim: ⊑ is not total, and ∼ does not imply ≈.

private
  variable
    ℓa ℓb : Level
    Label : Set ℓa
    Branch : Label → Set ℓb

Closed : (L : Set ℓa) → (L → Set ℓb) → Set (ℓa ⊔ ℓb)
Closed L R = TreeW.Branching.Closed L R

total : Closed Label Branch →
  HistoryNode (TreeW.Branching.signature Label Branch)
total x = tt , x

infix 4 _◃_ _<_ _⊑_ _⊏_ _∼_

_◃_ : Closed Label Branch → Closed Label Branch → Set _
_◃_ = PullbackRel total HistoryChild

_<_ : Closed Label Branch → Closed Label Branch → Set _
_<_ = PullbackRel total Descendant

◃-wf : WellFounded (_◃_ {Label = Label} {Branch = Branch})
◃-wf = pullback-wf history-child-wf

<-wf : WellFounded (_<_ {Label = Label} {Branch = Branch})
<-wf = pullback-wf descendant-wf

<-trans : {x y z : Closed Label Branch} → x < y → y < z → x < z
<-trans = descendant-trans

<-irrefl : (x : Closed Label Branch) → ¬ x < x
<-irrefl x = acc↛loop (<-wf x)

-- Every immediate predecessor of a node is one of its literal children;
-- every strict predecessor is a child or lies below one.
◃-spectrum : {a : Label} {f : Branch a → Closed Label Branch}
  {x : Closed Label Branch} →
  x ◃ Tree.node a f → Σ (Branch a) (λ y → x ≡ f y)
◃-spectrum (node-child y) = y , refl

<-spectrum : {a : Label} {f : Branch a → Closed Label Branch}
  {x : Closed Label Branch} →
  x < Tree.node a f → Σ (Branch a) (λ y → x ≡ f y ⊎ x < f y)
<-spectrum (immediate (node-child y)) = y , inj₁ refl
<-spectrum (nested (node-child y) route) =
  y , inj₂ route

mutual
  data _⊑_ {ℓ₁ ℓ₂ : Level} {L : Set ℓ₁} {R : L → Set ℓ₂}
    : Closed L R → Closed L R → Set (ℓ₁ ⊔ ℓ₂) where
    below : {a : L} {f : R a → Closed L R} {t : Closed L R} →
      ((y : R a) → f y ⊏ t) → Tree.node a f ⊑ t

  data _⊏_ {ℓ₁ ℓ₂ : Level} {L : Set ℓ₁} {R : L → Set ℓ₂}
    : Closed L R → Closed L R → Set (ℓ₁ ⊔ ℓ₂) where
    under : {x : Closed L R} {b : L} {h : R b → Closed L R}
      (z : R b) → x ⊑ h z → x ⊏ Tree.node b h

_∼_ : Closed Label Branch → Closed Label Branch → Set _
x ∼ y = x ⊑ y × y ⊑ x

⊑-refl : (x : Closed Label Branch) → x ⊑ x
⊑-refl (Tree.hole ())
⊑-refl (Tree.node a f) = below (λ y → under y (⊑-refl (f y)))

◃→⊏ : {x y : Closed Label Branch} → x ◃ y → x ⊏ y
◃→⊏ (node-child y) = under y (⊑-refl _)

⊏→⊑ : {x y : Closed Label Branch} → x ⊏ y → x ⊑ y
⊏→⊑ (under z (below p)) = below (λ u → under z (⊏→⊑ (p u)))

mutual
  ⊑-trans : {x y z : Closed Label Branch} → x ⊑ y → y ⊑ z → x ⊑ z
  ⊑-trans (below p) y⊑z = below (λ u → ⊏-⊑-trans (p u) y⊑z)

  ⊏-⊑-trans : {x y z : Closed Label Branch} → x ⊏ y → y ⊑ z → x ⊏ z
  ⊏-⊑-trans (under v x⊑hv) (below q) = ⊑-⊏-trans x⊑hv (q v)

  ⊑-⊏-trans : {x y z : Closed Label Branch} → x ⊑ y → y ⊏ z → x ⊏ z
  ⊑-⊏-trans x⊑y (under w y⊑kw) = under w (⊑-trans x⊑y y⊑kw)

⊏-trans : {x y z : Closed Label Branch} → x ⊏ y → y ⊏ z → x ⊏ z
⊏-trans x⊏y y⊏z = ⊑-⊏-trans (⊏→⊑ x⊏y) y⊏z

⊏-wf : WellFounded (_⊏_ {L = Label} {R = Branch})
⊏-wf t = acc (accessible t)
  where
    accessible : (t x : Closed _ _) → x ⊏ t → Acc _⊏_ x
    accessible (Tree.hole ()) x x⊏t
    accessible (Tree.node b h) x (under v x⊑hv) =
      acc λ y y⊏x → accessible (h v) y (⊏-⊑-trans y⊏x x⊑hv)

-- In particular no tree lies below itself, so ⊏ is not degenerate.
⊏-irrefl : (x : Closed Label Branch) → ¬ x ⊏ x
⊏-irrefl x = acc↛loop (⊏-wf x)

<→⊏ : {x y : Closed Label Branch} → x < y → x ⊏ y
<→⊏ (immediate step) = ◃→⊏ step
<→⊏ (nested (node-child y) route) =
  ⊑-⊏-trans (⊏→⊑ (<→⊏ route)) (◃→⊏ (node-child y))

≈→⊑ : {x y : Closed Label Branch} → x ≈ y → x ⊑ y
≈→⊑ (hole-rel {x = ()} r)
≈→⊑ (node-rel p) = below (λ u → under u (≈→⊑ (p u)))

≈→∼ : {x y : Closed Label Branch} → x ≈ y → x ∼ y
≈→∼ p = ≈→⊑ p , ≈→⊑ (≈-sym p)

⊏-respˡ-∼ : {x x′ y : Closed Label Branch} → x ∼ x′ → x ⊏ y → x′ ⊏ y
⊏-respˡ-∼ x∼x′ x⊏y = ⊑-⊏-trans (proj₂ x∼x′) x⊏y

⊏-respʳ-∼ : {x y y′ : Closed Label Branch} → y ∼ y′ → x ⊏ y → x ⊏ y′
⊏-respʳ-∼ y∼y′ x⊏y = ⊏-⊑-trans x⊏y (proj₁ y∼y′)

∼-refl : (x : Closed Label Branch) → x ∼ x
∼-refl x = ⊑-refl x , ⊑-refl x

∼-sym : {x y : Closed Label Branch} → x ∼ y → y ∼ x
∼-sym (p , q) = q , p

∼-trans : {x y z : Closed Label Branch} → x ∼ y → y ∼ z → x ∼ z
∼-trans (p , q) (p′ , q′) = ⊑-trans p p′ , ⊑-trans q′ q

-- Two nodes whose positions correspond in both directions, with each
-- child below its counterpart: the nodes are equivalent, whatever their
-- labels.
node-∼ : {a b : Label} {f : Branch a → Closed Label Branch}
  {h : Branch b → Closed Label Branch}
  (to : Branch a → Branch b) (from : Branch b → Branch a) →
  ((y : Branch a) → f y ⊑ h (to y)) →
  ((z : Branch b) → h z ⊑ f (from z)) →
  Tree.node a f ∼ Tree.node b h
node-∼ to from p q =
  below (λ y → under (to y) (p y)) , below (λ z → under (from z) (q z))

-- Two nodes with one label and pointwise equivalent children.
fan-∼ : {a : Label} {f h : Branch a → Closed Label Branch} →
  ((y : Branch a) → f y ∼ h y) → Tree.node a f ∼ Tree.node a h
fan-∼ p =
  below (λ u → under u (proj₁ (p u))) , below (λ u → under u (proj₂ (p u)))

------------------------------------------------------------------------
-- Shape equivalence: exact equivalences of branch types

-- x ≅ y retains, at every node, an exact equivalence E of the two branch
-- types (Core.Equality.Isomorphism) and relates the children along E and
-- along its inverse, both from left to right.  The second family is stored
-- rather than transported along the inverse law of E.
--
--     E : R a ≃ R b    Π y. f y ≅ h (E y)    Π z. f (E⁻¹ z) ≅ h z
--   ------------------------------------------------------------- branching
--                          node a f ≅ node b h
--
-- Labels are not compared.  Nonclaim: ∼ does not imply ≅.  A node over
-- Bool and a node over ⊤, all of whose children are the leaf over ⊥, are
-- ∼ but have no exact equivalence of branch types.

infix 4 _≅_

data _≅_ {ℓ₁ ℓ₂ : Level} {L : Set ℓ₁} {R : L → Set ℓ₂}
  : Closed L R → Closed L R → Set (ℓ₁ ⊔ ℓ₂) where
  branching : {a b : L} {f : R a → Closed L R} {h : R b → Closed L R}
    (E : Isomorphic (R a) (R b)) →
    ((y : R a) → f y ≅ h (forward E y)) →
    ((z : R b) → f (backward E z) ≅ h z) →
    Tree.node a f ≅ Tree.node b h

≅-refl : (x : Closed Label Branch) → x ≅ x
≅-refl (Tree.hole ())
≅-refl (Tree.node a f) =
  branching isomorphic-refl (λ y → ≅-refl (f y))
    (λ y → ≅-refl (f y))

≅-sym : {x y : Closed Label Branch} → x ≅ y → y ≅ x
≅-sym (branching E p q) =
  branching (isomorphic-sym E) (λ z → ≅-sym (q z))
    (λ y → ≅-sym (p y))

≅-trans : {x y z : Closed Label Branch} → x ≅ y → y ≅ z → x ≅ z
≅-trans (branching E p q) (branching F p′ q′) =
  branching (isomorphic-trans E F)
    (λ y → ≅-trans (p y) (p′ (forward E y)))
    (λ w → ≅-trans (q (backward F w)) (q′ w))

≈→≅ : {x y : Closed Label Branch} → x ≈ y → x ≅ y
≈→≅ (hole-rel {x = ()} r)
≈→≅ (node-rel p) =
  branching isomorphic-refl (λ u → ≈→≅ (p u)) (λ u → ≈→≅ (p u))

≅→⊑ : {x y : Closed Label Branch} → x ≅ y → x ⊑ y
≅→⊑ (branching E p q) = below (λ y → under (forward E y) (≅→⊑ (p y)))

≅→∼ : {x y : Closed Label Branch} → x ≅ y → x ∼ y
≅→∼ p = ≅→⊑ p , ≅→⊑ (≅-sym p)
