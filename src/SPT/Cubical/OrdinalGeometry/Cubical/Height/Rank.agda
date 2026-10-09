{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Height.Rank where

-- The rank of a height among the Cubical well-orders of its level:
--
--   rank (node A f) = sup (a : A). rank (f a) + 1   (Supremum.Family).
--
-- A child's rank lies strictly below its parent's (child), and the rank of
-- a node lies below every well-order, of any level, strictly above the
-- ranks of its children (least).  Every well-order W is the rank of its
-- canonical height, Height.Ordinals.whole of its relation (canonical), and
-- a height and its lift one universe up have equivalent ranks (lifted).
-- Shape-equivalent heights have equivalent ranks (rank-≅).  Each
-- equivalence is antisymmetry of ≼: one side from least, the other from
-- a simulation built on principal segments, or from least again.

open import Agda.Primitive using (Level; lsuc)
open import Level using (Lift; lift; lower)

import Cubical.Foundations.Prelude as Cubical
import Cubical.Induction.WellFounded as CubicalAccessibility
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

import SPT.Cubical.Core.Generator.Tree as Tree
open import SPT.Cubical.Core.WellFounded using (Acc; acc; WellFounded)
open import SPT.Cubical.Core.Equality.Isomorphism using (forward; backward)
open import SPT.Cubical.OrdinalGeometry.Height.Simulation using
  (_≅_; branching)
import SPT.Cubical.OrdinalGeometry.Height.Ordinals as Heights
open Heights using (Height; lift-height)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Ordinals using
  (successor; segments→simulation)
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Supremum.Family
  as Family

private
  variable
    ℓ c d : Level

------------------------------------------------------------------------
-- The rank

-- Mathematical shape: rank (node A f) = sup (a : A). rank (f a) + 1.
rank : Height ℓ → Woset.Woset ℓ ℓ
rank (Tree.hole ())
rank (Tree.node A f) = Family.supremum λ a → successor (rank (f a))

-- Mathematical shape: rank (f a) ≺ rank (node A f).
child : (A : Set ℓ) (f : A → Height ℓ) (a : A)
  → Simulation._≺_ (rank (f a)) (rank (Tree.node A f))
child A f = Family.strict-upper λ a → rank (f a)

-- Mathematical shape: (∀ a. rank (f a) ≺ B) → rank (node A f) ≼ B.
least : (A : Set ℓ) (f : A → Height ℓ) (B : Woset.Woset c d)
  → ((a : A) → Simulation._≺_ (rank (f a)) B)
  → Simulation._≼_ (rank (Tree.node A f)) B
least A f = Family.strict-least λ a → rank (f a)

private
  -- A node over the points of V whose children have the ranks of the
  -- principal segments of V has rank V.
  segments : (V : Woset.Woset ℓ ℓ) (f : Cubical.fst V → Height ℓ)
    → ((v : Cubical.fst V) →
        Woset.WosetEquiv (rank (f v)) (Simulation._↓_ V v))
    → Woset.WosetEquiv (rank (Tree.node (Cubical.fst V) f)) V
  segments V f e =
    Simulation.isAntisym≼Equiv (rank (Tree.node (Cubical.fst V) f)) V
      (least (Cubical.fst V) f V λ v →
        Simulation.≺RespectsEquivL V (Woset.invWosetEquiv (e v))
          (Simulation.↓Decreasing V v))
      (segments→simulation
        {H = V} {K = rank (Tree.node (Cubical.fst V) f)}
        λ v →
          Simulation.≺RespectsEquivL (rank (Tree.node (Cubical.fst V) f))
            (e v) (child (Cubical.fst V) f v))


------------------------------------------------------------------------
-- Canonical heights and lifts

-- Cubical accessibility gives accessibility in the sense of Core.
accessible : {A : Set ℓ} {_<_ : A → A → Set ℓ} {x : A}
  → CubicalAccessibility.Acc _<_ x → Acc _<_ x
accessible (CubicalAccessibility.acc smaller) =
  acc λ y p → accessible (smaller y p)

well-founded : (W : Woset.Woset ℓ ℓ)
  → WellFounded (Woset.WosetStr._≺_ (Cubical.snd W))
well-founded W x =
  accessible
    (Woset.IsWoset.is-well-founded
      (Woset.WosetStr.isWoset (Cubical.snd W)) x)

-- The canonical height of a well-order: Height.Ordinals.whole of its
-- relation.
canonical-height : Woset.Woset ℓ ℓ → Height ℓ
canonical-height W =
  Heights.whole (Woset.WosetStr._≺_ (Cubical.snd W)) (well-founded W)

-- Mathematical shape: rank (canonical-height W) ≃ W.  The child at x is
-- the canonical height of W ↓ x, by induction on accessibility.
canonical : (W : Woset.Woset ℓ ℓ)
  → Woset.WosetEquiv (rank (canonical-height W)) W
canonical W =
  segments W (Heights.rank _<_ (well-founded W))
    λ x → at x (well-founded W x)
  where
    _<_ = Woset.WosetStr._≺_ (Cubical.snd W)

    at : (x : Cubical.fst W) (accessibility : Acc _<_ x)
      → Woset.WosetEquiv (rank (Heights.rankAt _<_ x accessibility))
          (Simulation._↓_ W x)
    at x (acc smaller) =
      segments (Simulation._↓_ W x)
        (λ p →
          Heights.rankAt _<_ (Cubical.fst p)
            (smaller (Cubical.fst p) (Cubical.snd p)))
        λ p →
          Woset.compWosetEquiv
            (at (Cubical.fst p) (smaller (Cubical.fst p) (Cubical.snd p)))
            (Woset.invWosetEquiv
              (Simulation.↓AbsorbEquiv W x (Cubical.fst p) (Cubical.snd p)))

-- Mathematical shape: rank t ≃ rank (lift t), one universe level up.
lifted : (t : Height ℓ) → Woset.WosetEquiv (rank t) (rank (lift-height t))
lifted (Tree.hole ())
lifted {ℓ} (Tree.node A f) =
  Simulation.isAntisym≼Equiv (rank (Tree.node A f))
    (rank (lift-height (Tree.node A f)))
    (least A f (rank (lift-height (Tree.node A f))) λ a →
      Simulation.≺RespectsEquivL (rank (lift-height (Tree.node A f)))
        (Woset.invWosetEquiv (lifted (f a)))
        (child (Lift (lsuc ℓ) A) (λ b → lift-height (f (lower b))) (lift a)))
    (least (Lift (lsuc ℓ) A) (λ b → lift-height (f (lower b)))
      (rank (Tree.node A f)) λ b →
        Simulation.≺RespectsEquivL (rank (Tree.node A f))
          (lifted (f (lower b))) (child A f (lower b)))

------------------------------------------------------------------------
-- Shape equivalence

-- Mathematical shape: x ≅ y → rank x ≃ rank y.  Each child of either
-- node has the rank of a child of the other, by the retained
-- equivalence of branch types, so least applies both ways.
rank-≅ : {x y : Height ℓ} → x ≅ y
  → Woset.WosetEquiv (rank x) (rank y)
rank-≅ (branching {a = A} {b = B} {f = f} {h = h} E p q) =
  Simulation.isAntisym≼Equiv (rank (Tree.node A f)) (rank (Tree.node B h))
    (least A f (rank (Tree.node B h)) λ y →
      Simulation.≺RespectsEquivL (rank (Tree.node B h))
        (Woset.invWosetEquiv (rank-≅ (p y))) (child B h (forward E y)))
    (least B h (rank (Tree.node A f)) λ z →
      Simulation.≺RespectsEquivL (rank (Tree.node A f))
        (rank-≅ (q z)) (child A f (backward E z)))
