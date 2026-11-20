{-# OPTIONS --safe --without-K #-}

module SPT.OrdinalGeometry.Height.Hartogs where

-- The Hartogs boundary of every code, for a parent with a classifier
-- (Foundation.Impredicative.Classification) and its formers decoded up to
-- retraction.
-- The classifier makes the subsets of a decoding D a a decoding: the code
-- `subsets a` chooses a proxy at each point of D a, and a subset s branches
-- over the code of its members (`members`). The trees of this family are
-- the subset trees of a, and their boundary is the Hartogs boundary H(a),
-- a parent tree (`hartogs`). Every well-founded code-valued relation on
-- D a has strictly monotone ranks among the subset trees (`rank-strict`),
-- so its height lies strictly below H(a) (`founded-below`), and H(a) is the
-- height of no such relation (`not-height`). Conversely, code-level subsets
-- of every decoding, retaining every code-valued predicate, give a
-- classifier (`classifying`): the positions of the Hartogs boundaries are
-- code-level exactly when the parent has a classifier. The ℕ-branching
-- trees embed as subset trees of ℕ (`naturals-below`):
--
--   Π B : Founded a. height B ⊏ H(a),   Ω_ℕ ⊑ H(ℕ).
--
-- Nonclaim: H(a) is not shown to be least among bounds of the heights. It
-- is no stage or boundary of an analysis from below: subset trees have no
-- enumeration and no decidable comparison, and the boundary of the
-- presentations is Ordinal Geometry's presented ω₁.

open import SPT.Base
open import SPT.Foundation.Accessibility using
  (is-accessible; acc; is-well-founded)
open import SPT.Foundation.Impredicative.Classification using
  (Classifier; chosen; encode; decode)
import SPT.Foundation.Tree as Tree
open import SPT.Mahlo.Specification using (Family; Formers)
open import SPT.Foundation.Tree.W using (sup)
open import SPT.Mahlo.Retraction using
  (Retracts; out; into; out-into; choose)
open import SPT.OrdinalGeometry.Height.Simulation using
  (Closed; _⊑_; _⊏_; below; under; ⊑-⊏-trans; ⊏-irrefl)
open import SPT.OrdinalGeometry.Height.Reflection using
  (Unfolds; Trees; embed; unfold; boundary; embed-below)

------------------------------------------------------------------------
-- Code-level power presentations

-- Mathematical shape: for every code a, a code of subsets of D a, a
-- membership code, and retention of every code-valued predicate on D a up
-- to pointwise logical equivalence.
record Powers {κ ℓ : Level} {C : Set κ} (D : C → Set ℓ) : Set (κ ⊔ ℓ) where
  field
    subsets : C → C
    member : (a : C) → D (subsets a) → D a → C
    retain : (a : C) → (D a → C) → D (subsets a)
    recover : (a : C) (X : D a → C) (x : D a) →
      (D (X x) → D (member a (retain a X) x)) ×
      (D (member a (retain a X) x) → D (X x))

-- Code-level subsets of the unit code classify: a code c is retained as
-- the constant predicate, and its proxy is membership of the one point.
classifying : {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D} →
  Retracts Q → Powers D → Classifier D
classifying {Q = Q} retracts powers = record
  { proxies = Powers.subsets powers (Formers.unit Q)
  ; proxy = λ s →
      Powers.member powers (Formers.unit Q) s (Retracts.point retracts)
  ; classify = λ c →
      Powers.retain powers (Formers.unit Q) (λ u → c) ,
      Powers.recover powers (Formers.unit Q) (λ u → c)
        (Retracts.point retracts)
  }

------------------------------------------------------------------------
-- Subsets from a classifier

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D}
  (retracts : Retracts Q) (classifier : Classifier D)
  where

  -- Mathematical shape: subsets a = Π (x : a). proxies.
  subsets : C → C
  subsets a = Formers.product Q (a , λ x → Classifier.proxies classifier)

  -- The proxy that the subset s chooses at x.
  at : (a : C) → D (subsets a) → D a → D (Classifier.proxies classifier)
  at a s =
    out (Retracts.product retracts a (λ x → Classifier.proxies classifier)) s

  -- The subset retaining a code-valued predicate.
  retain : (a : C) → (D a → C) → D (subsets a)
  retain a X =
    into (Retracts.product retracts a (λ x → Classifier.proxies classifier))
      (λ x → chosen classifier (X x))

  at-retain : (a : C) (X : D a → C) (x : D a) →
    at a (retain a X) x ＝ chosen classifier (X x)
  at-retain a X x =
    ap (λ f → f x)
      (out-into
        (Retracts.product retracts a (λ y → Classifier.proxies classifier))
        (λ y → chosen classifier (X y)))

  -- Mathematical shape: members a s = Σ (x : a). proxy (at a s x).
  members : (a : C) → D (subsets a) → C
  members a s =
    Formers.sum Q (a , λ x → Classifier.proxy classifier (at a s x))

  -- The point of D a that a member is.
  point : (a : C) (s : D (subsets a)) → D (members a s) → D a
  point a s m =
    pr₁
      (out
        (Retracts.sum retracts a
          (λ x → Classifier.proxy classifier (at a s x)))
        m)

  -- A member of a retained subset satisfies the predicate.
  recover : (a : C) (X : D a → C) (m : D (members a (retain a X))) →
    D (X (point a (retain a X) m))
  recover a X m =
    decode classifier (X (point a (retain a X) m))
      (transport (λ j → D (Classifier.proxy classifier j))
        (at-retain a X (point a (retain a X) m))
        (pr₂
          (out
            (Retracts.sum retracts a
              (λ x → Classifier.proxy classifier (at a (retain a X) x)))
            m)))

  -- A point satisfying the predicate is a member of the retained subset.
  enter : (a : C) (X : D a → C) (x : D a) → D (X x) →
    D (members a (retain a X))
  enter a X x p =
    into
      (Retracts.sum retracts a
        (λ y → Classifier.proxy classifier (at a (retain a X) y)))
      (x ,
       transport (λ j → D (Classifier.proxy classifier j))
         (at-retain a X x ⁻¹) (encode classifier (X x) p))

  point-enter : (a : C) (X : D a → C) (x : D a) (p : D (X x)) →
    point a (retain a X) (enter a X x p) ＝ x
  point-enter a X x p =
    ap pr₁
      (out-into
        (Retracts.sum retracts a
          (λ y → Classifier.proxy classifier (at a (retain a X) y)))
        (x ,
         transport (λ j → D (Classifier.proxy classifier j))
           (at-retain a X x ⁻¹) (encode classifier (X x) p)))

  -- The classifier gives code-level power presentations.
  powers : Powers D
  powers = record
    { subsets = subsets
    ; member = λ a s x → Classifier.proxy classifier (at a s x)
    ; retain = retain
    ; recover = λ a X x →
        (λ p →
          transport (λ j → D (Classifier.proxy classifier j))
            (at-retain a X x ⁻¹) (encode classifier (X x) p)) ,
        (λ q →
          decode classifier (X x)
            (transport (λ j → D (Classifier.proxy classifier j))
              (at-retain a X x) q))
    }

  -- The family of the subsets of D a, branching over their members.
  power : C → Family D
  power a = subsets a , members a

  -- The full subset of D a, retaining the unit code.
  full : (a : C) → D (subsets a)
  full a = retain a (λ x → Formers.unit Q)

------------------------------------------------------------------------
-- Well-founded code-valued relations

-- A well-founded code-valued relation on D a.
record Founded {κ ℓ : Level} {C : Set κ} (D : C → Set ℓ) (a : C)
  : Set (κ ⊔ ℓ) where
  field
    relation : D a → D a → C
    wf : is-well-founded (λ y x → D (relation y x))

-- The order a founded relation decodes to.
founded-order : {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {a : C} →
  Founded D a → D a → D a → Set ℓ
founded-order {D = D} B y x = D (Founded.relation B y x)

infix 30 founded-order
syntax founded-order B y x = y ≺⟨ B ⟩ x

------------------------------------------------------------------------
-- The Hartogs boundary and the ranks below it

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D}
  (unfolds : Unfolds Q) (retracts : Retracts Q) (classifier : Classifier D)
  where

  -- Mathematical shape: H(a) = Ω_{power a}, the node at the tree code of
  -- power a whose positions are the subset trees of a.
  hartogs : C → Closed C D
  hartogs a = boundary unfolds (power retracts classifier a)

  -- Every subset tree of a lies below H(a).
  subset-below : (a : C) (w : Trees unfolds (power retracts classifier a)) →
    embed unfolds (power retracts classifier a) w ⊏ hartogs a
  subset-below a = embed-below unfolds (power retracts classifier a)

  module _ {a : C} (B : Founded D a) where

    -- The predecessors of x under B, as a subset of D a.
    predecessors : D a → D (subsets retracts classifier a)
    predecessors x =
      retain retracts classifier a (λ y → Founded.relation B y x)

    -- Mathematical shape: rank x = node (predecessors x) (λ m. rank m), by
    -- recursion on the accessibility of x.
    rank-at : (x : D a) → is-accessible (founded-order B) x →
      Trees unfolds (power retracts classifier a)
    rank-at x (acc smaller) =
      sup (predecessors x)
        (λ m →
          rank-at (point retracts classifier a (predecessors x) m)
            (smaller (point retracts classifier a (predecessors x) m)
              (recover retracts classifier a
                (λ y → Founded.relation B y x) m)))

    rank : D a → Trees unfolds (power retracts classifier a)
    rank x = rank-at x (Founded.wf B x)

    -- Ranks do not depend on the accessibility witness.
    rank-⊑ : (x : D a) (p q : is-accessible (founded-order B) x) →
      embed unfolds (power retracts classifier a) (rank-at x p)
      ⊑ embed unfolds (power retracts classifier a) (rank-at x q)
    rank-⊑ x (acc s) (acc s′) =
      below (λ m →
        under m
          (rank-⊑ (point retracts classifier a (predecessors x) m)
            (s (point retracts classifier a (predecessors x) m)
              (recover retracts classifier a
                (λ y → Founded.relation B y x) m))
            (s′ (point retracts classifier a (predecessors x) m)
              (recover retracts classifier a
                (λ y → Founded.relation B y x) m))))

    -- Ranks at identified points.
    rank-moved : (y z : D a) → z ＝ y →
      (p : is-accessible (founded-order B) y)
      (q : is-accessible (founded-order B) z) →
      embed unfolds (power retracts classifier a) (rank-at y p)
      ⊑ embed unfolds (power retracts classifier a) (rank-at z q)
    rank-moved y .y refl p q = rank-⊑ y p q

    -- Mathematical shape: y ≺ x ⟹ rank y ⊏ rank x.
    rank-strict : (y x : D a) → y ≺⟨ B ⟩ x →
      (p : is-accessible (founded-order B) y)
      (q : is-accessible (founded-order B) x) →
      embed unfolds (power retracts classifier a) (rank-at y p)
      ⊏ embed unfolds (power retracts classifier a) (rank-at x q)
    rank-strict y x y≺x p (acc smaller) =
      under
        (enter retracts classifier a (λ z → Founded.relation B z x) y y≺x)
        (rank-moved y
          (point retracts classifier a
            (retain retracts classifier a (λ z → Founded.relation B z x))
            (enter retracts classifier a (λ z → Founded.relation B z x) y
              y≺x))
          (point-enter retracts classifier a (λ z → Founded.relation B z x)
            y y≺x)
          p
          (smaller
            (point retracts classifier a
              (retain retracts classifier a (λ z → Founded.relation B z x))
              (enter retracts classifier a (λ z → Founded.relation B z x) y
                y≺x))
            (recover retracts classifier a (λ z → Founded.relation B z x)
              (enter retracts classifier a (λ z → Founded.relation B z x) y
                y≺x))))

    -- The height of B: a node at the full subset over the ranks of all
    -- points.
    height : Trees unfolds (power retracts classifier a)
    height =
      sup (full retracts classifier a)
        (λ m →
          rank (point retracts classifier a (full retracts classifier a) m))

    -- Mathematical shape: height B ⊏ H(a).
    founded-below :
      embed unfolds (power retracts classifier a) height ⊏ hartogs a
    founded-below = subset-below a height

    -- H(a) is the height of no well-founded relation on D a.
    not-height :
      ¬ (hartogs a ⊑ embed unfolds (power retracts classifier a) height)
    not-height h = ⊏-irrefl (hartogs a) (⊑-⊏-trans h founded-below)

------------------------------------------------------------------------
-- ℕ-branching trees as subset trees of ℕ

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D}
  (retracts : Retracts Q)
  where

  -- The parent family with a leaf at the empty code and ℕ-branching at the
  -- natural code, read through the two code.
  naturals : Family D
  naturals =
    Formers.two Q ,
    (λ b →
      choose (out (Retracts.two retracts) b) (Formers.empty Q)
        (Formers.natural Q))

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D}
  (unfolds : Unfolds Q) (retracts : Retracts Q) (classifier : Classifier D)
  where

  -- A leaf goes to the empty subset of ℕ, an ℕ-node to the full subset with
  -- the same children.
  simulated-node : (k : 𝟚) →
    (D (choose k (Formers.empty Q) (Formers.natural Q)) →
      Trees unfolds (power retracts classifier (Formers.natural Q))) →
    Trees unfolds (power retracts classifier (Formers.natural Q))
  simulated-node ₀ g =
    sup (retain retracts classifier (Formers.natural Q) (λ x → Formers.empty Q))
      (λ m →
        𝟘-elim
          (Retracts.empty retracts
            (recover retracts classifier (Formers.natural Q)
              (λ x → Formers.empty Q) m)))
  simulated-node ₁ g =
    sup (full retracts classifier (Formers.natural Q))
      (λ m →
        g (point retracts classifier (Formers.natural Q)
             (full retracts classifier (Formers.natural Q)) m))

  simulate : Trees unfolds (naturals retracts) →
    Trees unfolds (power retracts classifier (Formers.natural Q))
  simulate (sup b f) =
    simulated-node (out (Retracts.two retracts) b) (λ y → simulate (f y))

  simulated-node-⊒ : (k : 𝟚)
    (h : D (choose k (Formers.empty Q) (Formers.natural Q)) → Closed C D)
    (g : D (choose k (Formers.empty Q) (Formers.natural Q)) →
      Trees unfolds (power retracts classifier (Formers.natural Q))) →
    ((y : D (choose k (Formers.empty Q) (Formers.natural Q))) →
      h y ⊑
        embed unfolds (power retracts classifier (Formers.natural Q)) (g y)) →
    Tree.node (choose k (Formers.empty Q) (Formers.natural Q)) h
    ⊑ embed unfolds (power retracts classifier (Formers.natural Q))
        (simulated-node k g)
  simulated-node-⊒ ₀ h g h⊑ =
    below (λ y → 𝟘-elim (Retracts.empty retracts y))
  simulated-node-⊒ ₁ h g h⊑ =
    below (λ n →
      under
        (enter retracts classifier (Formers.natural Q) (λ x → Formers.unit Q)
          n (Retracts.point retracts))
        (transport
          (λ x →
            h n ⊑
              embed unfolds (power retracts classifier (Formers.natural Q))
                (g x))
          (point-enter retracts classifier (Formers.natural Q)
            (λ x → Formers.unit Q) n (Retracts.point retracts) ⁻¹)
          (h⊑ n)))

  simulates : (w : Trees unfolds (naturals retracts)) →
    embed unfolds (naturals retracts) w
    ⊑ embed unfolds (power retracts classifier (Formers.natural Q))
        (simulate w)
  simulates (sup b f) =
    simulated-node-⊒ (out (Retracts.two retracts) b)
      (λ y → embed unfolds (naturals retracts) (f y))
      (λ y → simulate (f y)) (λ y → simulates (f y))

  -- Mathematical shape: Ω_ℕ ⊑ H(ℕ). Every ℕ-branching tree is simulated by
  -- a subset tree of ℕ.
  naturals-below :
    boundary unfolds (naturals retracts)
    ⊑ hartogs unfolds retracts classifier (Formers.natural Q)
  naturals-below =
    below (λ q →
      ⊑-⊏-trans (simulates (unfold unfolds (naturals retracts) q))
        (subset-below unfolds retracts classifier (Formers.natural Q)
          (simulate (unfold unfolds (naturals retracts) q))))
