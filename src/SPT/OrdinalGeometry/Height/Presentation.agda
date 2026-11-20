{-# OPTIONS --safe --without-K #-}

module SPT.OrdinalGeometry.Height.Presentation where

-- The heights of presented ordinals: Height.Ordinals' ranks at a
-- presentation's own order and well-foundedness. The rank of P has the
-- ranks of its points as children (`whole-spectrum`, `whole-child`, and
-- `rank-at-spectrum` below a point). Equivalent points have ranks below
-- each other, smaller points smaller ranks (`rank-at-equivalent`,
-- `rank-at-strict`), and ∂x has the rank of x (`nested`, `von-neumann`).
-- Monotone maps raise ranks (`rank-at-map`, `whole-map`), P ≺𝒫 Q puts
-- rank P below its ceiling's rank (`whole-ceiling`, `whole-bound`), and
-- extensionality gives `rank-at-unique`.

open import SPT.Base
open import SPT.Foundation.Accessibility using (is-accessible; acc)
import SPT.Foundation.Tree.W as TreeW
open import SPT.Foundation.Tree.Child using (node-child)
open import SPT.Foundation.Tree.Relation using
  (ChildΠExt; module Extensional)
open import SPT.OrdinalGeometry.Height.Ordinals using
  (Height; rank-at; rank-at-≈; rank; whole)
open import SPT.OrdinalGeometry.Height.Simulation using
  ( _◃_; _⊑_; _⊏_; _∼_; below; under; ◃-spectrum; ≈→⊑; ⊑-⊏-trans
  ; fan-∼ )
  renaming (_≈_ to infix 6 _≈ᵗ_)
import SPT.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (Countable-Ordinal𝒫 to 𝒫)
import SPT.OrdinalGeometry.Presentation.Map as Maps
open import SPT.OrdinalGeometry.Presentation.Sum using (∂)

------------------------------------------------------------------------
-- Ranks of points and of presentations

-- The rank of a point x is rank-at _<_ x a, the node over the points
-- below x whose children are their ranks, for any accessibility witness a;
-- two witnesses give structurally equal ranks (Height.Ordinals'
-- rank-at-≈). The rank of P is whole _<_ <-wf, the node over the points of
-- P at the witnesses P keeps. Its children are exactly the ranks of the
-- points; the children of a point's rank are, up to ≈, the ranks of the
-- points below it. Equivalent points have the same predecessors, so their
-- ranks lie below each other; a point below y is a branch of the rank of
-- y.

module _ {ℓ : Level} (P : 𝒫 ℓ) where

  open Presented.Countable-Ordinal𝒫 P using (X; _<_; <-wf)

  -- z ◃ whole P → Σ x. z ＝ rank x.
  whole-spectrum : {z : Height ℓ} → z ◃ whole _<_ <-wf →
    Σ X (λ x → z ＝ rank _<_ <-wf x)
  whole-spectrum step = ◃-spectrum step

  -- Every point's rank is a child of the rank of P.
  whole-child : (x : X) → rank _<_ <-wf x ◃ whole _<_ <-wf
  whole-child x = node-child x

  -- z ◃ rank-at x a → Σ y. y < x × z ≈ rank y.
  rank-at-spectrum : (x : X) (a : is-accessible _<_ x) {z : Height ℓ} →
    z ◃ rank-at _<_ x a → Σ X (λ y → (y < x) × (z ≈ᵗ rank _<_ <-wf y))
  rank-at-spectrum x (acc s) (node-child (y , p)) =
    y , p , rank-at-≈ _<_ y (s y p) (<-wf y)

  -- x ≈ y → rank-at x a ⊑ rank-at y b.
  rank-at-equivalent : (x y : X) → 𝒫._≈_ P x y →
    (a : is-accessible _<_ x) (b : is-accessible _<_ y) →
    rank-at _<_ x a ⊑ rank-at _<_ y b
  rank-at-equivalent x y e (acc s) (acc s′) =
    below (λ v →
      under (pr₁ v , 𝒫.<-respʳ-≈ P e (pr₂ v))
        (≈→⊑
          (rank-at-≈ _<_ (pr₁ v) (s (pr₁ v) (pr₂ v))
            (s′ (pr₁ v) (𝒫.<-respʳ-≈ P e (pr₂ v))))))

  -- x < y → rank-at x a ⊏ rank-at y b.
  rank-at-strict : (x y : X) → x < y → (a : is-accessible _<_ x)
    (b : is-accessible _<_ y) → rank-at _<_ x a ⊏ rank-at _<_ y b
  rank-at-strict x y p a (acc s) =
    under (x , p) (≈→⊑ (rank-at-≈ _<_ x a (s x p)))

------------------------------------------------------------------------
-- The von Neumann law

-- The cone ∂x has the points (y , p) with p : y < x, ordered as in P. The
-- rank of (y , p) in ∂x and the rank of y in P branch over the same points,
-- (z , q) below (y , p) against z below y, so they lie below each other by
-- recursion (`nested`). The rank of the whole cone is then the node over
-- the points below x, which is the rank of x (`von-neumann`). The two nodes
-- have different labels, so the agreement is ∼, not ≈.

module _ {ℓ : Level} (P : 𝒫 ℓ) where

  open Presented.Countable-Ordinal𝒫 P using (X; _<_; <-trans)

  mutual
    -- The rank of (y , p) in ∂x lies below the rank of y in P.
    nested-⊑ : (x y : X) (p : y < x)
      (a : is-accessible (𝒫._<_ (∂ P x)) (y , p))
      (b : is-accessible _<_ y) →
      rank-at (𝒫._<_ (∂ P x)) (y , p) a ⊑ rank-at _<_ y b
    nested-⊑ x y p (acc s) (acc s′) =
      below (λ w →
        under (pr₁ (pr₁ w) , pr₂ w)
          (nested-⊑ x (pr₁ (pr₁ w)) (pr₂ (pr₁ w)) (s (pr₁ w) (pr₂ w))
            (s′ (pr₁ (pr₁ w)) (pr₂ w))))

    -- The rank of y in P lies below the rank of (y , p) in ∂x.
    nested-⊒ : (x y : X) (p : y < x)
      (a : is-accessible (𝒫._<_ (∂ P x)) (y , p))
      (b : is-accessible _<_ y) →
      rank-at _<_ y b ⊑ rank-at (𝒫._<_ (∂ P x)) (y , p) a
    nested-⊒ x y p (acc s) (acc s′) =
      below (λ v →
        under ((pr₁ v , <-trans (pr₂ v) p) , pr₂ v)
          (nested-⊒ x (pr₁ v) (<-trans (pr₂ v) p)
            (s (pr₁ v , <-trans (pr₂ v) p) (pr₂ v)) (s′ (pr₁ v) (pr₂ v))))

  -- The rank of (y , p) in ∂x ∼ the rank of y in P.
  nested : (x y : X) (p : y < x)
    (a : is-accessible (𝒫._<_ (∂ P x)) (y , p)) (b : is-accessible _<_ y) →
    rank-at (𝒫._<_ (∂ P x)) (y , p) a ∼ rank-at _<_ y b
  nested x y p a b = nested-⊑ x y p a b , nested-⊒ x y p a b

  -- rank (∂x) ∼ rank x.
  von-neumann : (x : X) (a : is-accessible _<_ x) →
    whole (𝒫._<_ (∂ P x)) (𝒫.<-wf (∂ P x)) ∼ rank-at _<_ x a
  von-neumann x (acc s) =
    fan-∼ (λ w →
      nested x (pr₁ w) (pr₂ w) (𝒫.<-wf (∂ P x) w) (s (pr₁ w) (pr₂ w)))

------------------------------------------------------------------------
-- Ranks along maps

-- A strictly monotone map f sends each point below x to a point below f x,
-- so the rank of x lies below the rank of f x, branch by branch
-- (`rank-at-map`). An order embedding therefore puts the rank of P below
-- the rank of Q (`whole-map`). A strict upper bound P ≺𝒫 Q places every
-- image below its ceiling c, so the rank of P lies below the rank of c
-- (`whole-ceiling`), a child of the rank of Q (`whole-bound`).

module _ {ℓ : Level} (P Q : 𝒫 ℓ) where

  -- f strictly monotone → rank-at x a ⊑ rank-at (f x) b.
  rank-at-map : (f : 𝒫.X P → 𝒫.X Q) →
    ({x y : 𝒫.X P} → 𝒫._<_ P x y → 𝒫._<_ Q (f x) (f y)) →
    (x : 𝒫.X P) (a : is-accessible (𝒫._<_ P) x)
    (b : is-accessible (𝒫._<_ Q) (f x)) →
    rank-at (𝒫._<_ P) x a ⊑ rank-at (𝒫._<_ Q) (f x) b
  rank-at-map f monotone x (acc s) (acc s′) =
    below (λ v →
      under (f (pr₁ v) , monotone (pr₂ v))
        (rank-at-map f monotone (pr₁ v) (s (pr₁ v) (pr₂ v))
          (s′ (f (pr₁ v)) (monotone (pr₂ v)))))

  -- P ↪ Q → rank P ⊑ rank Q.
  whole-map : Maps.Embedding P Q →
    whole (𝒫._<_ P) (𝒫.<-wf P) ⊑ whole (𝒫._<_ Q) (𝒫.<-wf Q)
  whole-map e =
    below (λ x →
      under (Maps.Embedding.map e x)
        (rank-at-map (Maps.Embedding.map e) (Maps.Embedding.strict e) x
          (𝒫.<-wf P x) (𝒫.<-wf Q (Maps.Embedding.map e x))))

  -- P ≺𝒫 Q with ceiling c → rank P ⊑ rank c.
  whole-ceiling : (e : P Presented.≺𝒫 Q) →
    whole (𝒫._<_ P) (𝒫.<-wf P) ⊑
      rank (𝒫._<_ Q) (𝒫.<-wf Q) (Presented._≺𝒫_.ceiling e)
  whole-ceiling e =
    below (λ x →
      ⊑-⊏-trans
        (rank-at-map (Presented._≺𝒫_.to e) (Presented._≺𝒫_.to-< e) x
          (𝒫.<-wf P x) (𝒫.<-wf Q (Presented._≺𝒫_.to e x)))
        (rank-at-strict Q (Presented._≺𝒫_.to e x)
          (Presented._≺𝒫_.ceiling e) (Presented._≺𝒫_.below e x)
          (𝒫.<-wf Q (Presented._≺𝒫_.to e x))
          (𝒫.<-wf Q (Presented._≺𝒫_.ceiling e))))

  -- P ≺𝒫 Q → rank P ⊏ rank Q, under the ceiling.
  whole-bound : P Presented.≺𝒫 Q →
    whole (𝒫._<_ P) (𝒫.<-wf P) ⊏ whole (𝒫._<_ Q) (𝒫.<-wf Q)
  whole-bound e = under (Presented._≺𝒫_.ceiling e) (whole-ceiling e)

------------------------------------------------------------------------
-- Ranks up to identity

-- Structural equality of heights is identity under extensionality for the
-- child families of nodes (`ChildΠExt`, a hypothesis here, used through
-- `Extensional.equality`). So the rank of a point is, up to ＝,
-- independent of its accessibility witness.

module _ {ℓ : Level} (P : 𝒫 ℓ)
  (extensionality :
    ChildΠExt (TreeW.Branching.signature (Set ℓ) (λ A → A)) (λ _ → 𝟘))
  where

  open Presented.Countable-Ordinal𝒫 P using (X; _<_)

  -- rank-at x a ＝ rank-at x b.
  rank-at-unique : (x : X) (a b : is-accessible _<_ x) →
    rank-at _<_ x a ＝ rank-at _<_ x b
  rank-at-unique x a b =
    Extensional.equality extensionality (rank-at _<_ x a) (rank-at _<_ x b)
      (rank-at-≈ _<_ x a b)
