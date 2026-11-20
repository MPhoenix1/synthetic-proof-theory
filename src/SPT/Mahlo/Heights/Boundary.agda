{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Heights.Boundary where

-- Heights of derivations against the boundary of a reflection. The parent's
-- tree codes unfold and its formers decode up to retraction; R reflects Ψ,
-- and its boundary Ω (OrdinalGeometry.Height.Reflection) is read as a
-- height (Height.Ordinals.decoded). Ω is where the derivations from the
-- child's own names close. A derivation by the formers and Ψ from seeds the
-- child names lies below a child tree built rule by rule: the leaf at a
-- constant former, a successor at an identity, and at a family rule the
-- fork between the index premise's tree and the spread of the members'
-- trees over the index's name (`forked`, `gathered`, `bounded`). So it lies
-- strictly below Ω (`below-boundary`), and no derivation reaches Ω
-- (`excluded`). The least height above the derivations from no seeds
-- (Heights.Least.closure-height) lies below the boundary of every
-- reflection of Ψ (`least-below-boundary`), and the carrier, whose family's
-- tree code roots Ω, is not derivable from seeds the child names
-- (`carrier-underivable`, by Height.Reflection.carrier-unnamed):
-- Stationary.Derivable.not-derivable-from, read in heights. Conversely each
-- child tree lies below a derivation from the child's names, the product
-- over each label with the label's own name as a seed (`conclusion`,
-- `derivation`, `dominates`), so Ω is the least height above every
-- derivation from the child's names (`boundary-least`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
import SPT.Foundation.Tree as Tree
import SPT.Mahlo.Ambient as Ambient
open import SPT.Foundation.Tree.W using (sup)
open import SPT.Mahlo.Retraction using (Retracts)
import SPT.Mahlo.Specification as Specification
open import SPT.Mahlo.DS.Cedents using
  ( Ced; ∅ᶜ; _⊆_; Derivable; least; named-closed
  ; seed; empty; unit; two; natural; product; sum; tree; identity; result
  ; branch)
import SPT.Mahlo.DS.Naming.Trees as Trees
open import SPT.Mahlo.Heights using (either; height; leaf-below)
open import SPT.Mahlo.Heights.Least using
  (closure-height; closure-least)
open import SPT.OrdinalGeometry.Height.Ordinals using
  (Height; decoded; decoded-⊏)
import SPT.OrdinalGeometry.Height.Reflection as Reflection
open import SPT.OrdinalGeometry.Height.Simulation using
  (_⊑_; _⊏_; below; under; ⊑-⊏-trans; ⊏-trans; ⊏-irrefl)

------------------------------------------------------------------------
-- Derivations below child trees

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Specification.Formers C D) (unfolds : Reflection.Unfolds Q)
  (retracts : Retracts Q)
  {Ψ : Specification.Operator D} (R : Specification.Reflection Q Ψ)
  where

  -- A node over one premise and the points of a named code a, each child
  -- below a child tree, lies below the fork between the premise's tree
  -- and the spread of the others over a's name.
  forked :
    (a : C)
    (n :
      Specification.Name
        (Specification.Closure.interpret (Specification.Reflection.closure R))
        a)
    (h : Height ℓ) (hs : D a → Height ℓ)
    (v : Reflection.ChildTrees unfolds R)
    (vs : D a → Reflection.ChildTrees unfolds R)
    → h ⊑ decoded D (Reflection.embed unfolds (Reflection.codes unfolds R) v)
    → ((x : D a)
       → hs x
         ⊑ decoded D
             (Reflection.embed unfolds (Reflection.codes unfolds R) (vs x)))
    → (y : Lift ℓ 𝟙 ⊎ D a)
    → either h hs y
      ⊏ decoded D
          (Reflection.embed unfolds (Reflection.codes unfolds R)
            (Reflection.fork unfolds retracts R v
              (Reflection.spread unfolds retracts R a n vs)))
  forked a n h hs v vs p ps (inl _) =
    ⊑-⊏-trans p
      (decoded-⊏ D
        (Reflection.fork-left unfolds retracts R v
          (Reflection.spread unfolds retracts R a n vs)))
  forked a n h hs v vs p ps (inr x) =
    ⊑-⊏-trans (ps x)
      (decoded-⊏ D
        (⊏-trans (Reflection.spread-above unfolds retracts R a n vs x)
          (Reflection.fork-right unfolds retracts R v
            (Reflection.spread unfolds retracts R a n vs))))

  -- The same, with the child trees found from the children.
  gathered :
    (a : C)
    (n :
      Specification.Name
        (Specification.Closure.interpret (Specification.Reflection.closure R))
        a)
    (h : Height ℓ) (hs : D a → Height ℓ)
    → Σ (Reflection.ChildTrees unfolds R)
        (λ w →
          h
          ⊑ decoded D
              (Reflection.embed unfolds (Reflection.codes unfolds R) w))
    → ((x : D a)
       → Σ (Reflection.ChildTrees unfolds R)
           (λ w →
             hs x
             ⊑ decoded D
                 (Reflection.embed unfolds (Reflection.codes unfolds R) w)))
    → Σ (Reflection.ChildTrees unfolds R)
        (λ w →
          Tree.node (Lift ℓ 𝟙 ⊎ D a) (either h hs)
          ⊑ decoded D (Reflection.embed unfolds (Reflection.codes unfolds R) w))
  gathered a n h hs p ps =
    Reflection.fork unfolds retracts R (pr₁ p)
      (Reflection.spread unfolds retracts R a n (λ x → pr₁ (ps x))) ,
    below
      (forked a n h hs (pr₁ p) (λ x → pr₁ (ps x)) (pr₂ p) (λ x → pr₂ (ps x)))

  module _
    (extensionality : (X : Set ℓ) → FunExt X (λ _ → C))
    where

    -- The child's name for a name derivable from seeds it names
    -- (Cedents.least at Cedents.named-closed).
    name :
      {ν : Level} (Γ : Ced ν C)
      → Γ ⊆ Specification.Name
              (Specification.Closure.interpret
                (Specification.Reflection.closure R))
      → {c : C} → Derivable Q Ψ Γ c
      → Specification.Name
          (Specification.Closure.interpret
            (Specification.Reflection.closure R))
          c
    name Γ named d =
      least {Γ = Γ} named
        (named-closed extensionality (Specification.Reflection.closure R))
        d

    -- Mathematical shape: d : Γ ⊢ c, Γ named ⊢ Σ w. height d ⊑ decoded w.
    -- Each derivation from seeds the child names lies below a child tree.
    bounded :
      {ν : Level} (Γ : Ced ν C)
      → Γ ⊆ Specification.Name
              (Specification.Closure.interpret
                (Specification.Reflection.closure R))
      → {c : C}
        (d : Derivable Q Ψ Γ c)
      → Σ (Reflection.ChildTrees unfolds R)
          (λ w →
            height d
            ⊑ decoded D
                (Reflection.embed unfolds (Reflection.codes unfolds R) w))
    bounded Γ named (seed p) = Reflection.leaf unfolds retracts R , leaf-below
    bounded Γ named empty = Reflection.leaf unfolds retracts R , leaf-below
    bounded Γ named unit = Reflection.leaf unfolds retracts R , leaf-below
    bounded Γ named two = Reflection.leaf unfolds retracts R , leaf-below
    bounded Γ named natural =
      Reflection.leaf unfolds retracts R , leaf-below
    bounded Γ named (product a b d e) =
      gathered a (name Γ named d) (height d) (λ x → height (e x))
        (bounded Γ named d) (λ x → bounded Γ named (e x))
    bounded Γ named (sum a b d e) =
      gathered a (name Γ named d) (height d) (λ x → height (e x))
        (bounded Γ named d) (λ x → bounded Γ named (e x))
    bounded Γ named (tree a b d e) =
      gathered a (name Γ named d) (height d) (λ x → height (e x))
        (bounded Γ named d) (λ x → bounded Γ named (e x))
    bounded Γ named (identity a x y d) =
      Reflection.successor unfolds retracts R (pr₁ (bounded Γ named d)) ,
      below
        (λ u →
          ⊑-⊏-trans (pr₂ (bounded Γ named d))
            (decoded-⊏ D
              (Reflection.successor-above unfolds retracts R
                (pr₁ (bounded Γ named d)))))
    bounded Γ named (result a b d e) =
      gathered a (name Γ named d) (height d) (λ x → height (e x))
        (bounded Γ named d) (λ x → bounded Γ named (e x))
    bounded Γ named (branch a b d e y) =
      gathered a (name Γ named d) (height d) (λ x → height (e x))
        (bounded Γ named d) (λ x → bounded Γ named (e x))

    -- Every derivation from seeds the child names lies strictly below Ω.
    below-boundary :
      {ν : Level} (Γ : Ced ν C)
      → Γ ⊆ Specification.Name
              (Specification.Closure.interpret
                (Specification.Reflection.closure R))
      → {c : C}
        (d : Derivable Q Ψ Γ c)
      → height d ⊏ decoded D (Reflection.Ω unfolds R)
    below-boundary Γ named d =
      ⊑-⊏-trans (pr₂ (bounded Γ named d))
        (decoded-⊏ D
          (Reflection.unbounded unfolds R (pr₁ (bounded Γ named d))))

    -- Mathematical shape: ¬ (decoded Ω ⊑ height d).  No derivation from
    -- seeds the child names reaches Ω.
    excluded :
      {ν : Level} (Γ : Ced ν C)
      → Γ ⊆ Specification.Name
              (Specification.Closure.interpret
                (Specification.Reflection.closure R))
      → {c : C}
        (d : Derivable Q Ψ Γ c)
      → ¬ (decoded D (Reflection.Ω unfolds R) ⊑ height d)
    excluded Γ named d p =
      ⊏-irrefl (decoded D (Reflection.Ω unfolds R))
        (⊑-⊏-trans p (below-boundary Γ named d))

    -- The least height above the derivations from no seeds lies below Ω.
    least-below-boundary :
      {K : Set ℓ}
      (L : Specification.Closure (Ambient.formers ℓ)
        (Trees.requests Q Ψ) K)
      → closure-height Q Ψ L
        ⊑ decoded D (Reflection.Ω unfolds R)
    least-below-boundary L =
      closure-least Q Ψ L
        (decoded D (Reflection.Ω unfolds R))
        (λ d → below-boundary ∅ᶜ (λ p → 𝟘-elim p) d)

    -- The carrier is not derivable from seeds the child names: its name
    -- would make Ω a named tree.
    carrier-underivable :
      {ν : Level} (Γ : Ced ν C)
      → Γ ⊆ Specification.Name
              (Specification.Closure.interpret
                (Specification.Reflection.closure R))
      → ¬ Derivable Q Ψ Γ
            (Specification.Reflection.carrier R)
    carrier-underivable Γ named d =
      Reflection.carrier-unnamed unfolds R (name Γ named d)

------------------------------------------------------------------------
-- Child trees below derivations from the child's names

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Specification.Formers C D) (unfolds : Reflection.Unfolds Q)
  {Ψ : Specification.Operator D} (R : Specification.Reflection Q Ψ)
  where

  -- The name a child tree's derivation concludes: the product over its
  -- root label of the names of its subtrees.
  conclusion : Reflection.ChildTrees unfolds R → C
  conclusion (sup x f) =
    Specification.Formers.product Q
      ( Specification.Closure.interpret (Specification.Reflection.closure R) x
      , (λ y → conclusion (f y)))

  -- Its derivation from the child's names, each label a seed.
  derivation :
    (w : Reflection.ChildTrees unfolds R)
    → Derivable Q Ψ
        (Specification.Name
          (Specification.Closure.interpret
            (Specification.Reflection.closure R)))
        (conclusion w)
  derivation (sup x f) =
    product
      ( Specification.Closure.interpret (Specification.Reflection.closure R) x)
      (λ y → conclusion (f y)) (seed (x , refl)) (λ y → derivation (f y))

  -- Mathematical shape: decoded w ⊑ height (derivation w).
  dominates :
    (w : Reflection.ChildTrees unfolds R)
    → decoded D (Reflection.embed unfolds (Reflection.codes unfolds R) w)
      ⊑ height (derivation w)
  dominates (sup x f) = below (λ y → under (inr y) (dominates (f y)))

  -- Mathematical shape: (Π d : names ⊢ c. height d ⊏ t) → decoded Ω ⊑ t.
  -- Ω is the least height above every derivation from the child's names.
  boundary-least :
    (t : Height ℓ)
    → ({c : C}
       (d : Derivable Q Ψ
              (Specification.Name
                (Specification.Closure.interpret
                  (Specification.Reflection.closure R)))
              c)
       → height d ⊏ t)
    → decoded D (Reflection.Ω unfolds R) ⊑ t
  boundary-least t above =
    below
      (λ q →
        ⊑-⊏-trans
          (dominates
            (Reflection.unfold unfolds (Reflection.codes unfolds R) q))
          (above
            (derivation
              (Reflection.unfold unfolds (Reflection.codes unfolds R) q))))
