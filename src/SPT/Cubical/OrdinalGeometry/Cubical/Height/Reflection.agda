{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Height.Reflection where

-- The ranks of boundaries over the universe of level ℓ.  For a family P of
-- types, the positions of the boundary Ω_P (Height.Reflection) are the
-- P-trees, and the points of its rank are, merely, the ranks of P-trees
-- (cut).  For a reflection the family is that of its child codes
-- (reflection-rank).  All of this is constructive.

open import Agda.Primitive using (Level; lsuc)

import Cubical.Data.Sigma.Base as Sigma
import Cubical.Data.Sum as Sum
open Sum using (inl; inr)
import Cubical.Foundations.Prelude as Cubical
import Cubical.HITs.PropositionalTruncation as Truncation
open Truncation using (∥_∥₁; ∣_∣₁)
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

import SPT.Cubical.Core.Mahlo.Specification as Mahlo
open import SPT.Cubical.Core.Mahlo.Decoding using (W; sup)
import SPT.Cubical.Core.Mahlo.Ambient as Ambient
import SPT.Cubical.OrdinalGeometry.Height.Reflection as Reflection
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Ordinals using
  (successor; successor-segments)
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Supremum.Family
  as Family
open import SPT.Cubical.OrdinalGeometry.Cubical.Height.Rank using
  (rank; child)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- Families of types and their trees

-- Mathematical shape: Family(ℓ) = Σ (A : Set ℓ). A → Set ℓ.
Family : (ℓ : Level) → Set (lsuc ℓ)
Family ℓ = Mahlo.Family (λ (A : Set ℓ) → A)

Trees : Family ℓ → Set ℓ
Trees {ℓ} = Reflection.Trees (Ambient.laws ℓ)

-- The rank of a P-tree, and the rank of the boundary Ω_P.
tree-rank : (P : Family ℓ) → Trees P → Woset.Woset ℓ ℓ
tree-rank {ℓ} P w = rank (Reflection.embed (Ambient.laws ℓ) P w)

boundary-rank : Family ℓ → Woset.Woset ℓ ℓ
boundary-rank {ℓ} P = rank (Reflection.boundary (Ambient.laws ℓ) P)

------------------------------------------------------------------------
-- The cut

-- Mathematical shape: rank w ≺ rank Ω_P.  The P-tree w is a child of Ω_P.
tree-below : (P : Family ℓ) (w : Trees P)
  → Simulation._≺_ (tree-rank P w) (boundary-rank P)
tree-below {ℓ} P w =
  child (W (Cubical.fst P) (Cubical.snd P))
    (λ q → Reflection.embed (Ambient.laws ℓ) P q) w

-- Every principal segment of the rank of a P-tree is, merely, the rank of
-- a subtree: a point of the supremum is the top of a child's successor or
-- lies below it.
subtree : (P : Family ℓ) (w : Trees P)
  (z : Cubical.fst (tree-rank P w))
  → ∥ Cubical.Σ (Trees P) (λ v →
      Woset.WosetEquiv (Simulation._↓_ (tree-rank P w) z) (tree-rank P v))
    ∥₁
subtree P (sup c k) z =
  Truncation.rec Truncation.squash₁
    (λ represented →
      let y = Cubical.fst represented
          x = Cubical.fst (Cubical.snd represented)
          e = Cubical.snd (Cubical.snd represented)
      in below y x e (successor-segments (tree-rank P (k y)) x))
    (Family.covered (λ y → successor (tree-rank P (k y))) z)
  where
    below : (y : Cubical.snd P c)
      (x : Cubical.fst (successor (tree-rank P (k y))))
      → Woset.WosetEquiv (Simulation._↓_ (tree-rank P (sup c k)) z)
          (Simulation._↓_ (successor (tree-rank P (k y))) x)
      → Woset.WosetEquiv
          (Simulation._↓_ (successor (tree-rank P (k y))) x)
          (tree-rank P (k y))
        Sum.⊎ Cubical.Σ (Cubical.fst (tree-rank P (k y))) (λ x′ →
          Woset.WosetEquiv
            (Simulation._↓_ (successor (tree-rank P (k y))) x)
            (Simulation._↓_ (tree-rank P (k y)) x′))
      → ∥ Cubical.Σ (Trees P) (λ v →
          Woset.WosetEquiv (Simulation._↓_ (tree-rank P (sup c k)) z)
            (tree-rank P v))
        ∥₁
    below y x e (inl e′) = ∣ k y Cubical., Woset.compWosetEquiv e e′ ∣₁
    below y x e (inr (Cubical._,_ x′ e′)) =
      Truncation.map
        (λ found →
          Cubical.fst found Cubical.,
          Woset.compWosetEquiv e
            (Woset.compWosetEquiv e′ (Cubical.snd found)))
        (subtree P (k y) x′)

-- Mathematical shape: α ≺ rank Ω_P → ‖Σ w. α ≃ rank w‖.
segment : (P : Family ℓ) (α : Woset.Woset ℓ ℓ)
  → Simulation._≺_ α (boundary-rank P)
  → ∥ Cubical.Σ (Trees P) (λ w → Woset.WosetEquiv α (tree-rank P w)) ∥₁
segment P α (Cubical._,_ point e) =
  Truncation.rec Truncation.squash₁
    (λ represented →
      let w = Cubical.fst represented
          x = Cubical.fst (Cubical.snd represented)
          e′ = Cubical.snd (Cubical.snd represented)
          α≃ = Woset.compWosetEquiv (Woset.invWosetEquiv e) e′
      in below w x α≃ (successor-segments (tree-rank P w) x))
    (Family.covered (λ w → successor (tree-rank P w)) point)
  where
    below : (w : Trees P) (x : Cubical.fst (successor (tree-rank P w)))
      → Woset.WosetEquiv α (Simulation._↓_ (successor (tree-rank P w)) x)
      → Woset.WosetEquiv
          (Simulation._↓_ (successor (tree-rank P w)) x) (tree-rank P w)
        Sum.⊎ Cubical.Σ (Cubical.fst (tree-rank P w)) (λ x′ →
          Woset.WosetEquiv
            (Simulation._↓_ (successor (tree-rank P w)) x)
            (Simulation._↓_ (tree-rank P w) x′))
      → ∥ Cubical.Σ (Trees P) (λ v → Woset.WosetEquiv α (tree-rank P v)) ∥₁
    below w x α≃ (inl e″) = ∣ w Cubical., Woset.compWosetEquiv α≃ e″ ∣₁
    below w x α≃ (inr (Cubical._,_ x′ e″)) =
      Truncation.map
        (λ found →
          Cubical.fst found Cubical.,
          Woset.compWosetEquiv α≃
            (Woset.compWosetEquiv e″ (Cubical.snd found)))
        (subtree P w x′)

-- Mathematical shape: α ≺ rank Ω_P ⇔ ‖Σ w. α ≃ rank w‖.
cut : (P : Family ℓ) (α : Woset.Woset ℓ ℓ)
  → (Simulation._≺_ α (boundary-rank P)
      → ∥ Cubical.Σ (Trees P) (λ w → Woset.WosetEquiv α (tree-rank P w)) ∥₁)
    Sigma.×
    (∥ Cubical.Σ (Trees P) (λ w → Woset.WosetEquiv α (tree-rank P w)) ∥₁
      → Simulation._≺_ α (boundary-rank P))
cut P α =
  segment P α Cubical.,
  Truncation.rec (Simulation.isPropValued≺ α (boundary-rank P))
    (λ found →
      Simulation.≺RespectsEquivL (boundary-rank P)
        (Woset.invWosetEquiv (Cubical.snd found))
        (tree-below P (Cubical.fst found)))

------------------------------------------------------------------------
-- Reflections

-- The rank of the boundary of a reflection R of Ψ: the family of its
-- child codes, whose trees are the child trees.
reflection-rank : {Ψ : Ambient.Operator ℓ}
  → Mahlo.Reflection (Ambient.formers ℓ) Ψ → Woset.Woset ℓ ℓ
reflection-rank {ℓ} R = boundary-rank (Reflection.codes (Ambient.laws ℓ) R)
