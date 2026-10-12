{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Height.Ordinals.Mahlo where

-- Inaccessible points of Ord(ℓ), from the Mahlo rule.  The universe of
-- level ℓ is a parent whose codes are its types (Core.Mahlo.Ambient), and
-- the reflector of the Mahlo rule is a parameter; in Agda one is given by
-- induction–recursion, which this release does not use.  The main
-- results are mahlo, a point closed under an operator and above a height,
-- and between, which places that point strictly below Ord(ℓ).

open import Agda.Primitive using (Level; lsuc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)

import SPT.Cubical.Core.Generator.Tree as Tree
import SPT.Cubical.Core.Mahlo.Specification as Mahlo
open import SPT.Cubical.Core.Mahlo.Decoding using (W; sup)
import SPT.Cubical.Core.Mahlo.Ambient as Ambient
open Ambient using (Operator)
open import SPT.Cubical.OrdinalGeometry.Height.Simulation using
  (_◃_; _⊑_; _⊏_; below; under; ⊑-⊏-trans; ⊏-irrefl)
import SPT.Cubical.OrdinalGeometry.Height.Reflection as Reflection
open import SPT.Cubical.OrdinalGeometry.Height.Ordinals using
  (Height; lift-height; lift-⊏; Ord; upper)

private
  variable
    ℓ : Level

  Family : (ℓ : Level) → Set (lsuc ℓ)
  Family ℓ = Mahlo.Family (λ (A : Set ℓ) → A)

  boundary : Family ℓ → Height ℓ
  boundary {ℓ} = Reflection.boundary (Ambient.laws ℓ)

------------------------------------------------------------------------
-- Labels of a height, and operators paired with them

-- The nodes of a height: the root, or a node of a child.
Nodes : Height ℓ → Set ℓ
Nodes (Tree.hole ())
Nodes {ℓ} (Tree.node A f) = ⊤ {ℓ} ⊎ Σ A λ a → Nodes (f a)

label : (t : Height ℓ) → Nodes t → Set ℓ
label (Tree.hole ())
label (Tree.node A f) (inj₁ _) = A
label (Tree.node A f) (inj₂ (a , n)) = label (f a) n

-- The family of the labels of t, indexed by its nodes.
labels : Height ℓ → Family ℓ
labels t = Nodes t , label t

-- Mathematical shape: (Ψ ⊕ P)(X) = Ψ(X) + P, with members side by side.
paired : Operator ℓ → Family ℓ → Operator ℓ
paired Ψ P X = (proj₁ (Ψ X) ⊎ proj₁ P) , [ proj₂ (Ψ X) , proj₂ P ]

private
  sum : Family ℓ → Family ℓ → Family ℓ
  sum P Q = (proj₁ P ⊎ proj₁ Q) , [ proj₂ P , proj₂ Q ]

  -- The trees of the left summand are trees of the sum, with the same
  -- height.
  left : (P Q : Family ℓ) → W (proj₁ P) (proj₂ P)
    → W (proj₁ (sum P Q)) (proj₂ (sum P Q))
  left P Q (sup a f) = sup (inj₁ a) λ y → left P Q (f y)

  left-⊑ : (P Q : Family ℓ) (w : W (proj₁ P) (proj₂ P))
    → Reflection.embed (Ambient.laws ℓ) P w
      ⊑ Reflection.embed (Ambient.laws ℓ) (sum P Q) (left P Q w)
  left-⊑ P Q (sup a f) = below λ y → under y (left-⊑ P Q (f y))

  boundary-left : (P Q : Family ℓ) → boundary P ⊑ boundary (sum P Q)
  boundary-left P Q = below λ w → under (left P Q w) (left-⊑ P Q w)

  -- Members of equal families correspond.
  member-≡ : {u v : Family ℓ} (p : u ≡ v) (x : proj₁ u)
    → proj₂ u x ≡ proj₂ v (subst proj₁ p x)
  member-≡ refl x = refl

  subst-back : {u v : Family ℓ} (p : u ≡ v) (y : proj₁ v)
    → subst proj₁ p (subst proj₁ (sym p) y) ≡ y
  subst-back refl y = refl

  coe : {A B : Set ℓ} → A ≡ B → A → B
  coe refl x = x

  coe-sym : {A B : Set ℓ} (q : A ≡ B) (y : B) → coe q (coe (sym q) y) ≡ y
  coe-sym refl y = refl

------------------------------------------------------------------------
-- The closed inaccessible point above a height

-- The reflection of Ψ paired with the labels of t, its child, and its
-- point Ω.
reflection : (M : Mahlo.Mahlo (Ambient.formers ℓ)) (Ψ : Operator ℓ)
  (t : Height ℓ) → Mahlo.Reflection (Ambient.formers ℓ) (paired Ψ (labels t))
reflection M Ψ t = Mahlo.Mahlo.reflect M (paired Ψ (labels t))

child : (M : Mahlo.Mahlo (Ambient.formers ℓ)) (Ψ : Operator ℓ)
  (t : Height ℓ)
  → Mahlo.Closure (Ambient.formers ℓ) (paired Ψ (labels t))
      (Mahlo.Reflection.carrier (reflection M Ψ t))
child M Ψ t = Mahlo.Reflection.closure (reflection M Ψ t)

point : Mahlo.Mahlo (Ambient.formers ℓ) → Operator ℓ → Height ℓ → Height ℓ
point {ℓ} M Ψ t = Reflection.Ω (Ambient.laws ℓ) (reflection M Ψ t)

-- Every member of the paired image of a child family F is named in the
-- child: inner F lists it, by inner-β.
member : (M : Mahlo.Mahlo (Ambient.formers ℓ)) (Ψ : Operator ℓ)
  (t : Height ℓ) (F : Mahlo.Family (Mahlo.Closure.Decode (child M Ψ t)))
  (x : proj₁ (paired Ψ (labels t) (Mahlo.Closure.map (child M Ψ t) F)))
  → Mahlo.Closure.Name (child M Ψ t)
      (proj₂ (paired Ψ (labels t) (Mahlo.Closure.map (child M Ψ t) F)) x)
member M Ψ t F x =
  proj₂ inner y ,
  trans (member-≡ p y)
    (cong (proj₂ (paired Ψ (labels t) (Mahlo.Closure.map (child M Ψ t) F)))
      (subst-back p x))
  where
    inner = Mahlo.Closure.inner (child M Ψ t) F
    p = Mahlo.Closure.inner-β (child M Ψ t) F
    y = subst proj₁ (sym p) x

private
  -- A child family: the unit name, constantly.
  seed : (M : Mahlo.Mahlo (Ambient.formers ℓ)) (Ψ : Operator ℓ)
    (t : Height ℓ) → Mahlo.Family (Mahlo.Closure.Decode (child M Ψ t))
  seed M Ψ t = unit , λ _ → unit
    where
      unit = proj₁ (Mahlo.Closure.unit (child M Ψ t))

  -- The right part of the paired image lists the labels of t, so the
  -- child names each of them.
  naming : (M : Mahlo.Mahlo (Ambient.formers ℓ)) (Ψ : Operator ℓ)
    (t : Height ℓ) (n : Nodes t)
    → Reflection.Naming (Ambient.laws ℓ) (reflection M Ψ t) (label t n)
  naming M Ψ t n = record
    { code = proj₁ name
    ; back = coe (proj₂ name)
    ; forth = coe (sym (proj₂ name))
    ; back-forth = coe-sym (proj₂ name)
    }
    where
      name = member M Ψ t (seed M Ψ t) (inj₂ n)

  -- A height all of whose labels are named in the child is named.
  named : (M : Mahlo.Mahlo (Ambient.formers ℓ)) (Ψ : Operator ℓ)
    (t s : Height ℓ)
    → ((n : Nodes s) →
        Reflection.Naming (Ambient.laws ℓ) (reflection M Ψ t) (label s n))
    → Reflection.Named (Ambient.laws ℓ) (reflection M Ψ t) s
  named M Ψ t (Tree.hole ()) N
  named M Ψ t (Tree.node A f) N =
    N (inj₁ tt) , λ a → named M Ψ t (f a) λ n → N (inj₂ (a , n))

-- Mathematical shape, writing Ω for point M Ψ t:
--
--   (Π F. Ω_{Ψ (map F)} ⊏ Ω) × (t ⊏ Ω).
--
-- Ω is closed under Ψ and lies above t.  Closure under the pair is the
-- closure of Height.Reflection, restricted to its left part; t is named in
-- the child by the right part.
mahlo : (M : Mahlo.Mahlo (Ambient.formers ℓ)) (Ψ : Operator ℓ)
  (t : Height ℓ)
  → ((F : Mahlo.Family (Mahlo.Closure.Decode (child M Ψ t))) →
      boundary (Ψ (Mahlo.Closure.map (child M Ψ t) F)) ⊏ point M Ψ t)
    × (t ⊏ point M Ψ t)
mahlo {ℓ} M Ψ t =
  (λ F →
    ⊑-⊏-trans
      (boundary-left (Ψ (Mahlo.Closure.map (child M Ψ t) F)) (labels t))
      (Reflection.closed (Ambient.laws ℓ) (reflection M Ψ t) F))
  , Reflection.above (Ambient.laws ℓ) (reflection M Ψ t) t
      (named M Ψ t t (naming M Ψ t))

-- The closed inaccessible point lies strictly between t and Ord(ℓ).
between : (M : Mahlo.Mahlo (Ambient.formers ℓ)) (Ψ : Operator ℓ)
  (t : Height ℓ)
  → (lift-height t ⊏ lift-height (point M Ψ t))
    × (lift-height (point M Ψ t) ◃ Ord ℓ)
between M Ψ t = lift-⊏ (proj₂ (mahlo M Ψ t)) , upper (point M Ψ t)

-- Discriminator: closure is a condition.  The point of a reflection is
-- not closed under the constant operator that returns the codes of that
-- reflection, whose boundary is the point itself.
not-closed : (M : Mahlo.Mahlo (Ambient.formers ℓ)) (Ψ : Operator ℓ)
  (t : Height ℓ)
  → ¬ ((F : Mahlo.Family (Mahlo.Closure.Decode (child M Ψ t))) →
      boundary (Reflection.codes (Ambient.laws ℓ) (reflection M Ψ t))
        ⊏ point M Ψ t)
not-closed M Ψ t closed = ⊏-irrefl (point M Ψ t) (closed (seed M Ψ t))

-- Discriminator: closure does not single out these points.  Ord(ℓ)
-- itself lies above the boundary of every operator's output and above
-- every height, as a parent is its own closure.  What between adds is that
-- the closed points lie strictly below Ord(ℓ), because the carrier of a
-- reflection is a type of level ℓ.
Ord-closed : (Ψ : Operator ℓ)
  → ((F : Family ℓ) → lift-height (boundary (Ψ F)) ◃ Ord ℓ)
    × ((t : Height ℓ) → lift-height t ◃ Ord ℓ)
Ord-closed Ψ = (λ F → upper (boundary (Ψ F))) , upper
