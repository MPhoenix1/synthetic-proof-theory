{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Height.Reflection where

-- Heights of an arbitrary reflection, in the geometry of its parent.  The
-- parent is a Tarski family (C , D) with formers and decoding laws, and a
-- reflection of an operator Ψ returns a parent code r with a closure on
-- D r.  The boundary of a parent family P is the node at the tree code of
-- P whose positions, read by tree-β, are the P-trees.  The boundary Ω of a
-- reflection is the boundary of the family (r , interpret) of all child
-- codes, so its positions are the child trees.  Ω lies above every child
-- tree, is regular for families indexed by points of child codes, is
-- closed under Ψ, and lies above every tree whose labels are named in the
-- child.  No particular parent or reflector is assumed, so the same
-- statements hold inside every reflected child that carries a reflector.

open import Agda.Primitive using (Level; _⊔_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; cong; subst)

import SPT.Cubical.Core.Generator.Tree as Tree
open import SPT.Cubical.Core.Generator.Tree.Relation using (node-rel)
import SPT.Cubical.Core.Mahlo.Specification as Mahlo
open import SPT.Cubical.Core.Mahlo.Decoding using (W; sup; DecodingLaws)
open import SPT.Cubical.OrdinalGeometry.Height.Simulation using
  (Closed; _⊑_; _⊏_; _≈_; below; under; ⊑-refl; ⊑-⊏-trans; ≈-sym; ≈→⊑)

private
  coe : ∀ {ℓ} {X Y : Set ℓ} → X ≡ Y → X → Y
  coe refl x = x

  coe-sym : ∀ {ℓ} {X Y : Set ℓ} (q : X ≡ Y) (y : Y) →
    coe q (coe (sym q) y) ≡ y
  coe-sym refl y = refl

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  {Q : Mahlo.Formers C D} (laws : DecodingLaws Q) where

  ----------------------------------------------------------------------
  -- Boundaries of parent families

  -- Mathematical shape, for P = (c , d):
  --
  --   Trees P = W (D c) (D ∘ d),
  --   Ω_P = node (tree P) (λ q → embed P (unfold q)).
  --
  -- unfold reads the decoding of the tree code of P as the P-trees by
  -- tree-β; where tree-β is refl it is the identity.
  Trees : Mahlo.Family D → Set ℓ
  Trees P = W (D (proj₁ P)) (λ x → D (proj₂ P x))

  embed : (P : Mahlo.Family D) → Trees P → Closed C D
  embed P (sup z f) = Tree.node (proj₂ P z) (λ y → embed P (f y))

  unfold : (P : Mahlo.Family D) → D (Mahlo.Formers.tree Q P) → Trees P
  unfold P = coe (DecodingLaws.tree-β laws (proj₁ P) (proj₂ P))

  fold : (P : Mahlo.Family D) → Trees P → D (Mahlo.Formers.tree Q P)
  fold P = coe (sym (DecodingLaws.tree-β laws (proj₁ P) (proj₂ P)))

  unfold-fold : (P : Mahlo.Family D) (w : Trees P) →
    unfold P (fold P w) ≡ w
  unfold-fold P = coe-sym (DecodingLaws.tree-β laws (proj₁ P) (proj₂ P))

  boundary : Mahlo.Family D → Closed C D
  boundary P =
    Tree.node (Mahlo.Formers.tree Q P) (λ q → embed P (unfold P q))

  -- Every P-tree lies below Ω_P.
  embed-below : (P : Mahlo.Family D) (w : Trees P) →
    embed P w ⊏ boundary P
  embed-below P w =
    under (fold P w)
      (subst (λ v → embed P w ⊑ embed P v) (sym (unfold-fold P w))
        (⊑-refl (embed P w)))

  -- Everything below Ω_P lies below some P-tree.
  boundary-bounded : (P : Mahlo.Family D) {x : Closed C D} →
    x ⊏ boundary P → Σ (Trees P) (λ w → x ⊑ embed P w)
  boundary-bounded P (under q x⊑) = unfold P q , x⊑

  ----------------------------------------------------------------------
  -- The boundary of a reflection

  -- The family of all child codes, and the child trees over it.
  codes : {Ψ : Mahlo.Operator D} → Mahlo.Reflection Q Ψ → Mahlo.Family D
  codes R =
    Mahlo.Reflection.carrier R
    , Mahlo.Closure.interpret (Mahlo.Reflection.closure R)

  ChildTrees : {Ψ : Mahlo.Operator D} → Mahlo.Reflection Q Ψ → Set ℓ
  ChildTrees R = Trees (codes R)

  -- Mathematical shape: Ω_R = Ω_{(r , interpret)}.
  Ω : {Ψ : Mahlo.Operator D} → Mahlo.Reflection Q Ψ → Closed C D
  Ω R = boundary (codes R)

  unbounded : {Ψ : Mahlo.Operator D} (R : Mahlo.Reflection Q Ψ)
    (w : ChildTrees R) → embed (codes R) w ⊏ Ω R
  unbounded R = embed-below (codes R)

  bounded : {Ψ : Mahlo.Operator D} (R : Mahlo.Reflection Q Ψ)
    {x : Closed C D} → x ⊏ Ω R →
    Σ (ChildTrees R) (λ w → x ⊑ embed (codes R) w)
  bounded R = boundary-bounded (codes R)

  -- Mathematical shape:
  --   a : r, f : D (interpret a) → Closed C D, Π y. f y ⊏ Ω
  --     ⊢ node (interpret a) f ⊏ Ω.
  -- A node at a child code whose children lie below Ω lies below Ω: the
  -- bounding child trees are assembled under the code a itself.
  regular : {Ψ : Mahlo.Operator D} (R : Mahlo.Reflection Q Ψ)
    (a : D (Mahlo.Reflection.carrier R))
    (f : D (Mahlo.Closure.interpret (Mahlo.Reflection.closure R) a) →
      Closed C D) →
    ((y : D (Mahlo.Closure.interpret (Mahlo.Reflection.closure R) a)) →
      f y ⊏ Ω R) →
    Tree.node (Mahlo.Closure.interpret (Mahlo.Reflection.closure R) a) f
      ⊏ Ω R
  regular R a f below-Ω =
    ⊑-⊏-trans
      (below λ y → under y (proj₂ (bounded R (below-Ω y))))
      (unbounded R (sup a (λ y → proj₁ (bounded R (below-Ω y)))))

  ----------------------------------------------------------------------
  -- Closure under the reflected operator

  -- The trees of the image of a child family G, as child trees: a node of
  -- shape x takes the child code proj₂ G x.
  relabel : {Ψ : Mahlo.Operator D} (R : Mahlo.Reflection Q Ψ)
    (G : Mahlo.Family
      (Mahlo.Closure.Decode (Mahlo.Reflection.closure R))) →
    Trees (Mahlo.Closure.map (Mahlo.Reflection.closure R) G) →
    ChildTrees R
  relabel R G (sup x k) = sup (proj₂ G x) (λ y → relabel R G (k y))

  relabel-≈ : {Ψ : Mahlo.Operator D} (R : Mahlo.Reflection Q Ψ)
    (G : Mahlo.Family
      (Mahlo.Closure.Decode (Mahlo.Reflection.closure R)))
    (v : Trees (Mahlo.Closure.map (Mahlo.Reflection.closure R) G)) →
    embed (codes R) (relabel R G v)
      ≈ embed (Mahlo.Closure.map (Mahlo.Reflection.closure R) G) v
  relabel-≈ R G (sup x k) = node-rel (λ y → relabel-≈ R G (k y))

  -- The child tree rooted at the child's own tree name for G, with every
  -- image tree of G as a child.
  named : {Ψ : Mahlo.Operator D} (R : Mahlo.Reflection Q Ψ)
    (G : Mahlo.Family
      (Mahlo.Closure.Decode (Mahlo.Reflection.closure R))) →
    ChildTrees R
  named R G =
    sup (proj₁ name) λ p →
      relabel R G
        (unfold (Mahlo.Closure.map (Mahlo.Reflection.closure R) G)
          (coe (cong D (proj₂ name)) p))
    where
      name = Mahlo.Closure.tree (Mahlo.Reflection.closure R) G

  named-⊒ : {Ψ : Mahlo.Operator D} (R : Mahlo.Reflection Q Ψ)
    (G : Mahlo.Family
      (Mahlo.Closure.Decode (Mahlo.Reflection.closure R))) →
    boundary (Mahlo.Closure.map (Mahlo.Reflection.closure R) G)
      ⊑ embed (codes R) (named R G)
  named-⊒ R G = below λ q →
    under (coe (sym (cong D (proj₂ name))) q)
      (subst
        (λ q′ → embed P (unfold P q)
          ⊑ embed (codes R) (relabel R G (unfold P q′)))
        (sym (coe-sym (cong D (proj₂ name)) q))
        (≈→⊑ (≈-sym (relabel-≈ R G (unfold P q)))))
    where
      name = Mahlo.Closure.tree (Mahlo.Reflection.closure R) G
      P = Mahlo.Closure.map (Mahlo.Reflection.closure R) G

  -- The image of every child family has its boundary below Ω.
  family-below : {Ψ : Mahlo.Operator D} (R : Mahlo.Reflection Q Ψ)
    (G : Mahlo.Family
      (Mahlo.Closure.Decode (Mahlo.Reflection.closure R))) →
    boundary (Mahlo.Closure.map (Mahlo.Reflection.closure R) G) ⊏ Ω R
  family-below R G = ⊑-⊏-trans (named-⊒ R G) (unbounded R (named R G))

  -- Mathematical shape: Π F. Ω_{Ψ (map F)} ⊏ Ω.
  -- The proof uses only the closure data for Ψ: inner F is a child family
  -- and inner-β identifies its image with Ψ (map F).
  closed : {Ψ : Mahlo.Operator D} (R : Mahlo.Reflection Q Ψ)
    (F : Mahlo.Family
      (Mahlo.Closure.Decode (Mahlo.Reflection.closure R))) →
    boundary (Ψ (Mahlo.Closure.map (Mahlo.Reflection.closure R) F)) ⊏ Ω R
  closed R F =
    subst (λ P → boundary P ⊏ Ω R)
      (Mahlo.Closure.inner-β (Mahlo.Reflection.closure R) F)
      (family-below R
        (Mahlo.Closure.inner (Mahlo.Reflection.closure R) F))

  ----------------------------------------------------------------------
  -- Trees named in the child

  -- A naming of a parent code c in the child: a child code whose points
  -- correspond to those of c, back after forth being the identity.
  record Naming {Ψ : Mahlo.Operator D} (R : Mahlo.Reflection Q Ψ)
    (c : C) : Set ℓ where
    field
      code : D (Mahlo.Reflection.carrier R)
      back : D (Mahlo.Closure.interpret (Mahlo.Reflection.closure R) code)
        → D c
      forth : D c →
        D (Mahlo.Closure.interpret (Mahlo.Reflection.closure R) code)
      back-forth : (z : D c) → back (forth z) ≡ z

  -- A tree is named when every node label is named.
  Named : {Ψ : Mahlo.Operator D} (R : Mahlo.Reflection Q Ψ) →
    Closed C D → Set ℓ
  Named R (Tree.hole ())
  Named R (Tree.node c f) = Naming R c × ((y : D c) → Named R (f y))

  copy : {Ψ : Mahlo.Operator D} (R : Mahlo.Reflection Q Ψ)
    (x : Closed C D) → Named R x → ChildTrees R
  copy R (Tree.hole ()) n
  copy R (Tree.node c f) (N , Ns) =
    sup (Naming.code N) λ p →
      copy R (f (Naming.back N p)) (Ns (Naming.back N p))

  copy-⊒ : {Ψ : Mahlo.Operator D} (R : Mahlo.Reflection Q Ψ)
    (x : Closed C D) (n : Named R x) → x ⊑ embed (codes R) (copy R x n)
  copy-⊒ R (Tree.hole ()) n
  copy-⊒ R (Tree.node c f) (N , Ns) = below λ z →
    under (Naming.forth N z)
      (subst (λ w → f z ⊑ embed (codes R) (copy R (f w) (Ns w)))
        (sym (Naming.back-forth N z))
        (copy-⊒ R (f z) (Ns z)))

  -- Mathematical shape: every named tree lies below Ω.
  above : {Ψ : Mahlo.Operator D} (R : Mahlo.Reflection Q Ψ)
    (x : Closed C D) → Named R x → x ⊏ Ω R
  above R x n = ⊑-⊏-trans (copy-⊒ R x n) (unbounded R (copy R x n))
