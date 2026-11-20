{-# OPTIONS --safe --without-K #-}

module SPT.OrdinalGeometry.Height.Reflection where

-- Heights of an arbitrary reflection, in the geometry of its parent. The
-- parent is a Tarski family (C , D) with formers whose tree codes unfold onto
-- their trees up to similarity (Unfolds), as exact decoding laws give
-- (lawful) and decoding up to retraction gives (retracted). A reflection of an
-- operator Ψ returns a parent code r with a closure on D r. The boundary of a
-- parent family P is the node at the tree code of P whose positions, read by
-- the unfolding, are the P-trees. The boundary Ω of a reflection is the
-- boundary of the family (r , interpret) of all child codes, so its positions
-- are the child trees. Ω lies above every child tree, is regular for families
-- indexed by points of child codes, is closed under Ψ, and lies above every
-- tree whose labels are named in the child. So Ω is excluded from its child,
-- as ε₀ is from the notations below it: no child tree reaches it (excluded)
-- and it is no named tree (boundary-unnamed). Hence the child names neither
-- the tree code of its own family (tree-unnamed) nor its carrier
-- (carrier-unnamed), and Ψ never returns the child's own codes
-- (codes-unreturned): closure under an operator is a condition, failing
-- for the constant operator returning the child's codes, at the family of
-- the unit code (unit-family, not-closed). A name of a parent code in the
-- child names it (name-naming). The child trees bound their families
-- indexed by the points of child codes (child-trees-bound-families, an
-- instance of Regularity). With the formers decoded up to retraction, the
-- child's empty, unit and two codes and every code naming a parent code
-- build child trees above their parts (leaf, successor, fork, spread), and
-- the class of a child code, the family over the two code of the empty
-- code and it, has its boundary below Ω (child-class, child-class-below). No
-- particular parent or reflector is assumed, so the same statements hold
-- inside every reflected child that carries a reflector.
--
--   Ω_R = node (tree (r , interpret)) (λ q → embed (unfold q)).

open import SPT.Base
import SPT.Foundation.Tree as Tree
open import SPT.Foundation.Tree.Relation using (node-rel)
open import SPT.Mahlo.Specification using
  (Family; Operator; Formers; Decode; map; Name; Closure; Reflection)
open import SPT.Foundation.Tree.W using (W; sup)
open import SPT.Mahlo.Decoding using (DecodingLaws)
open import SPT.Mahlo.Retraction using
  (out; into; out-into; Unfolding; Similar; unfolding-of-identification;
   Retracts; choose)
open import SPT.OrdinalGeometry.Height.Simulation using
  (Closed; _⊑_; _⊏_; _≈_; below; under; ⊑-refl; ⊑-⊏-trans; ⊏-⊑-trans;
   ⊏-irrefl; ≈-sym; ≈→⊑)
open import SPT.OrdinalGeometry.Regularity using (Bounded-Families)

------------------------------------------------------------------------
-- Tree codes that unfold onto their trees

-- Logical kind: record, a hypothesis on a parent with formers.
-- Mathematical shape: for every family P, the decoding of the tree code of P
-- unfolds onto the P-trees, up to similarity.
record Unfolds {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Formers C D) : Set (κ ⊔ ℓ) where
  field
    tree : (P : Family D) →
      Unfolding (D (Formers.tree Q P)) (D (pr₁ P)) (λ x → D (pr₂ P x))

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D} where

  -- Exact decoding laws give the unfolding, by transport along tree-β.
  lawful : DecodingLaws Q → Unfolds Q
  lawful laws = record
    { tree = λ P →
        unfolding-of-identification
          (DecodingLaws.tree-β laws (pr₁ P) (pr₂ P))
    }

  -- Decoding up to retraction gives it as its tree field.
  retracted : Retracts Q → Unfolds Q
  retracted retracts = record
    { tree = λ P → Retracts.tree retracts (pr₁ P) (pr₂ P) }

-- A family moved along an identification of its index code is the family
-- there.
moved-family : {κ ℓ : Level} {C : Set κ} (D : C → Set ℓ) {c c′ : C}
  (e : c ＝ c′) (h : D c′ → C) →
  _＝_ {A = Family D} (c , (λ y → h (transport id (ap D e) y))) (c′ , h)
moved-family D refl h = refl

-- The child family whose index and members are the child's unit code.
unit-family : {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D}
  {Ψ : Operator D} (R : Reflection Q Ψ) →
  Family (Decode D (Closure.interpret (Reflection.closure R)))
unit-family R =
  pr₁ (Closure.unit (Reflection.closure R)) ,
  (λ y → pr₁ (Closure.unit (Reflection.closure R)))

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D}
  (unfolds : Unfolds Q) where

  ----------------------------------------------------------------------
  -- Boundaries of parent families

  -- Mathematical shape, for P = (c , d):
  --
  --   Trees P = W (D c) (D ∘ d),
  --   Ω_P = node (tree P) (λ q → embed P (unfold q)).
  --
  -- unfold reads the decoding of the tree code of P as the P-trees; at exact
  -- laws whose tree-β is refl it is the identity.
  Trees : Family D → Set ℓ
  Trees P = W (D (pr₁ P)) (λ x → D (pr₂ P x))

  embed : (P : Family D) → Trees P → Closed C D
  embed P (sup z f) = Tree.node (pr₂ P z) (λ y → embed P (f y))

  unfold : (P : Family D) → D (Formers.tree Q P) → Trees P
  unfold P = Unfolding.out (Unfolds.tree unfolds P)

  fold : (P : Family D) → Trees P → D (Formers.tree Q P)
  fold P = Unfolding.into (Unfolds.tree unfolds P)

  unfold-fold : (P : Family D) (w : Trees P) →
    Similar (unfold P (fold P w)) w
  unfold-fold P = Unfolding.out-into (Unfolds.tree unfolds P)

  -- Similar trees have the same height; one direction is used.
  similar-⊑ : (P : Family D) {v w : Trees P} → Similar v w →
    embed P w ⊑ embed P v
  similar-⊑ P {sup x f} {sup y g} (refl , s) =
    below (λ i → under i (similar-⊑ P (s i)))

  boundary : Family D → Closed C D
  boundary P = Tree.node (Formers.tree Q P) (λ q → embed P (unfold P q))

  -- Every P-tree lies below Ω_P.
  embed-below : (P : Family D) (w : Trees P) → embed P w ⊏ boundary P
  embed-below P w = under (fold P w) (similar-⊑ P (unfold-fold P w))

  -- Everything below Ω_P lies below some P-tree.
  boundary-bounded : (P : Family D) {x : Closed C D} →
    x ⊏ boundary P → Σ (Trees P) (λ w → x ⊑ embed P w)
  boundary-bounded P (under q x⊑) = unfold P q , x⊑

  ----------------------------------------------------------------------
  -- The boundary of a reflection

  -- The family of all child codes, and the child trees over it.
  codes : {Ψ : Operator D} → Reflection Q Ψ → Family D
  codes R =
    Reflection.carrier R , Closure.interpret (Reflection.closure R)

  ChildTrees : {Ψ : Operator D} → Reflection Q Ψ → Set ℓ
  ChildTrees R = Trees (codes R)

  -- Mathematical shape: Ω_R = Ω_{(r , interpret)}.
  Ω : {Ψ : Operator D} → Reflection Q Ψ → Closed C D
  Ω R = boundary (codes R)

  unbounded : {Ψ : Operator D} (R : Reflection Q Ψ) (w : ChildTrees R) →
    embed (codes R) w ⊏ Ω R
  unbounded R = embed-below (codes R)

  bounded : {Ψ : Operator D} (R : Reflection Q Ψ) {x : Closed C D} →
    x ⊏ Ω R → Σ (ChildTrees R) (λ w → x ⊑ embed (codes R) w)
  bounded R = boundary-bounded (codes R)

  -- Mathematical shape:
  --   a : r, f : D (interpret a) → Closed C D, Π y. f y ⊏ Ω
  --     ⊢ node (interpret a) f ⊏ Ω.
  -- A node at a child code whose children lie below Ω lies below Ω: the
  -- bounding child trees are assembled under the code a itself.
  regular : {Ψ : Operator D} (R : Reflection Q Ψ)
    (a : D (Reflection.carrier R))
    (f : D (Closure.interpret (Reflection.closure R) a) → Closed C D) →
    ((y : D (Closure.interpret (Reflection.closure R) a)) → f y ⊏ Ω R) →
    Tree.node (Closure.interpret (Reflection.closure R) a) f ⊏ Ω R
  regular R a f below-Ω =
    ⊑-⊏-trans
      (below (λ y → under y (pr₂ (bounded R (below-Ω y)))))
      (unbounded R (sup a (λ y → pr₁ (bounded R (below-Ω y)))))

  ----------------------------------------------------------------------
  -- Closure under the reflected operator

  -- The trees of the image of a child family G, as child trees: a node of
  -- shape x takes the child code pr₂ G x.
  relabel : {Ψ : Operator D} (R : Reflection Q Ψ)
    (G : Family (Decode D (Closure.interpret (Reflection.closure R)))) →
    Trees (map D (Closure.interpret (Reflection.closure R)) G) →
    ChildTrees R
  relabel R G (sup x k) = sup (pr₂ G x) (λ y → relabel R G (k y))

  relabel-≈ : {Ψ : Operator D} (R : Reflection Q Ψ)
    (G : Family (Decode D (Closure.interpret (Reflection.closure R))))
    (v : Trees (map D (Closure.interpret (Reflection.closure R)) G)) →
    embed (codes R) (relabel R G v)
      ≈ embed (map D (Closure.interpret (Reflection.closure R)) G) v
  relabel-≈ R G (sup x k) = node-rel (λ y → relabel-≈ R G (k y))

  -- The child tree rooted at the child's own tree name for G, with every
  -- image tree of G as a child.
  named : {Ψ : Operator D} (R : Reflection Q Ψ)
    (G : Family (Decode D (Closure.interpret (Reflection.closure R)))) →
    ChildTrees R
  named R G =
    sup (pr₁ (Closure.tree (Reflection.closure R) G))
      (λ p →
        relabel R G
          (unfold (map D (Closure.interpret (Reflection.closure R)) G)
            (transport id
              (ap D (pr₂ (Closure.tree (Reflection.closure R) G))) p)))

  named-⊒ : {Ψ : Operator D} (R : Reflection Q Ψ)
    (G : Family (Decode D (Closure.interpret (Reflection.closure R)))) →
    boundary (map D (Closure.interpret (Reflection.closure R)) G)
      ⊑ embed (codes R) (named R G)
  named-⊒ R G =
    below (λ q →
      under
        (transport id
          (ap D (pr₂ (Closure.tree (Reflection.closure R) G)) ⁻¹) q)
        (transport
          (λ q′ →
            embed (map D (Closure.interpret (Reflection.closure R)) G)
              (unfold (map D (Closure.interpret (Reflection.closure R)) G) q)
            ⊑ embed (codes R)
                (relabel R G
                  (unfold
                    (map D (Closure.interpret (Reflection.closure R)) G)
                    q′)))
          (back-and-forth-transport id
            (ap D (pr₂ (Closure.tree (Reflection.closure R) G))) q ⁻¹)
          (≈→⊑
            (≈-sym
              (relabel-≈ R G
                (unfold (map D (Closure.interpret (Reflection.closure R)) G)
                  q))))))

  -- The image of every child family has its boundary below Ω.
  family-below : {Ψ : Operator D} (R : Reflection Q Ψ)
    (G : Family (Decode D (Closure.interpret (Reflection.closure R)))) →
    boundary (map D (Closure.interpret (Reflection.closure R)) G) ⊏ Ω R
  family-below R G = ⊑-⊏-trans (named-⊒ R G) (unbounded R (named R G))

  -- Mathematical shape: Π F. Ω_{Ψ (map F)} ⊏ Ω.
  -- The proof uses only the closure data for Ψ: inner F is a child family
  -- and inner-β identifies its image with Ψ (map F).
  closed : {Ψ : Operator D} (R : Reflection Q Ψ)
    (F : Family (Decode D (Closure.interpret (Reflection.closure R)))) →
    boundary (Ψ (map D (Closure.interpret (Reflection.closure R)) F))
      ⊏ Ω R
  closed R F =
    transport (λ P → boundary P ⊏ Ω R)
      (Closure.inner-β (Reflection.closure R) F)
      (family-below R (Closure.inner (Reflection.closure R) F))

  ----------------------------------------------------------------------
  -- Trees named in the child

  -- A naming of a parent code c in the child: a child code whose points
  -- correspond to those of c, back after forth being the identity.
  record Naming {Ψ : Operator D} (R : Reflection Q Ψ) (c : C) : Set ℓ where
    field
      code : D (Reflection.carrier R)
      back : D (Closure.interpret (Reflection.closure R) code) → D c
      forth : D c → D (Closure.interpret (Reflection.closure R) code)
      back-forth : (z : D c) → back (forth z) ＝ z

  -- A tree is named when every node label is named.
  Named : {Ψ : Operator D} (R : Reflection Q Ψ) → Closed C D → Set ℓ
  Named R (Tree.hole ())
  Named R (Tree.node c f) = Naming R c × ((y : D c) → Named R (f y))

  copy : {Ψ : Operator D} (R : Reflection Q Ψ) (x : Closed C D) →
    Named R x → ChildTrees R
  copy R (Tree.hole ()) n
  copy R (Tree.node c f) (N , Ns) =
    sup (Naming.code N)
      (λ p → copy R (f (Naming.back N p)) (Ns (Naming.back N p)))

  copy-⊒ : {Ψ : Operator D} (R : Reflection Q Ψ) (x : Closed C D)
    (n : Named R x) → x ⊑ embed (codes R) (copy R x n)
  copy-⊒ R (Tree.hole ()) n
  copy-⊒ R (Tree.node c f) (N , Ns) =
    below (λ z →
      under (Naming.forth N z)
        (transport (λ w → f z ⊑ embed (codes R) (copy R (f w) (Ns w)))
          (Naming.back-forth N z ⁻¹)
          (copy-⊒ R (f z) (Ns z))))

  -- Mathematical shape: every named tree lies below Ω.
  above : {Ψ : Operator D} (R : Reflection Q Ψ) (x : Closed C D) →
    Named R x → x ⊏ Ω R
  above R x n = ⊑-⊏-trans (copy-⊒ R x n) (unbounded R (copy R x n))

  ----------------------------------------------------------------------
  -- The boundary is excluded from the child

  -- Mathematical shape: Ω ⋢ w for every child tree w. Every child tree lies
  -- strictly below Ω, so none reaches it.
  excluded : {Ψ : Operator D} (R : Reflection Q Ψ) (w : ChildTrees R) →
    ¬ (Ω R ⊑ embed (codes R) w)
  excluded R w q = ⊏-irrefl (Ω R) (⊑-⊏-trans q (unbounded R w))

  -- Mathematical shape: ¬ Named R Ω. Everything named in the child lies
  -- below Ω, so Ω is no named tree.
  boundary-unnamed : {Ψ : Operator D} (R : Reflection Q Ψ) →
    ¬ (Named R (Ω R))
  boundary-unnamed R n = ⊏-irrefl (Ω R) (above R (Ω R) n)

  -- Each child code names its own interpretation.
  self-naming : {Ψ : Operator D} (R : Reflection Q Ψ)
    (a : D (Reflection.carrier R)) →
    Naming R (Closure.interpret (Reflection.closure R) a)
  self-naming R a = record
    { code = a ; back = id ; forth = id ; back-forth = λ z → refl }

  -- A child code interpreted as c names c.
  name-naming : {Ψ : Operator D} (R : Reflection Q Ψ) {c : C} →
    Name (Closure.interpret (Reflection.closure R)) c → Naming R c
  name-naming R (a , refl) = self-naming R a

  -- Every child tree is named, label by label.
  embedded-named : {Ψ : Operator D} (R : Reflection Q Ψ)
    (w : ChildTrees R) → Named R (embed (codes R) w)
  embedded-named R (sup a f) =
    self-naming R a , (λ y → embedded-named R (f y))

  -- Mathematical shape: no child code corresponds to the tree code of the
  -- child's own family. The children of Ω are named, so a naming of its root
  -- would make Ω a named tree.
  tree-unnamed : {Ψ : Operator D} (R : Reflection Q Ψ) →
    ¬ (Naming R (Formers.tree Q (codes R)))
  tree-unnamed R N =
    boundary-unnamed R (N , (λ q → embedded-named R (unfold (codes R) q)))

  -- A child code interpreted as the carrier: the child's tree name for that
  -- code, with the child's codes as members, names the tree code of the
  -- child's own family.
  tree-naming : {Ψ : Operator D} (R : Reflection Q Ψ)
    (x : D (Reflection.carrier R)) →
    Closure.interpret (Reflection.closure R) x ＝ Reflection.carrier R →
    Naming R (Formers.tree Q (codes R))
  tree-naming R x e =
    let name = Closure.tree (Reflection.closure R)
                 (x , (λ y → transport id (ap D e) y))
        p = pr₂ name
            ∙ ap (Formers.tree Q)
                (moved-family D e (Closure.interpret (Reflection.closure R)))
    in record
      { code = pr₁ name
      ; back = transport id (ap D p)
      ; forth = transport id (ap D p ⁻¹)
      ; back-forth = back-and-forth-transport id (ap D p)
      }

  -- Mathematical shape: ¬ Σ x. interpret x ＝ r. No child code is
  -- interpreted as the carrier.
  carrier-unnamed : {Ψ : Operator D} (R : Reflection Q Ψ) →
    ¬ (Name (Closure.interpret (Reflection.closure R))
         (Reflection.carrier R))
  carrier-unnamed R (x , e) = tree-unnamed R (tree-naming R x e)

  -- Mathematical shape: Ψ (map F) ≠ (r , interpret) for every child family
  -- F. An operator the child is closed under never returns the child's own
  -- codes: their boundary, Ω itself, would lie below Ω.
  codes-unreturned : {Ψ : Operator D} (R : Reflection Q Ψ)
    (F : Family (Decode D (Closure.interpret (Reflection.closure R)))) →
    ¬ (Ψ (map D (Closure.interpret (Reflection.closure R)) F) ＝ codes R)
  codes-unreturned R F e =
    ⊏-irrefl (Ω R) (transport (λ P → boundary P ⊏ Ω R) e (closed R F))

  -- Mathematical shape: ¬ Π F. Ω_{(r , interpret)} ⊏ Ω. Closure under an
  -- operator is a condition: the constant operator returning the child's
  -- own codes has Ω itself as its boundary, at the unit family.
  not-closed : {Ψ : Operator D} (R : Reflection Q Ψ) →
    ¬ ((F : Family (Decode D (Closure.interpret (Reflection.closure R)))) →
        boundary (codes R) ⊏ Ω R)
  not-closed R bounds = ⊏-irrefl (Ω R) (bounds (unit-family R))

  ----------------------------------------------------------------------
  -- The child trees bound their families

  -- The child trees of R with the families indexed by the points of child
  -- codes: an instance of Regularity. The bound of a family at a code a is
  -- the child tree at a over the family.
  child-trees-bound-families : {Ψ : Operator D} (R : Reflection Q Ψ) →
    Bounded-Families (ChildTrees R)
      (λ v w → embed (codes R) v ⊏ embed (codes R) w)
      (λ v w → embed (codes R) v ⊑ embed (codes R) w)
      (D (Reflection.carrier R))
      (λ a → D (Closure.interpret (Reflection.closure R) a))
  child-trees-bound-families R = record
    { strict-is-irreflexive = λ v → ⊏-irrefl (embed (codes R) v)
    ; strict-then-weak = ⊏-⊑-trans
    ; upper-bound = λ a F →
        sup a F , (λ y → under y (⊑-refl (embed (codes R) (F y))))
    }

  ----------------------------------------------------------------------
  -- Child trees from decoding up to retraction

  -- With the formers decoded up to retraction, the child's constant codes
  -- build child trees: a leaf at the empty code, with no children; a
  -- successor at the unit code, one tree at every point; a fork at the two
  -- code, one tree for each point of 𝟚; and a spread at a code naming c, one
  -- tree at each point of c. Each lies strictly above the trees it is built
  -- over (successor-above, fork-left, fork-right, spread-above); the
  -- successor's position is the point of the unit code (unit-point).

  module _ (retracts : Retracts Q) {Ψ : Operator D} (R : Reflection Q Ψ)
    where

    leaf : ChildTrees R
    leaf =
      sup (pr₁ (Closure.empty (Reflection.closure R)))
        (λ y →
          𝟘-elim
            (Retracts.empty retracts
              (transport id
                (ap D (pr₂ (Closure.empty (Reflection.closure R)))) y)))

    successor : ChildTrees R → ChildTrees R
    successor v =
      sup (pr₁ (Closure.unit (Reflection.closure R))) (λ y → v)

    -- The point of the child's unit code, read back from the parent's.
    unit-point : D (Closure.interpret (Reflection.closure R)
      (pr₁ (Closure.unit (Reflection.closure R))))
    unit-point =
      transport id (ap D (pr₂ (Closure.unit (Reflection.closure R))) ⁻¹)
        (Retracts.point retracts)

    -- Mathematical shape: embed v ⊏ embed (successor v), at the point of
    -- the unit code.
    successor-above : (v : ChildTrees R) →
      embed (codes R) v ⊏ embed (codes R) (successor v)
    successor-above v = under unit-point (⊑-refl (embed (codes R) v))

    -- A point of the two code read as a point of 𝟚; the point at a point of
    -- 𝟚 reads back as it.
    side :
      D (Closure.interpret (Reflection.closure R)
          (pr₁ (Closure.two (Reflection.closure R)))) →
      𝟚
    side t =
      out (Retracts.two retracts)
        (transport id (ap D (pr₂ (Closure.two (Reflection.closure R)))) t)

    at : 𝟚 →
      D (Closure.interpret (Reflection.closure R)
          (pr₁ (Closure.two (Reflection.closure R))))
    at b =
      transport id (ap D (pr₂ (Closure.two (Reflection.closure R))) ⁻¹)
        (into (Retracts.two retracts) b)

    side-at : (b : 𝟚) → side (at b) ＝ b
    side-at b =
      ap (out (Retracts.two retracts))
        (back-and-forth-transport id
          (ap D (pr₂ (Closure.two (Reflection.closure R))))
          (into (Retracts.two retracts) b))
      ∙ out-into (Retracts.two retracts) b

    -- The fork of v and w: v at the point read as ₁, w at the point read
    -- as ₀.
    fork : ChildTrees R → ChildTrees R → ChildTrees R
    fork v w =
      sup (pr₁ (Closure.two (Reflection.closure R)))
        (λ t → choose (side t) w v)

    -- Mathematical shape: embed v ⊏ embed (fork v w) and
    -- embed w ⊏ embed (fork v w).
    fork-left : (v w : ChildTrees R) →
      embed (codes R) v ⊏ embed (codes R) (fork v w)
    fork-left v w =
      under (at ₁)
        (transport
          (λ s → embed (codes R) v ⊑ embed (codes R) (choose s w v))
          (side-at ₁ ⁻¹) (⊑-refl (embed (codes R) v)))

    fork-right : (v w : ChildTrees R) →
      embed (codes R) w ⊏ embed (codes R) (fork v w)
    fork-right v w =
      under (at ₀)
        (transport
          (λ s → embed (codes R) w ⊑ embed (codes R) (choose s w v))
          (side-at ₀ ⁻¹) (⊑-refl (embed (codes R) w)))

    spread : (c : C) → Name (Closure.interpret (Reflection.closure R)) c →
      (D c → ChildTrees R) → ChildTrees R
    spread c n vs =
      sup (pr₁ n) (λ q → vs (transport id (ap D (pr₂ n)) q))

    -- Mathematical shape: embed (vs x) ⊏ embed (spread c n vs).
    spread-above : (c : C)
      (n : Name (Closure.interpret (Reflection.closure R)) c)
      (vs : D c → ChildTrees R) (x : D c) →
      embed (codes R) (vs x) ⊏ embed (codes R) (spread c n vs)
    spread-above c n vs x =
      under (transport id (ap D (pr₂ n) ⁻¹) x)
        (transport
          (λ z → embed (codes R) (vs x) ⊑ embed (codes R) (vs z))
          (back-and-forth-transport id (ap D (pr₂ n)) x ⁻¹)
          (⊑-refl (embed (codes R) (vs x))))

    -- The class of a child code c: the child family over the two code with
    -- the empty code at the point read as ₀ and c at ₁. Its image's trees
    -- are the trees branching over c, with leaves at the empty code.
    child-class : D (Reflection.carrier R) →
      Family (Decode D (Closure.interpret (Reflection.closure R)))
    child-class c =
      pr₁ (Closure.two (Reflection.closure R)) ,
      (λ t →
        choose (side t) (pr₁ (Closure.empty (Reflection.closure R))) c)

    -- Mathematical shape: Ω_{class c} ⊏ Ω, the image of a child family.
    child-class-below : (c : D (Reflection.carrier R)) →
      boundary
        (map D (Closure.interpret (Reflection.closure R)) (child-class c))
      ⊏ Ω R
    child-class-below c = family-below R (child-class c)
