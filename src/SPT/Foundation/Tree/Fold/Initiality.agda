{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Tree.Fold.Initiality where

-- Pointwise initiality of induction on the open trees of any signature, with
-- no extensionality. Write h and n for methods of induction at a motive P,
-- at holes and at nodes (Tree.Fold). A valuation v of a motive Q is lax for
-- them along a relation C when it is related to h at every hole, and at
-- every node to n at any hypotheses related to v at the children (`Lax`).
-- Such a valuation is related to induction at every tree:
--
--   Lax Q P C v h n → C j t (v t) (induction P h n t)
--                                              (`induction-unique-rel`).
--
-- Instances: the fundamental theorem, related methods have related
-- inductions (`Relational`, `induction-rel`); uniqueness, a valuation
-- satisfying the computation equations of congruent node methods is their
-- induction, which satisfies them by refl (`Congruent`, `Homomorphic`,
-- `induction-unique`, `induction-homomorphic`); and fusion along a map of
-- motives (`Carries`, `induction-fusion`). The hypotheses of a node method
-- are one function on the node's positions, so extensionality there makes
-- every node method congruent (`congruent`).
--
-- The generated part of an algebra of a Dybjer–Setzer description is the
-- closed trees of one signature (IR.Generated); its pointwise
-- initiality is the instance there (IR.Generated.Initiality).
--
-- The fold form. Tree.Fold's fold is induction at the constant motive of the
-- carrier, with the algebra's node operation as its method there
-- (`node-method`), so the theorems above hold of folds. The fold satisfies
-- the computation equations of the algebra by refl (`fold-homomorphic`); a
-- valuation satisfying them is the fold at every tree when the node method
-- is congruent (`fold-unique`), and with no congruence it is related to the
-- fold by every relation that the algebra's operations preserve, with
-- identity at holes (`fold-unique-rel`). A congruent node action (Tree.Fold's
-- `Congruent-Node-Action`) gives a congruent node method
-- (`node-method-congruent`); the converse needs a child family at every
-- operation, so `fold-unique` keeps the weaker hypothesis. Together these are
-- the free completion of the holes under the operations at such an algebra
-- (`Free-Completion`, `free-completion`). Under extensionality for valuations
-- (`ValuationΠExt`) the valuation is the fold as a function
-- (`fold-unique-map`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Tree
open import SPT.Foundation.Tree.Fold using
  ( Algebra; on-hole; on-node; Congruent-Node-Action; node-method; fold
  ; induction
  )
open import SPT.Foundation.Tree.Fold.Relation using
  (Relational-Algebra; on-hole-rel; on-node-rel)

------------------------------------------------------------------------
-- The lax law

-- The lax law of a valuation v of Q for the methods h and n of P along C:
-- at a hole, v is related to h; at a node, n at any hypotheses related to v
-- at the children is related to v at the node. No reflexivity, transitivity
-- or congruence of C is asked.

module _
  {ℓj ℓo ℓp ℓx μ ν ρ : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx}
  (Q : (j : Judgment S) → Tree S X j → Set μ)
  (P : (j : Judgment S) → Tree S X j → Set ν)
  (C : (j : Judgment S) (tree : Tree S X j) → Q j tree → P j tree → Set ρ)
  where

  record Lax
    (v : {j : Judgment S} (tree : Tree S X j) → Q j tree)
    (h : {j : Judgment S} (x : X j) → P j (hole x))
    (n : {j : Judgment S} (o : Op S j)
      (child : (p : Pos S o) → Tree S X (boundary S o p)) →
      ((p : Pos S o) → P (boundary S o p) (child p)) → P j (node o child))
    : Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx ⊔ ν ⊔ ρ) where
    field
      at-hole : {j : Judgment S} (x : X j) → C j (hole x) (v (hole x)) (h x)
      at-node : {j : Judgment S} (o : Op S j)
        (child : (p : Pos S o) → Tree S X (boundary S o p))
        (k : (p : Pos S o) → P (boundary S o p) (child p)) →
        ((p : Pos S o) → C (boundary S o p) (child p) (v (child p)) (k p)) →
        C j (node o child) (v (node o child)) (n o child k)

------------------------------------------------------------------------
-- Relational uniqueness

-- Induction at the motive relating v to induction: its hypotheses at a
-- node are the relatedness the law asks for, at induction's own values.

module _
  {ℓj ℓo ℓp ℓx μ ν ρ : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx}
  (Q : (j : Judgment S) → Tree S X j → Set μ)
  (P : (j : Judgment S) → Tree S X j → Set ν)
  (C : (j : Judgment S) (tree : Tree S X j) → Q j tree → P j tree → Set ρ)
  (v : {j : Judgment S} (tree : Tree S X j) → Q j tree)
  (h : {j : Judgment S} (x : X j) → P j (hole x))
  (n : {j : Judgment S} (o : Op S j)
    (child : (p : Pos S o) → Tree S X (boundary S o p)) →
    ((p : Pos S o) → P (boundary S o p) (child p)) → P j (node o child))
  where

  induction-unique-rel :
    Lax Q P C v h n → {j : Judgment S} (tree : Tree S X j) →
    C j tree (v tree) (induction P h n tree)
  induction-unique-rel law =
    induction (λ j tree → C j tree (v tree) (induction P h n tree))
      (Lax.at-hole law)
      (λ o child related →
        Lax.at-node law o child (λ p → induction P h n (child p)) related)

------------------------------------------------------------------------
-- The fundamental theorem

-- Methods related at related hypotheses have related inductions; the
-- values of an induction at the children are its hypotheses there.

module _
  {ℓj ℓo ℓp ℓx μ ν ρ : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx}
  (Q : (j : Judgment S) → Tree S X j → Set μ)
  (P : (j : Judgment S) → Tree S X j → Set ν)
  (C : (j : Judgment S) (tree : Tree S X j) → Q j tree → P j tree → Set ρ)
  where

  record Relational
    (hq : {j : Judgment S} (x : X j) → Q j (hole x))
    (nq : {j : Judgment S} (o : Op S j)
      (child : (p : Pos S o) → Tree S X (boundary S o p)) →
      ((p : Pos S o) → Q (boundary S o p) (child p)) → Q j (node o child))
    (hp : {j : Judgment S} (x : X j) → P j (hole x))
    (np : {j : Judgment S} (o : Op S j)
      (child : (p : Pos S o) → Tree S X (boundary S o p)) →
      ((p : Pos S o) → P (boundary S o p) (child p)) → P j (node o child))
    : Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx ⊔ μ ⊔ ν ⊔ ρ) where
    field
      at-hole : {j : Judgment S} (x : X j) → C j (hole x) (hq x) (hp x)
      at-node : {j : Judgment S} (o : Op S j)
        (child : (p : Pos S o) → Tree S X (boundary S o p))
        (g : (p : Pos S o) → Q (boundary S o p) (child p))
        (k : (p : Pos S o) → P (boundary S o p) (child p)) →
        ((p : Pos S o) → C (boundary S o p) (child p) (g p) (k p)) →
        C j (node o child) (nq o child g) (np o child k)

module _
  {ℓj ℓo ℓp ℓx μ ν ρ : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx}
  (Q : (j : Judgment S) → Tree S X j → Set μ)
  (P : (j : Judgment S) → Tree S X j → Set ν)
  (C : (j : Judgment S) (tree : Tree S X j) → Q j tree → P j tree → Set ρ)
  (hq : {j : Judgment S} (x : X j) → Q j (hole x))
  (nq : {j : Judgment S} (o : Op S j)
    (child : (p : Pos S o) → Tree S X (boundary S o p)) →
    ((p : Pos S o) → Q (boundary S o p) (child p)) → Q j (node o child))
  (hp : {j : Judgment S} (x : X j) → P j (hole x))
  (np : {j : Judgment S} (o : Op S j)
    (child : (p : Pos S o) → Tree S X (boundary S o p)) →
    ((p : Pos S o) → P (boundary S o p) (child p)) → P j (node o child))
  where

  induction-rel :
    Relational Q P C hq nq hp np → {j : Judgment S} (tree : Tree S X j) →
    C j tree (induction Q hq nq tree) (induction P hp np tree)
  induction-rel related =
    induction-unique-rel Q P C (induction Q hq nq) hp np
      (record
        { at-hole = Relational.at-hole related
        ; at-node = λ o child k r →
            Relational.at-node related o child
              (λ p → induction Q hq nq (child p)) k r
        })

------------------------------------------------------------------------
-- Uniqueness

-- A node method is congruent when hypotheses agreeing at every position
-- give the same value; the hypotheses are functions on the positions, so
-- this is a genuine hypothesis. A valuation satisfying the computation
-- equations of methods with a congruent node method is their induction at
-- every tree, and induction satisfies them by refl.

module _
  {ℓj ℓo ℓp ℓx ν : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx}
  (P : (j : Judgment S) → Tree S X j → Set ν)
  where

  Identical : (j : Judgment S) (tree : Tree S X j) → P j tree → P j tree →
    Set ν
  Identical j tree x y = x ＝ y

  Congruent :
    ({j : Judgment S} (o : Op S j)
      (child : (p : Pos S o) → Tree S X (boundary S o p)) →
      ((p : Pos S o) → P (boundary S o p) (child p)) → P j (node o child)) →
    Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx ⊔ ν)
  Congruent n =
    {j : Judgment S} (o : Op S j)
    (child : (p : Pos S o) → Tree S X (boundary S o p))
    (g k : (p : Pos S o) → P (boundary S o p) (child p)) →
    ((p : Pos S o) → g p ＝ k p) → n o child g ＝ n o child k

  record Homomorphic
    (v : {j : Judgment S} (tree : Tree S X j) → P j tree)
    (h : {j : Judgment S} (x : X j) → P j (hole x))
    (n : {j : Judgment S} (o : Op S j)
      (child : (p : Pos S o) → Tree S X (boundary S o p)) →
      ((p : Pos S o) → P (boundary S o p) (child p)) → P j (node o child))
    : Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx ⊔ ν) where
    field
      at-hole : {j : Judgment S} (x : X j) → v (hole x) ＝ h x
      at-node : {j : Judgment S} (o : Op S j)
        (child : (p : Pos S o) → Tree S X (boundary S o p)) →
        v (node o child) ＝ n o child (λ p → v (child p))

module _
  {ℓj ℓo ℓp ℓx ν : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx}
  (P : (j : Judgment S) → Tree S X j → Set ν)
  (v : {j : Judgment S} (tree : Tree S X j) → P j tree)
  (h : {j : Judgment S} (x : X j) → P j (hole x))
  (n : {j : Judgment S} (o : Op S j)
    (child : (p : Pos S o) → Tree S X (boundary S o p)) →
    ((p : Pos S o) → P (boundary S o p) (child p)) → P j (node o child))
  where

  induction-unique :
    Congruent P n → Homomorphic P v h n → {j : Judgment S}
    (tree : Tree S X j) → v tree ＝ induction P h n tree
  induction-unique congruence equations =
    induction-unique-rel P P (Identical P) v h n
      (record
        { at-hole = Homomorphic.at-hole equations
        ; at-node = λ o child k r →
            Homomorphic.at-node equations o child
            ∙ congruence o child (λ p → v (child p)) k r
        })

module _
  {ℓj ℓo ℓp ℓx ν : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx}
  (P : (j : Judgment S) → Tree S X j → Set ν)
  (h : {j : Judgment S} (x : X j) → P j (hole x))
  (n : {j : Judgment S} (o : Op S j)
    (child : (p : Pos S o) → Tree S X (boundary S o p)) →
    ((p : Pos S o) → P (boundary S o p) (child p)) → P j (node o child))
  where

  induction-homomorphic : Homomorphic P (induction P h n) h n
  induction-homomorphic = record
    { at-hole = λ x → refl
    ; at-node = λ o child → refl
    }

------------------------------------------------------------------------
-- Congruence under extensionality

-- Under extensionality for families over the positions, hypotheses
-- agreeing at every position are identical, so every node method is
-- congruent.

module _
  {ℓj ℓo ℓp ℓx ν : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx}
  (extensionality : (A : Set ℓp) (Y : A → Set ν) → FunExt A Y)
  (P : (j : Judgment S) → Tree S X j → Set ν)
  where

  congruent :
    (n : {j : Judgment S} (o : Op S j)
      (child : (p : Pos S o) → Tree S X (boundary S o p)) →
      ((p : Pos S o) → P (boundary S o p) (child p)) → P j (node o child)) →
    Congruent P n
  congruent n o child g k r =
    ap (n o child)
      (extensionality (Pos S o) (λ p → P (boundary S o p) (child p)) g k r)

------------------------------------------------------------------------
-- Fusion

-- A map of motives that carries the methods of one to methods of the
-- other with a congruent node method, at the mapped hypotheses, carries
-- induction to induction: the two are related by the graph of the map.

module _
  {ℓj ℓo ℓp ℓx ν ν′ : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx}
  (P : (j : Judgment S) → Tree S X j → Set ν)
  (P′ : (j : Judgment S) → Tree S X j → Set ν′)
  (f : {j : Judgment S} (tree : Tree S X j) → P j tree → P′ j tree)
  where

  Graph : (j : Judgment S) (tree : Tree S X j) → P j tree → P′ j tree →
    Set ν′
  Graph j tree x y = f tree x ＝ y

  record Carries
    (h : {j : Judgment S} (x : X j) → P j (hole x))
    (n : {j : Judgment S} (o : Op S j)
      (child : (p : Pos S o) → Tree S X (boundary S o p)) →
      ((p : Pos S o) → P (boundary S o p) (child p)) → P j (node o child))
    (h′ : {j : Judgment S} (x : X j) → P′ j (hole x))
    (n′ : {j : Judgment S} (o : Op S j)
      (child : (p : Pos S o) → Tree S X (boundary S o p)) →
      ((p : Pos S o) → P′ (boundary S o p) (child p)) → P′ j (node o child))
    : Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx ⊔ ν ⊔ ν′) where
    field
      at-hole : {j : Judgment S} (x : X j) → f (hole x) (h x) ＝ h′ x
      at-node : {j : Judgment S} (o : Op S j)
        (child : (p : Pos S o) → Tree S X (boundary S o p))
        (k : (p : Pos S o) → P (boundary S o p) (child p)) →
        f (node o child) (n o child k)
          ＝ n′ o child (λ p → f (child p) (k p))

module _
  {ℓj ℓo ℓp ℓx ν ν′ : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx}
  (P : (j : Judgment S) → Tree S X j → Set ν)
  (P′ : (j : Judgment S) → Tree S X j → Set ν′)
  (f : {j : Judgment S} (tree : Tree S X j) → P j tree → P′ j tree)
  (h : {j : Judgment S} (x : X j) → P j (hole x))
  (n : {j : Judgment S} (o : Op S j)
    (child : (p : Pos S o) → Tree S X (boundary S o p)) →
    ((p : Pos S o) → P (boundary S o p) (child p)) → P j (node o child))
  (h′ : {j : Judgment S} (x : X j) → P′ j (hole x))
  (n′ : {j : Judgment S} (o : Op S j)
    (child : (p : Pos S o) → Tree S X (boundary S o p)) →
    ((p : Pos S o) → P′ (boundary S o p) (child p)) → P′ j (node o child))
  where

  induction-fusion :
    Congruent P′ n′ → Carries P P′ f h n h′ n′ → {j : Judgment S}
    (tree : Tree S X j) →
    f tree (induction P h n tree) ＝ induction P′ h′ n′ tree
  induction-fusion congruence carries =
    induction-unique-rel P P′ (Graph P P′ f) (induction P h n) h′ n′
      (record
        { at-hole = Carries.at-hole carries
        ; at-node = λ o child k r →
            Carries.at-node carries o child
              (λ p → induction P h n (child p))
            ∙ congruence o child
                (λ p → f (child p) (induction P h n (child p))) k r
        })

------------------------------------------------------------------------
-- The fold form

-- Tree.Fold's fold is induction at the constant motive of the carrier with
-- the algebra's node method, so uniqueness, its relational form and the
-- free completion are the theorems above at that motive.

module _
  {ℓj ℓo ℓp ℓx ℓd : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} {D : Judgment S → Set ℓd}
  (algebra : Algebra S X D)
  where

  -- A congruent node action gives a congruent node method, at every child
  -- family.
  node-method-congruent : Congruent-Node-Action D (on-node algebra) →
    Congruent (λ j tree → D j) (node-method algebra)
  node-method-congruent congruence o child g k agree = congruence o agree

  fold-homomorphic :
    Homomorphic (λ j tree → D j) (fold algebra) (on-hole algebra)
      (node-method algebra)
  fold-homomorphic = record
    { at-hole = λ x → refl
    ; at-node = λ o child → refl
    }

  fold-unique :
    (value : {j : Judgment S} (tree : Tree S X j) → D j) →
    Congruent (λ j tree → D j) (node-method algebra) →
    Homomorphic (λ j tree → D j) value (on-hole algebra)
      (node-method algebra) →
    {j : Judgment S} (tree : Tree S X j) → value tree ＝ fold algebra tree
  fold-unique value congruence equations tree =
    induction-unique (λ j tree → D j) value (on-hole algebra)
      (node-method algebra) congruence equations tree

  -- With no congruence: a relation C on values that the algebra's
  -- operations preserve, with identity at holes, relates a valuation
  -- satisfying the algebra's equations to the fold at every tree.
  fold-unique-rel :
    {ℓc : Level} {C : {j : Judgment S} → D j → D j → Set ℓc} →
    Relational-Algebra _＝_ C algebra algebra →
    (value : {j : Judgment S} (tree : Tree S X j) → D j) →
    Homomorphic (λ j tree → D j) value (on-hole algebra)
      (node-method algebra) →
    {j : Judgment S} (tree : Tree S X j) → C (value tree) (fold algebra tree)
  fold-unique-rel {ℓc} {C} related value equations tree =
    induction-unique-rel (λ j tree → D j) (λ j tree → D j) (λ j tree → C)
      value (on-hole algebra) (node-method algebra)
      (record
        { at-hole = λ x →
            transport (λ d → C d (on-hole algebra x))
              (Homomorphic.at-hole equations x ⁻¹)
              (on-hole-rel related refl)
        ; at-node = λ o child k values →
            transport (λ d → C d (node-method algebra o child k))
              (Homomorphic.at-node equations o child ⁻¹)
              (on-node-rel related o values)
        })
      tree

  -- The free completion: a valuation satisfying the algebra's equations,
  -- to which every other such valuation is equal at every tree.
  record Free-Completion : Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx ⊔ ℓd) where
    field
      extend : {j : Judgment S} (tree : Tree S X j) → D j
      computes :
        Homomorphic (λ j tree → D j) extend (on-hole algebra)
          (node-method algebra)
      unique : (value : {j : Judgment S} (tree : Tree S X j) → D j) →
        Homomorphic (λ j tree → D j) value (on-hole algebra)
          (node-method algebra) →
        {j : Judgment S} (tree : Tree S X j) → value tree ＝ extend tree

  free-completion :
    Congruent (λ j tree → D j) (node-method algebra) → Free-Completion
  free-completion congruence = record
    { extend = fold algebra
    ; computes = fold-homomorphic
    ; unique = λ value equations →
        fold-unique value congruence equations
    }

------------------------------------------------------------------------
-- The map form

-- Extensionality for valuations: two valuations agreeing at every tree are
-- identified. It is a hypothesis, never assumed.

ValuationΠExt : {ℓj ℓo ℓp ℓx ℓd : Level} (S : Signature ℓj ℓo ℓp)
  (X : Judgment S → Set ℓx) (D : Judgment S → Set ℓd) →
  Set (ℓj ⊔ ℓo ⊔ ℓp ⊔ ℓx ⊔ ℓd)
ValuationΠExt S X D =
  (left right : {j : Judgment S} → Tree S X j → D j) →
  ({j : Judgment S} (tree : Tree S X j) → left tree ＝ right tree) →
  _＝_ {A = {j : Judgment S} → Tree S X j → D j} left right

module _
  {ℓj ℓo ℓp ℓx ℓd : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} {D : Judgment S → Set ℓd}
  (extensionality : ValuationΠExt S X D) (algebra : Algebra S X D)
  where

  fold-unique-map :
    (value : {j : Judgment S} (tree : Tree S X j) → D j) →
    Congruent (λ j tree → D j) (node-method algebra) →
    Homomorphic (λ j tree → D j) value (on-hole algebra)
      (node-method algebra) →
    _＝_ {A = {j : Judgment S} → Tree S X j → D j} value (fold algebra)
  fold-unique-map value congruence equations =
    extensionality value (fold algebra)
      (fold-unique algebra value congruence equations)
