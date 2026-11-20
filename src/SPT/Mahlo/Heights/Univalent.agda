{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Heights.Univalent where

-- Smallness with unique names from heights regular for relations.
-- Heights.Regular gives the ambient Mahlo rule from heights regular for
-- Φ's stages, where every family of stage codes, given as a function,
-- lies in one child's stage. Here the stages are univalent. At a node the
-- layer of codes of the formers and Φ over the children's univalent stages
-- (`Layer`, `layer-decoding`, with Heights.Stages' `Code`) is completed
-- (Univalent.Completion), so each univalent stage is a small type whose
-- decoding is an embedding (`univalent-stage`):
--
--   univalent-stage (node X f)
--     = the completion of Σ x. Code Φ (univalent-stage (f x)) → Set ℓ.
--
-- A node is regular for relations (`Relationally-Regular`) when it has a
-- child and every code a of its stage, with a family b of codes over a's
-- decoding, lies merely in one child's stage, a's decoding and every
-- member's named there:
--
--   Covered ℓ (Σ z. Name (decoding at f z) (decoding a)
--     × Π y. Name (decoding at f z) (decoding (b y))).
--
-- Given such a child, F's index and members named there form a family of
-- the child's codes decoding to F's (`bounded-members`,
-- `bounded-members-decode`, by extensionality for families of types), and
-- the formers, the identity types and Φ's index and members at F are
-- layer codes over the child (`product-layer`, `sum-layer`, `tree-layer`,
-- `identity-layer`, `result-layer`, `branch-layer`). The stage names a
-- code covered by layer codes (Univalent.Completion's
-- `names-in-the-completion`), so the child is needed only merely. So at a
-- node regular for relations the univalent stage is a closure of Φ
-- (`regular-closure`) with unique names
-- (`regular-closure-has-unique-names`), and heights regular for relations
-- give smallness with unique names, with no choice, excluded middle or
-- resizing (`relational-passage`):
--
--   Type-Hypotheses ℓ → Completions ℓ (Set ℓ) →
--     (Π Φ. Σ X f. Relationally-Regular Φ X f) → Univalent-Smallness ℓ.
--
-- Inside a univalent stage a family of members is a function by unique
-- choice, so only the bound is asked for. Regularity for relations is a
-- condition: the node over one leaf is not regular, since the leaf's stage
-- completes an empty layer (`node-over-a-leaf-is-irregular`). Whether the
-- Mahlo rule gives heights regular for relations, which would give the
-- rule with unique names, is declared and not inhabited
-- (`Relational-Regularity`). At a node regular for functions the witnesses
-- of a total relation upward closed along ⊏ are never the decoding of a
-- stage code (Heights.Regular's `witnesses-are-not-decodings`), so
-- collecting all witnesses does not give it.

open import SPT.Base
open import SPT.Foundation.Covers using
  (Covered; map-covered; bind-covered; covered-is-not-refuted)
open import SPT.Foundation.Extensionality using (FunExt)
import SPT.Foundation.Tree as Tree
import SPT.Mahlo.Ambient as Ambient
import SPT.Mahlo.Specification as Specification
open import SPT.Mahlo.DS.Naming.Trees using (pair)
open import SPT.Mahlo.DS.Realization.Family using (cast)
open import SPT.Mahlo.DS.Univalent.Completion using
  ( Completion; Completions; Has-Unique-Names; carried
  ; names-in-the-completion )
open import SPT.Mahlo.DS.Univalent.Smallness using
  (Univalent-Smallness; smallness-of-reflector)
open import SPT.Mahlo.DS.Univalent.Types using
  (Type-Hypotheses; type-parent; reflector-of-unique-names)
open import SPT.Mahlo.Heights using (leaf)
open import SPT.Mahlo.Heights.Stages using
  ( Code; decode; family; reidentified; rebranched
  ; empty; unit; two; natural; product; sum; tree; result; identity
  ; branch )
open import SPT.OrdinalGeometry.Height.Ordinals using (Height)

------------------------------------------------------------------------
-- Univalent stages

module _ {ℓ : Level} (completions : Completions ℓ (Set ℓ))
  (Φ : Ambient.Operator ℓ) where

  mutual
    -- One layer of codes of the formers and Φ over the univalent stages
    -- of a node's children.
    Layer : Height ℓ → Set ℓ
    Layer (Tree.hole ())
    Layer (Tree.node X f) =
      Σ X (λ x →
        Code Φ (Completion.completed (univalent-stage (f x)))
          (Completion.decode (univalent-stage (f x))))

    layer-decoding : (t : Height ℓ) → Layer t → Set ℓ
    layer-decoding (Tree.hole ())
    layer-decoding (Tree.node X f) (x , c) = decode c

    -- The completion of the layer.
    univalent-stage : (t : Height ℓ) → Completion (layer-decoding t)
    univalent-stage t = completions (Layer t) (layer-decoding t)

  -- Mathematical shape: a child, and for every code a of the stage at
  -- node X f and family b of its codes over a's decoding, merely a child
  -- z whose stage names a's decoding and every member's:
  --
  --   Covered ℓ (Σ z. Name (decoding at f z) (decoding a)
  --     × Π y. Name (decoding at f z) (decoding (b y))).
  record Relationally-Regular (X : Set ℓ) (f : X → Height ℓ) :
    Set (lsuc ℓ) where
    field
      point : X
      bound :
        (a : Completion.completed (univalent-stage (Tree.node X f)))
        (b : Completion.decode (univalent-stage (Tree.node X f)) a →
          Completion.completed (univalent-stage (Tree.node X f))) →
        Covered ℓ
          (Σ X (λ z →
            Specification.Name (Completion.decode (univalent-stage (f z)))
              (Completion.decode (univalent-stage (Tree.node X f)) a)
            × ((y : Completion.decode (univalent-stage (Tree.node X f)) a) →
              Specification.Name
                (Completion.decode (univalent-stage (f z)))
                (Completion.decode (univalent-stage (Tree.node X f))
                  (b y)))))

------------------------------------------------------------------------
-- Layer codes over a bounding child

-- A family F of codes of the stage at node X f, and a child whose stage
-- names F's index and members: a point of Relationally-Regular's bound.

module _ {ℓ : Level} (completions : Completions ℓ (Set ℓ))
  (Φ : Ambient.Operator ℓ) (X : Set ℓ) (f : X → Height ℓ)
  (F :
    Specification.Family
      (Specification.Decode (λ (A : Set ℓ) → A)
        (Completion.decode
          (univalent-stage completions Φ (Tree.node X f)))))
  (w :
    Σ X (λ z →
      Specification.Name
        (Completion.decode (univalent-stage completions Φ (f z)))
        (Completion.decode (univalent-stage completions Φ (Tree.node X f))
          (pr₁ F))
      × ((y :
          Completion.decode (univalent-stage completions Φ (Tree.node X f))
            (pr₁ F)) →
        Specification.Name
          (Completion.decode (univalent-stage completions Φ (f z)))
          (Completion.decode
            (univalent-stage completions Φ (Tree.node X f)) (pr₂ F y)))))
  where

  -- F's members at the points of the child's code of F's index: codes of
  -- the child's stage.
  bounded-members :
    Completion.decode (univalent-stage completions Φ (f (pr₁ w)))
      (pr₁ (pr₁ (pr₂ w))) →
    Completion.completed (univalent-stage completions Φ (f (pr₁ w)))
  bounded-members x = pr₁ (pr₂ (pr₂ w) (cast (pr₂ (pr₁ (pr₂ w))) x))

  -- Mathematical shape: the child's family decodes to F's.
  bounded-members-decode :
    (families : (X : Set ℓ) → FunExt X (λ _ → Set ℓ)) →
    _＝_ {A = Specification.Family (λ (A : Set ℓ) → A)}
      ( Completion.decode (univalent-stage completions Φ (f (pr₁ w)))
          (pr₁ (pr₁ (pr₂ w)))
      , (λ x →
          Completion.decode (univalent-stage completions Φ (f (pr₁ w)))
            (bounded-members x)))
      (Specification.map (λ (A : Set ℓ) → A)
        (Completion.decode (univalent-stage completions Φ (Tree.node X f)))
        F)
  bounded-members-decode families =
    family families (pr₂ (pr₁ (pr₂ w)))
      (λ x → pr₂ (pr₂ (pr₂ w) (cast (pr₂ (pr₁ (pr₂ w))) x)))

  -- The layer codes of the formers and of Φ at F over the child, with
  -- their decodings.

  product-layer : (families : (X : Set ℓ) → FunExt X (λ _ → Set ℓ)) →
    Specification.Name (layer-decoding completions Φ (Tree.node X f))
      (Specification.Formers.product (Ambient.formers ℓ)
        (Specification.map (λ (A : Set ℓ) → A)
          (Completion.decode
            (univalent-stage completions Φ (Tree.node X f)))
          F))
  product-layer families =
    (pr₁ w , product (pr₁ (pr₁ (pr₂ w))) bounded-members) ,
    ap (Specification.Formers.product (Ambient.formers ℓ))
      (bounded-members-decode families)

  sum-layer : (families : (X : Set ℓ) → FunExt X (λ _ → Set ℓ)) →
    Specification.Name (layer-decoding completions Φ (Tree.node X f))
      (Specification.Formers.sum (Ambient.formers ℓ)
        (Specification.map (λ (A : Set ℓ) → A)
          (Completion.decode
            (univalent-stage completions Φ (Tree.node X f)))
          F))
  sum-layer families =
    (pr₁ w , sum (pr₁ (pr₁ (pr₂ w))) bounded-members) ,
    ap (Specification.Formers.sum (Ambient.formers ℓ))
      (bounded-members-decode families)

  tree-layer : (families : (X : Set ℓ) → FunExt X (λ _ → Set ℓ)) →
    Specification.Name (layer-decoding completions Φ (Tree.node X f))
      (Specification.Formers.tree (Ambient.formers ℓ)
        (Specification.map (λ (A : Set ℓ) → A)
          (Completion.decode
            (univalent-stage completions Φ (Tree.node X f)))
          F))
  tree-layer families =
    (pr₁ w , tree (pr₁ (pr₁ (pr₂ w))) bounded-members) ,
    ap (Specification.Formers.tree (Ambient.formers ℓ))
      (bounded-members-decode families)

  identity-layer :
    (x y :
      Completion.decode (univalent-stage completions Φ (Tree.node X f))
        (pr₁ F)) →
    Specification.Name (layer-decoding completions Φ (Tree.node X f))
      (Specification.Formers.identity (Ambient.formers ℓ)
        (Completion.decode (univalent-stage completions Φ (Tree.node X f))
          (pr₁ F))
        x y)
  identity-layer x y =
    ( pr₁ w
    , identity (pr₁ (pr₁ (pr₂ w)))
        (cast (pr₂ (pr₁ (pr₂ w)) ⁻¹) x) (cast (pr₂ (pr₁ (pr₂ w)) ⁻¹) y) ) ,
    reidentified (pr₂ (pr₁ (pr₂ w))) x y

  result-layer : (families : (X : Set ℓ) → FunExt X (λ _ → Set ℓ)) →
    Specification.Name (layer-decoding completions Φ (Tree.node X f))
      (pr₁
        (Φ (Specification.map (λ (A : Set ℓ) → A)
          (Completion.decode
            (univalent-stage completions Φ (Tree.node X f)))
          F)))
  result-layer families =
    (pr₁ w , result (pr₁ (pr₁ (pr₂ w))) bounded-members) ,
    ap (λ G → pr₁ (Φ G)) (bounded-members-decode families)

  branch-layer : (families : (X : Set ℓ) → FunExt X (λ _ → Set ℓ))
    (j :
      pr₁
        (Φ (Specification.map (λ (A : Set ℓ) → A)
          (Completion.decode
            (univalent-stage completions Φ (Tree.node X f)))
          F))) →
    Specification.Name (layer-decoding completions Φ (Tree.node X f))
      (pr₂
        (Φ (Specification.map (λ (A : Set ℓ) → A)
          (Completion.decode
            (univalent-stage completions Φ (Tree.node X f)))
          F))
        j)
  branch-layer families j =
    ( pr₁ w
    , branch (pr₁ (pr₁ (pr₂ w))) bounded-members
        (cast (ap (λ F → pr₁ (Φ F)) (bounded-members-decode families ⁻¹))
          j) ) ,
    rebranched Φ (bounded-members-decode families) j

------------------------------------------------------------------------
-- The closure at a node regular for relations

module _ {ℓ : Level} (H : Type-Hypotheses ℓ)
  (completions : Completions ℓ (Set ℓ)) (Φ : Ambient.Operator ℓ)
  {X : Set ℓ} {f : X → Height ℓ}
  (regular : Relationally-Regular completions Φ X f) where

  -- Φ's index at F is named in the stage.
  operator-index-in-the-stage :
    (F :
      Specification.Family
        (Specification.Decode (λ (A : Set ℓ) → A)
          (Completion.decode
            (univalent-stage completions Φ (Tree.node X f))))) →
    Specification.Name
      (Completion.decode (univalent-stage completions Φ (Tree.node X f)))
      (pr₁
        (Φ (Specification.map (λ (A : Set ℓ) → A)
          (Completion.decode
            (univalent-stage completions Φ (Tree.node X f)))
          F)))
  operator-index-in-the-stage F =
    names-in-the-completion (type-parent H)
      (univalent-stage completions Φ (Tree.node X f))
      (pr₁
        (Φ (Specification.map (λ (A : Set ℓ) → A)
          (Completion.decode
            (univalent-stage completions Φ (Tree.node X f)))
          F)))
      (map-covered
        (λ w →
          result-layer completions Φ X f F w (Type-Hypotheses.families H))
        (Relationally-Regular.bound regular (pr₁ F) (pr₂ F)))

  -- So is each of its members, read along the index's name.
  operator-members-in-the-stage :
    (F :
      Specification.Family
        (Specification.Decode (λ (A : Set ℓ) → A)
          (Completion.decode
            (univalent-stage completions Φ (Tree.node X f)))))
    (z :
      Completion.decode (univalent-stage completions Φ (Tree.node X f))
        (pr₁ (operator-index-in-the-stage F))) →
    Specification.Name
      (Completion.decode (univalent-stage completions Φ (Tree.node X f)))
      (pr₂
        (Φ (Specification.map (λ (A : Set ℓ) → A)
          (Completion.decode
            (univalent-stage completions Φ (Tree.node X f)))
          F))
        (cast (ap (λ (A : Set ℓ) → A) (pr₂ (operator-index-in-the-stage F)))
          z))
  operator-members-in-the-stage F z =
    names-in-the-completion (type-parent H)
      (univalent-stage completions Φ (Tree.node X f))
      (pr₂
        (Φ (Specification.map (λ (A : Set ℓ) → A)
          (Completion.decode
            (univalent-stage completions Φ (Tree.node X f)))
          F))
        (cast (ap (λ (A : Set ℓ) → A) (pr₂ (operator-index-in-the-stage F)))
          z))
      (map-covered
        (λ w →
          branch-layer completions Φ X f F w (Type-Hypotheses.families H)
            (cast
              (ap (λ (A : Set ℓ) → A) (pr₂ (operator-index-in-the-stage F)))
              z))
        (Relationally-Regular.bound regular (pr₁ F) (pr₂ F)))

  -- Identity types, over the constant family at a code.
  identity-types-in-the-stage :
    (a : Completion.completed (univalent-stage completions Φ (Tree.node X f)))
    (x y :
      Completion.decode (univalent-stage completions Φ (Tree.node X f)) a) →
    Specification.Name
      (Completion.decode (univalent-stage completions Φ (Tree.node X f)))
      (Specification.Formers.identity (Ambient.formers ℓ)
        (Completion.decode (univalent-stage completions Φ (Tree.node X f))
          a)
        x y)
  identity-types-in-the-stage a x y =
    names-in-the-completion (type-parent H)
      (univalent-stage completions Φ (Tree.node X f))
      (Specification.Formers.identity (Ambient.formers ℓ)
        (Completion.decode (univalent-stage completions Φ (Tree.node X f))
          a)
        x y)
      (map-covered
        (λ w → identity-layer completions Φ X f (a , (λ y → a)) w x y)
        (Relationally-Regular.bound regular a (λ y → a)))

  regular-closure :
    Specification.Closure (Ambient.formers ℓ) Φ
      (Completion.completed
        (univalent-stage completions Φ (Tree.node X f)))
  regular-closure = record
    { interpret =
        Completion.decode (univalent-stage completions Φ (Tree.node X f))
    ; empty =
        carried (type-parent H)
          (univalent-stage completions Φ (Tree.node X f))
          (Specification.Formers.empty (Ambient.formers ℓ))
          ((Relationally-Regular.point regular , empty) , refl)
    ; unit =
        carried (type-parent H)
          (univalent-stage completions Φ (Tree.node X f))
          (Specification.Formers.unit (Ambient.formers ℓ))
          ((Relationally-Regular.point regular , unit) , refl)
    ; two =
        carried (type-parent H)
          (univalent-stage completions Φ (Tree.node X f))
          (Specification.Formers.two (Ambient.formers ℓ))
          ((Relationally-Regular.point regular , two) , refl)
    ; natural =
        carried (type-parent H)
          (univalent-stage completions Φ (Tree.node X f))
          (Specification.Formers.natural (Ambient.formers ℓ))
          ((Relationally-Regular.point regular , natural) , refl)
    ; product = λ F →
        names-in-the-completion (type-parent H)
          (univalent-stage completions Φ (Tree.node X f))
          (Specification.Formers.product (Ambient.formers ℓ)
            (Specification.map (λ (A : Set ℓ) → A)
              (Completion.decode
                (univalent-stage completions Φ (Tree.node X f)))
              F))
          (map-covered
            (λ w →
              product-layer completions Φ X f F w
                (Type-Hypotheses.families H))
            (Relationally-Regular.bound regular (pr₁ F) (pr₂ F)))
    ; sum = λ F →
        names-in-the-completion (type-parent H)
          (univalent-stage completions Φ (Tree.node X f))
          (Specification.Formers.sum (Ambient.formers ℓ)
            (Specification.map (λ (A : Set ℓ) → A)
              (Completion.decode
                (univalent-stage completions Φ (Tree.node X f)))
              F))
          (map-covered
            (λ w →
              sum-layer completions Φ X f F w (Type-Hypotheses.families H))
            (Relationally-Regular.bound regular (pr₁ F) (pr₂ F)))
    ; tree = λ F →
        names-in-the-completion (type-parent H)
          (univalent-stage completions Φ (Tree.node X f))
          (Specification.Formers.tree (Ambient.formers ℓ)
            (Specification.map (λ (A : Set ℓ) → A)
              (Completion.decode
                (univalent-stage completions Φ (Tree.node X f)))
              F))
          (map-covered
            (λ w →
              tree-layer completions Φ X f F w (Type-Hypotheses.families H))
            (Relationally-Regular.bound regular (pr₁ F) (pr₂ F)))
    ; identity = identity-types-in-the-stage
    ; inner = λ F →
        pr₁ (operator-index-in-the-stage F) ,
        (λ z → pr₁ (operator-members-in-the-stage F z))
    ; inner-β = λ F →
        pair (λ (A : Set ℓ) → A) (Type-Hypotheses.families H)
          (pr₂ (operator-index-in-the-stage F))
          (λ z → pr₂ (operator-members-in-the-stage F z))
    }

  -- The stage's decoding is an embedding.
  regular-closure-has-unique-names :
    Has-Unique-Names (type-parent H) regular-closure
  regular-closure-has-unique-names =
    Completion.decode-is-an-embedding
      (univalent-stage completions Φ (Tree.node X f))

------------------------------------------------------------------------
-- The passage

relational-passage : {ℓ : Level} → Type-Hypotheses ℓ →
  (completions : Completions ℓ (Set ℓ)) →
  ((Φ : Ambient.Operator ℓ) →
    Σ (Set ℓ) (λ X →
      Σ (X → Height ℓ) (Relationally-Regular completions Φ X))) →
  Univalent-Smallness ℓ
relational-passage H completions heights =
  smallness-of-reflector
    (reflector-of-unique-names H
      (λ Φ →
        ( Completion.completed
            (univalent-stage completions Φ
              (Tree.node (pr₁ (heights Φ)) (pr₁ (pr₂ (heights Φ)))))
        , regular-closure H completions Φ (pr₂ (pr₂ (heights Φ))) ) ,
        regular-closure-has-unique-names H completions Φ
          (pr₂ (pr₂ (heights Φ)))))

------------------------------------------------------------------------
-- Discriminator: regularity for relations is a condition

-- A code of the empty type at the node lies in no stage of a leaf: a code
-- of the leaf's stage is covered by a layer code, and the leaf's layer is
-- empty.
node-over-a-leaf-is-irregular : {ℓ : Level}
  (completions : Completions ℓ (Set ℓ)) (Φ : Ambient.Operator ℓ) →
  ¬ Relationally-Regular completions Φ (Lift ℓ 𝟙) (λ _ → leaf)
node-over-a-leaf-is-irregular {ℓ} completions Φ regular =
  covered-is-not-refuted
    (bind-covered
      (Relationally-Regular.bound regular
        (Completion.include
          (univalent-stage completions Φ
            (Tree.node (Lift ℓ 𝟙) (λ _ → leaf)))
          (Relationally-Regular.point regular , empty))
        (λ y →
          Completion.include
            (univalent-stage completions Φ
              (Tree.node (Lift ℓ 𝟙) (λ _ → leaf)))
            (Relationally-Regular.point regular , empty)))
      (λ w →
        map-covered (λ k → pr₁ (pr₁ k))
          (Completion.include-covers (univalent-stage completions Φ leaf)
            (pr₁ (pr₁ (pr₂ w))))))
    lower

------------------------------------------------------------------------
-- The question in heights form

-- Merely declared: the Mahlo rule gives, for every operator, a height
-- regular for relations. With `relational-passage` it gives smallness
-- with unique names.
Relational-Regularity : (ℓ : Level) → Set (lsuc ℓ)
Relational-Regularity ℓ =
  Type-Hypotheses ℓ → (completions : Completions ℓ (Set ℓ)) →
  Specification.Mahlo (Ambient.formers ℓ) →
  (Φ : Ambient.Operator ℓ) →
  Σ (Set ℓ) (λ X →
    Σ (X → Height ℓ) (Relationally-Regular completions Φ X))
