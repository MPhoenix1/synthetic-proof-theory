{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Heights where

-- Heights of derivations of the derivable names, and the height below which
-- the closure built from the ambient Mahlo rule closes, as closed trees
-- whose labels are the small types, each node branching over its label,
-- compared by simulation (OrdinalGeometry.Height.Ordinals). Those trees
-- carry no connection to Ordinal Geometry by themselves; the connection to
-- its presented ordinals is Heights.Presentation. Premises are indexed by
-- small types, the decodings of names, so every derivation has a height of
-- level ℓ: one node per rule, branching over its premises (`height`). A
-- tree's stage has its height (`stage-height`), and the transformation from
-- trees to derivations (Naming.Cedents.derived) lands below it
-- (`derived-height`). The bound is formed from the codes: the fan of the
-- heights of the closure's codes is a small height (`closing`), strictly
-- above a derivation of every name the closure names (`named-height`), so,
-- under extensionality, of every derivable name (`derivable-height`).
--
-- Conversely every derivation lies below its code. Rule by rule, as in
-- Cedents.named-closed, a derivation has a code naming its conclusion whose
-- stage lies above it, since moving a stage into the joined family keeps
-- its branching (`relabel-height`, `carry-height`, `raised`, `bounded`). So
-- every derivation of every derivable name lies strictly below the small
-- height (`below-closing`): for every operator, the derivable names close
-- below a small height, formed from the codes, while no small height lies
-- above Ord ℓ, the height of all small heights (Height.Ordinals.not-small).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
import SPT.Foundation.Tree as Tree
import SPT.Mahlo.Ambient as Ambient
open import SPT.Foundation.Tree.W using (sup)
import SPT.Mahlo.Specification as Specification
open import SPT.Mahlo.DS.Cedents using
  ( Ced; ∅ᶜ; Derivable
  ; seed; empty; unit; two; natural; product; sum; tree; identity; result
  ; branch)
open import SPT.IR.Description using (index)
import SPT.Mahlo.DS.Realization.Family as Families
open import SPT.Mahlo.DS.Realization.Family using (cast)
import SPT.Mahlo.DS.Naming as Naming
open import SPT.Mahlo.DS.Naming using (recast)
open import SPT.Mahlo.DS.Naming.Cedents using
  (applying; derived; named-derivable; derivable-sorted)
import SPT.Mahlo.DS.Naming.Trees as Trees
open import SPT.OrdinalGeometry.Height.Ordinals using (Height)
open import SPT.OrdinalGeometry.Height.Simulation using
  (_⊑_; _⊏_; below; under; ⊑-refl; ⊑-trans)

------------------------------------------------------------------------
-- Leaves and nodes over one branch and a family

leaf : {ℓ : Level} → Height ℓ
leaf {ℓ} = Tree.node (Lift ℓ 𝟘) (λ x → 𝟘-elim (lower x))

leaf-below : {ℓ : Level} {t : Height ℓ} → leaf ⊑ t
leaf-below = below (λ x → 𝟘-elim (lower x))

either :
  {ℓ : Level} {A : Set ℓ} → Height ℓ → (A → Height ℓ)
  → Lift ℓ 𝟙 ⊎ A → Height ℓ
either h hs (inl _) = h
either h hs (inr x) = hs x

-- A node over one branch and a family lies below another, along a map
-- of the families' points.
either-under :
  {ℓ : Level} {X Y : Set ℓ} (h : Height ℓ) (hs : X → Height ℓ)
  (k : Lift ℓ 𝟙 ⊎ Y → Height ℓ) (to : X → Y)
  → h ⊑ k (inl (lift ⋆)) → ((x : X) → hs x ⊑ k (inr (to x)))
  → (y : Lift ℓ 𝟙 ⊎ X) → either h hs y ⊏ Tree.node (Lift ℓ 𝟙 ⊎ Y) k
either-under h hs k to p q (inl _) = under (inl (lift ⋆)) p
either-under h hs k to p q (inr x) = under (inr (to x)) (q x)

either-below :
  {ℓ : Level} {X Y : Set ℓ} (h : Height ℓ) (hs : X → Height ℓ)
  (k : Lift ℓ 𝟙 ⊎ Y → Height ℓ) (to : X → Y)
  → h ⊑ k (inl (lift ⋆)) → ((x : X) → hs x ⊑ k (inr (to x)))
  → Tree.node (Lift ℓ 𝟙 ⊎ X) (either h hs) ⊑ Tree.node (Lift ℓ 𝟙 ⊎ Y) k
either-below h hs k to p q = below (either-under h hs k to p q)

------------------------------------------------------------------------
-- Heights of derivations

module _
  {κ ℓ ν : Level} {C : Set κ} {D : C → Set ℓ}
  {Q : Specification.Formers C D} {Φ : Specification.Operator D}
  {Γ : Ced ν C}
  where

  -- One node per rule, branching over its premises.
  height : {c : C} → Derivable Q Φ Γ c → Height ℓ
  height (seed p) = leaf
  height empty = leaf
  height unit = leaf
  height two = leaf
  height natural = leaf
  height (product a b d e) =
    Tree.node (Lift ℓ 𝟙 ⊎ D a) (either (height d) (λ x → height (e x)))
  height (sum a b d e) =
    Tree.node (Lift ℓ 𝟙 ⊎ D a) (either (height d) (λ x → height (e x)))
  height (tree a b d e) =
    Tree.node (Lift ℓ 𝟙 ⊎ D a) (either (height d) (λ x → height (e x)))
  height (identity a x y d) = Tree.node (Lift ℓ 𝟙) (λ _ → height d)
  height (result a b d e) =
    Tree.node (Lift ℓ 𝟙 ⊎ D a) (either (height d) (λ x → height (e x)))
  height (branch a b d e y) =
    Tree.node (Lift ℓ 𝟙 ⊎ D a) (either (height d) (λ x → height (e x)))

  transport-height :
    {c c' : C} (p : c ＝ c') (d : Derivable Q Φ Γ c)
    → height (transport (Derivable Q Φ Γ) p d) ⊑ height d
  transport-height refl d = ⊑-refl (height d)

-- The identity former and Φ's members along identities of their inputs.
identified :
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Specification.Formers C D) {a' a : C} (e : a' ＝ a) (x y : D a)
  → Specification.Formers.identity Q a'
      (cast (ap D e ⁻¹) x) (cast (ap D e ⁻¹) y)
    ＝ Specification.Formers.identity Q a x y
identified Q refl x y = refl

moved-member :
  {κ ℓ : Level} {C : Set κ} (D : C → Set ℓ)
  (Φ : Specification.Operator D)
  {G H : Specification.Family D} (e : G ＝ H) (y : D (pr₁ (Φ H)))
  → pr₂ (Φ G) (cast (ap (λ K → D (pr₁ (Φ K))) (e ⁻¹)) y) ＝ pr₂ (Φ H) y
moved-member D Φ refl y = refl

-- The height of a tree's stage.
stage-height :
  {ℓ : Level} {A : Set ℓ} (B : A → Set ℓ) → Trees.Stage A B → Height ℓ
stage-height {ℓ} {A} B (sup l f) =
  Tree.node (Trees.Branches A B l) (λ y → stage-height B (f y))

-- Moving a stage along a map of indices keeps its branching, so its
-- height does not drop.
relabel-height :
  {ℓ : Level} {A A' : Set ℓ} (B : A → Set ℓ) (ι : A' → A)
  (s : Trees.Stage A' (λ x → B (ι x)))
  → stage-height (λ x → B (ι x)) s ⊑ stage-height B (Trees.relabel B ι s)
relabel-height B ι (sup (Trees.constant t) f) =
  below (λ y → under y (relabel-height B ι (f y)))
relabel-height B ι (sup (Trees.applied t x) f) =
  below (λ y → under y (relabel-height B ι (f y)))
relabel-height B ι (sup Trees.identity f) =
  below (λ y → under y (relabel-height B ι (f y)))

------------------------------------------------------------------------
-- Trees derive below their stages

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Specification.Formers C D) (Φ : Specification.Operator D)
  where

  applying-height :
    (t : Trees.Unary) (F : Specification.Family D)
    (d : Derivable Q Φ ∅ᶜ (pr₁ F))
    (e : (x : D (pr₁ F)) → Derivable Q Φ ∅ᶜ (pr₂ F x))
    (i : Trees.Selection (Trees.apply Q Φ t F))
    → height (applying Q Φ t F d e i)
      ＝ Tree.node (Lift ℓ 𝟙 ⊎ D (pr₁ F))
          (either (height d) (λ x → height (e x)))
  applying-height Trees.product F d e i = refl
  applying-height Trees.sum F d e i = refl
  applying-height Trees.wellfounded F d e i = refl
  applying-height Trees.operator F d e (inl _) = refl
  applying-height Trees.operator F d e (inr y) = refl

  derived-height :
    {A : Set ℓ} (B : A → Set ℓ) (s : Trees.Stage A B)
    (τ : pr₁ (Trees.layer Q Φ B s))
    (i : Trees.Selection (pr₂ (Trees.layer Q Φ B s) τ))
    → height (derived Q Φ B s τ i) ⊑ stage-height B s
  derived-height B (sup (Trees.constant Trees.empty) f) τ i = leaf-below
  derived-height B (sup (Trees.constant Trees.unit) f) τ i = leaf-below
  derived-height B (sup (Trees.constant Trees.two) f) τ i = leaf-below
  derived-height B (sup (Trees.constant Trees.natural) f) τ i = leaf-below
  derived-height B (sup (Trees.applied t x) f) τ i =
    let F =
          Trees.input D (B x) (Trees.layer Q Φ B (f (inl (lift ⋆))))
            (λ y → Trees.layer Q Φ B (f (inr y))) τ
        d = derived Q Φ B (f (inl (lift ⋆))) (pr₁ (pr₁ τ)) (pr₂ (pr₁ τ))
        e = λ z →
          derived Q Φ B (f (inr (pr₁ (pr₂ τ) z)))
            (pr₁ (pr₂ (pr₂ τ) (pr₁ (pr₂ τ) z)))
            (pr₂ (pr₂ (pr₂ τ) (pr₁ (pr₂ τ) z)))
    in
    transport (λ h → h ⊑ stage-height B (sup (Trees.applied t x) f))
      (applying-height t F d e i ⁻¹)
      (either-below (height d) (λ z → height (e z))
        (λ y → stage-height B (f y)) (pr₁ (pr₂ τ))
        (derived-height B (f (inl (lift ⋆))) (pr₁ (pr₁ τ)) (pr₂ (pr₁ τ)))
        (λ z →
          derived-height B (f (inr (pr₁ (pr₂ τ) z)))
            (pr₁ (pr₂ (pr₂ τ) (pr₁ (pr₂ τ) z)))
            (pr₂ (pr₂ (pr₂ τ) (pr₁ (pr₂ τ) z)))))
  derived-height B (sup Trees.identity f) τ i =
    below
      (λ u →
        under u
          (derived-height B (f (lift ⋆)) (pr₁ (pr₁ τ)) (pr₂ (pr₁ τ))))

------------------------------------------------------------------------
-- The height below which the closure closes

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Specification.Formers C D) (Φ : Specification.Operator D)
  {K : Set ℓ}
  (L : Specification.Closure (Ambient.formers ℓ) (Trees.requests Q Φ) K)
  where

  code-height : Naming.Value Q Φ L → Height ℓ
  code-height v =
    stage-height (index (Families.view L (Naming.Value.family v)))
      (Trees.Request.stage (Naming.Value.origin v))

  -- The fan of the codes' heights: a small height.
  closing : Height ℓ
  closing = Tree.node (Naming.Value Q Φ L) code-height

  named-height :
    {c : C} (n : Specification.Name (Naming.sort Q Φ L) c)
    → height (named-derivable Q Φ L n) ⊏ closing
  named-height n =
    under (pr₁ n)
      (⊑-trans
        (transport-height (pr₂ n)
          (derived Q Φ (index (Families.view L (Naming.Value.family (pr₁ n))))
            (Trees.Request.stage (Naming.Value.origin (pr₁ n)))
            (Trees.Request.tree (Naming.Value.origin (pr₁ n)))
            (Trees.Request.selection (Naming.Value.origin (pr₁ n)))))
        (derived-height Q Φ
          (index (Families.view L (Naming.Value.family (pr₁ n))))
          (Trees.Request.stage (Naming.Value.origin (pr₁ n)))
          (Trees.Request.tree (Naming.Value.origin (pr₁ n)))
          (Trees.Request.selection (Naming.Value.origin (pr₁ n)))))

  -- Every derivable name has a derivation below the small height.
  derivable-height :
    (extensionality : (X : Set ℓ) → FunExt X (λ _ → C))
    {c : C} → Derivable Q Φ ∅ᶜ c
    → Σ (Derivable Q Φ ∅ᶜ c) (λ d → height d ⊏ closing)
  derivable-height extensionality d =
    named-derivable Q Φ L (derivable-sorted Q Φ L extensionality d) ,
    named-height (derivable-sorted Q Φ L extensionality d)

  ----------------------------------------------------------------------
  -- Every derivation lies below the small height

  module _
    (extensionality : (X : Set ℓ) → FunExt X (λ _ → C))
    where

    carry-height :
      {A A' : Set ℓ} (B : A → Set ℓ) (ι : A' → A) {B' : A' → Set ℓ}
      (e : (λ x → B (ι x)) ＝ B') (r : Trees.Request Q Φ B')
      → stage-height B' (Trees.Request.stage r)
        ⊑ stage-height B
            (Trees.Request.stage (Trees.carry extensionality Q Φ B ι e r))
    carry-height B ι refl r = relabel-height B ι (Trees.Request.stage r)

    -- A family node over codes of an index and of members, each above a
    -- derivation, lies above the node of those derivations.
    module _
      (a : C) (b : D a → C) (v : Naming.Value Q Φ L)
      (p : Naming.sort Q Φ L v ＝ a)
      (w : (x : D a) → Naming.Value Q Φ L)
      (q : (x : D a) → Naming.sort Q Φ L (w x) ＝ b x)
      where

      members : D (Naming.sort Q Φ L v) → Naming.Value Q Φ L
      members x = w (cast (ap D p) x)

      joint-β : Naming.carried-family Q Φ L extensionality v members ＝ (a , b)
      joint-β =
        Naming.node-β Q Φ L extensionality v members
        ∙ Trees.pair D extensionality p (λ x → q (cast (ap D p) x))

      toward : D a → index (Families.view L
          (Families.Extension.family (Naming.joined Q Φ L v members)))
          (Families.Extension.left (Naming.joined Q Φ L v members) (lift ⋆))
      toward x =
        cast (Naming.pointed Q Φ L v members ⁻¹) (cast (ap D p ⁻¹) x)

      back :
        (x : D a)
        → cast (ap D p) (cast (Naming.pointed Q Φ L v members) (toward x)) ＝ x
      back x =
        ap (cast (ap D p))
          (recast (Naming.pointed Q Φ L v members) (cast (ap D p ⁻¹) x))
        ∙ recast (ap D p) x

      raised :
        (t : Trees.Unary) (h : Height ℓ) (hs : D a → Height ℓ)
        → h ⊑ code-height v → ((x : D a) → hs x ⊑ code-height (w x))
        → Tree.node (Lift ℓ 𝟙 ⊎ D a) (either h hs)
          ⊑ stage-height
              (index (Families.view L (Naming.Node.family
                (Naming.node Q Φ L extensionality t (v , members)))))
              (Naming.Node.stage
                (Naming.node Q Φ L extensionality t (v , members)))
      raised t h hs below-index below-members =
        either-below h hs
          (λ y →
            stage-height
              (index (Families.view L
                (Families.Extension.family (Naming.joined Q Φ L v members))))
              (Naming.branches Q Φ L extensionality v members y))
          toward
          (⊑-trans below-index
            (carry-height
              (index (Families.view L
                (Families.Extension.family (Naming.joined Q Φ L v members))))
              (Naming.index-inclusion Q Φ L v members)
              (Naming.index-included Q Φ L v members)
              (Naming.Value.origin v)))
          (λ x →
            ⊑-trans (below-members x)
              (⊑-trans
                (transport
                  (λ x' → code-height (w x) ⊑ code-height (w x'))
                  (back x ⁻¹) (⊑-refl (code-height (w x))))
                (carry-height
                  (index (Families.view L
                    (Families.Extension.family
                      (Naming.joined Q Φ L v members))))
                  (Naming.member-inclusion Q Φ L v members
                    (cast (Naming.pointed Q Φ L v members) (toward x)))
                  (Naming.member-included Q Φ L v members
                    (cast (Naming.pointed Q Φ L v members) (toward x)))
                  (Naming.Value.origin
                    (members
                      (cast (Naming.pointed Q Φ L v members) (toward x)))))))

    -- Each derivation has a code naming its conclusion, above it.
    bounded :
      {c : C} (d : Derivable Q Φ ∅ᶜ c)
      → Σ (Naming.Value Q Φ L)
          (λ v → (Naming.sort Q Φ L v ＝ c) × (height d ⊑ code-height v))
    bounded (seed ())
    bounded empty =
      Naming.selecting Q Φ L (Naming.constant-node Q Φ L Trees.empty)
        (lift ⋆) ,
      (refl , leaf-below)
    bounded unit =
      Naming.selecting Q Φ L (Naming.constant-node Q Φ L Trees.unit)
        (lift ⋆) ,
      (refl , leaf-below)
    bounded two =
      Naming.selecting Q Φ L (Naming.constant-node Q Φ L Trees.two)
        (lift ⋆) ,
      (refl , leaf-below)
    bounded natural =
      Naming.selecting Q Φ L (Naming.constant-node Q Φ L Trees.natural)
        (lift ⋆) ,
      (refl , leaf-below)
    bounded (product a b d e) =
      let v = pr₁ (bounded d)
          p = pr₁ (pr₂ (bounded d))
          w = λ x → pr₁ (bounded (e x))
          q = λ x → pr₁ (pr₂ (bounded (e x)))
      in
      Naming.selecting Q Φ L
        (Naming.node Q Φ L extensionality Trees.product
          (v , members a b v p w q))
        (lift ⋆) ,
      ( ap (Specification.Formers.product Q) (joint-β a b v p w q)
      , raised a b v p w q Trees.product (height d) (λ x → height (e x))
          (pr₂ (pr₂ (bounded d))) (λ x → pr₂ (pr₂ (bounded (e x)))))
    bounded (sum a b d e) =
      let v = pr₁ (bounded d)
          p = pr₁ (pr₂ (bounded d))
          w = λ x → pr₁ (bounded (e x))
          q = λ x → pr₁ (pr₂ (bounded (e x)))
      in
      Naming.selecting Q Φ L
        (Naming.node Q Φ L extensionality Trees.sum
          (v , members a b v p w q))
        (lift ⋆) ,
      ( ap (Specification.Formers.sum Q) (joint-β a b v p w q)
      , raised a b v p w q Trees.sum (height d) (λ x → height (e x))
          (pr₂ (pr₂ (bounded d))) (λ x → pr₂ (pr₂ (bounded (e x)))))
    bounded (tree a b d e) =
      let v = pr₁ (bounded d)
          p = pr₁ (pr₂ (bounded d))
          w = λ x → pr₁ (bounded (e x))
          q = λ x → pr₁ (pr₂ (bounded (e x)))
      in
      Naming.selecting Q Φ L
        (Naming.node Q Φ L extensionality Trees.wellfounded
          (v , members a b v p w q))
        (lift ⋆) ,
      ( ap (Specification.Formers.tree Q) (joint-β a b v p w q)
      , raised a b v p w q Trees.wellfounded (height d)
          (λ x → height (e x))
          (pr₂ (pr₂ (bounded d))) (λ x → pr₂ (pr₂ (bounded (e x)))))
    bounded (identity a x y d) =
      let v = pr₁ (bounded d)
          p = pr₁ (pr₂ (bounded d))
      in
      Naming.selecting Q Φ L
        (Naming.identity-node Q Φ L v
          (cast (ap D p ⁻¹) x) (cast (ap D p ⁻¹) y))
        (lift ⋆) ,
      ( identified Q p x y
      , below (λ u → under u (pr₂ (pr₂ (bounded d)))))
    bounded (result a b d e) =
      let v = pr₁ (bounded d)
          p = pr₁ (pr₂ (bounded d))
          w = λ x → pr₁ (bounded (e x))
          q = λ x → pr₁ (pr₂ (bounded (e x)))
      in
      Naming.selecting Q Φ L
        (Naming.node Q Φ L extensionality Trees.operator
          (v , members a b v p w q))
        (inl (lift ⋆)) ,
      ( ap (λ G → pr₁ (Φ G)) (joint-β a b v p w q)
      , raised a b v p w q Trees.operator (height d) (λ x → height (e x))
          (pr₂ (pr₂ (bounded d))) (λ x → pr₂ (pr₂ (bounded (e x)))))
    bounded (branch a b d e y) =
      let v = pr₁ (bounded d)
          p = pr₁ (pr₂ (bounded d))
          w = λ x → pr₁ (bounded (e x))
          q = λ x → pr₁ (pr₂ (bounded (e x)))
      in
      Naming.selecting Q Φ L
        (Naming.node Q Φ L extensionality Trees.operator
          (v , members a b v p w q))
        (inr
          (cast (ap (λ K → D (pr₁ (Φ K))) (joint-β a b v p w q ⁻¹)) y)) ,
      ( moved-member D Φ (joint-β a b v p w q) y
      , raised a b v p w q Trees.operator (height d) (λ x → height (e x))
          (pr₂ (pr₂ (bounded d))) (λ x → pr₂ (pr₂ (bounded (e x)))))

    -- Every derivation of a derivable name lies strictly below the small
    -- height: the derivable names close below it.
    below-closing :
      {c : C} (d : Derivable Q Φ ∅ᶜ c) → height d ⊏ closing
    below-closing d = under (pr₁ (bounded d)) (pr₂ (pr₂ (bounded d)))
