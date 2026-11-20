{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Heights.Least where

-- The closure height of the derivable names from the ambient Mahlo rule,
-- with no induction–recursion. Heights.closing is the fan of the stages'
-- heights of the closure's codes; a stage may branch beyond what its
-- derivation uses, so that fan is only shown to lie above. Here each code
-- is measured by the height of its own derivation (`derivation-height`),
-- and the fan of those (`closure-height`) is the least height strictly
-- above every derivation: it lies below every height strictly above all
-- derivations, by construction (`closure-least`), and below Heights.closing
-- (`least-below-closing`). That every derivation lies strictly below it
-- needs one lemma: a derivation taken from a moved tree keeps its height
-- (`shift-derived`, `carry-derived`). With it, the code that
-- Heights.bounded forms from a derivation has a derivation at least as
-- high, rule by rule (`raised-derived`, `bounded-derived`), so every
-- derivation lies strictly below the closure height (`below-least`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
import SPT.Foundation.Tree as Tree
import SPT.Mahlo.Ambient as Ambient
open import SPT.Foundation.Tree.W using (sup)
import SPT.Mahlo.Specification as Specification
open import SPT.Mahlo.DS.Cedents using
  ( ∅ᶜ; Derivable
  ; seed; empty; unit; two; natural; product; sum; tree; identity; result
  ; branch)
open import SPT.IR.Description using (index)
import SPT.Mahlo.DS.Realization.Family as Families
open import SPT.Mahlo.DS.Realization.Family using (cast)
import SPT.Mahlo.DS.Naming as Naming
open import SPT.Mahlo.DS.Naming using (recast)
open import SPT.Mahlo.DS.Naming.Cedents using
  (applying; derived; named-derivable)
import SPT.Mahlo.DS.Naming.Trees as Trees
open import SPT.OrdinalGeometry.Height.Ordinals using (Height)
open import SPT.OrdinalGeometry.Height.Simulation using
  (_⊑_; _⊏_; below; under; ⊑-refl; ⊑-trans)
open import SPT.Mahlo.Heights using
  ( leaf-below; either; either-below; height; applying-height
  ; derived-height; closing; bounded; members; joint-β)

------------------------------------------------------------------------
-- Derivations of moved trees keep their heights

-- Along relabel and shift each node keeps its rule and its premises: an
-- applied node's members are read through the identity of the chosen
-- index (`moved`), and recast returns each member to its own branch.

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (extensionality : (X : Set ℓ) → FunExt X (λ _ → C))
  (Q : Specification.Formers C D) (Φ : Specification.Operator D)
  where

  shift-derived :
    {A A' : Set ℓ} (B : A → Set ℓ) (ι : A' → A)
    (s : Trees.Stage A' (λ x → B (ι x)))
    (τ : pr₁ (Trees.layer Q Φ (λ x → B (ι x)) s))
    (i : Trees.Selection (pr₂ (Trees.layer Q Φ (λ x → B (ι x)) s) τ))
    → height (derived Q Φ (λ x → B (ι x)) s τ i)
      ⊑ height
          (derived Q Φ B (Trees.relabel B ι s)
            (Trees.shift extensionality Q Φ B ι s τ)
            (transport Trees.Selection
              (Trees.shifted extensionality Q Φ B ι s τ ⁻¹) i))
  shift-derived B ι (sup (Trees.constant Trees.empty) f) τ i = leaf-below
  shift-derived B ι (sup (Trees.constant Trees.unit) f) τ i = leaf-below
  shift-derived B ι (sup (Trees.constant Trees.two) f) τ i = leaf-below
  shift-derived B ι (sup (Trees.constant Trees.natural) f) τ i =
    leaf-below
  shift-derived B ι (sup (Trees.applied t u) f) τ i =
    let τ' = Trees.shift extensionality Q Φ B ι (sup (Trees.applied t u) f) τ
        i' =
          transport Trees.Selection
            (Trees.shifted extensionality Q Φ B ι
              (sup (Trees.applied t u) f) τ ⁻¹)
            i
        F =
          Trees.input D (B (ι u))
            (Trees.layer Q Φ (λ x → B (ι x)) (f (inl (lift ⋆))))
            (λ y → Trees.layer Q Φ (λ x → B (ι x)) (f (inr y))) τ
        d =
          derived Q Φ (λ x → B (ι x)) (f (inl (lift ⋆)))
            (pr₁ (pr₁ τ)) (pr₂ (pr₁ τ))
        e = λ z →
          derived Q Φ (λ x → B (ι x)) (f (inr (pr₁ (pr₂ τ) z)))
            (pr₁ (pr₂ (pr₂ τ) (pr₁ (pr₂ τ) z)))
            (pr₂ (pr₂ (pr₂ τ) (pr₁ (pr₂ τ) z)))
        F' =
          Trees.input D (B (ι u))
            (Trees.layer Q Φ B (Trees.relabel B ι (f (inl (lift ⋆)))))
            (λ y → Trees.layer Q Φ B (Trees.relabel B ι (f (inr y)))) τ'
        d' =
          derived Q Φ B (Trees.relabel B ι (f (inl (lift ⋆))))
            (pr₁ (pr₁ τ')) (pr₂ (pr₁ τ'))
        e' = λ z →
          derived Q Φ B (Trees.relabel B ι (f (inr (pr₁ (pr₂ τ') z))))
            (pr₁ (pr₂ (pr₂ τ') (pr₁ (pr₂ τ') z)))
            (pr₂ (pr₂ (pr₂ τ') (pr₁ (pr₂ τ') z)))
        moving =
          ap D
            (Trees.moved extensionality Q Φ B ι (f (inl (lift ⋆))) (pr₁ τ))
        G = λ y →
          height
            (derived Q Φ B (Trees.relabel B ι (f (inr y)))
              (Trees.shift extensionality Q Φ B ι (f (inr y))
                (pr₁ (pr₂ (pr₂ τ) y)))
              (transport Trees.Selection
                (Trees.shifted extensionality Q Φ B ι (f (inr y))
                  (pr₁ (pr₂ (pr₂ τ) y)) ⁻¹)
                (pr₂ (pr₂ (pr₂ τ) y))))
    in
    transport (λ h → h ⊑ height (applying Q Φ t F' d' e' i'))
      (applying-height Q Φ t F d e i ⁻¹)
      (transport
        (λ h →
          Tree.node (Lift ℓ 𝟙 ⊎ D (pr₁ F))
            (either (height d) (λ z → height (e z)))
          ⊑ h)
        (applying-height Q Φ t F' d' e' i' ⁻¹)
        (either-below (height d) (λ z → height (e z))
          (either (height d') (λ z → height (e' z)))
          (λ z → cast (moving ⁻¹) z)
          (shift-derived B ι (f (inl (lift ⋆))) (pr₁ (pr₁ τ)) (pr₂ (pr₁ τ)))
          (λ z →
            ⊑-trans
              (shift-derived B ι (f (inr (pr₁ (pr₂ τ) z)))
                (pr₁ (pr₂ (pr₂ τ) (pr₁ (pr₂ τ) z)))
                (pr₂ (pr₂ (pr₂ τ) (pr₁ (pr₂ τ) z))))
              (transport
                (λ w → G (pr₁ (pr₂ τ) z) ⊑ G (pr₁ (pr₂ τ) w))
                (recast moving z ⁻¹)
                (⊑-refl (G (pr₁ (pr₂ τ) z)))))))
  shift-derived B ι (sup Trees.identity f) τ i =
    below
      (λ u →
        under u
          (shift-derived B ι (f (lift ⋆)) (pr₁ (pr₁ τ)) (pr₂ (pr₁ τ))))

  -- Along an identity of families, by its one case.
  carry-derived :
    {A A' : Set ℓ} (B : A → Set ℓ) (ι : A' → A) {B' : A' → Set ℓ}
    (e : (λ x → B (ι x)) ＝ B') (r : Trees.Request Q Φ B')
    → height
        (derived Q Φ B' (Trees.Request.stage r) (Trees.Request.tree r)
          (Trees.Request.selection r))
      ⊑ height
          (derived Q Φ B
            (Trees.Request.stage (Trees.carry extensionality Q Φ B ι e r))
            (Trees.Request.tree (Trees.carry extensionality Q Φ B ι e r))
            (Trees.Request.selection
              (Trees.carry extensionality Q Φ B ι e r)))
  carry-derived B ι refl r =
    shift-derived B ι (Trees.Request.stage r) (Trees.Request.tree r)
      (Trees.Request.selection r)

------------------------------------------------------------------------
-- The closure height

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Specification.Formers C D) (Φ : Specification.Operator D)
  {K : Set ℓ}
  (L : Specification.Closure (Ambient.formers ℓ) (Trees.requests Q Φ) K)
  where

  -- The height of the derivation of a code's tree.
  derivation-height : Naming.Value Q Φ L → Height ℓ
  derivation-height v =
    height
      (derived Q Φ (index (Families.view L (Naming.Value.family v)))
        (Trees.Request.stage (Naming.Value.origin v))
        (Trees.Request.tree (Naming.Value.origin v))
        (Trees.Request.selection (Naming.Value.origin v)))

  -- The fan of the codes' derivation heights: a small height.
  closure-height : Height ℓ
  closure-height = Tree.node (Naming.Value Q Φ L) derivation-height

  -- Below every height strictly above all derivations.
  closure-least :
    (t : Height ℓ)
    → ({c : C} (d : Derivable Q Φ ∅ᶜ c) → height d ⊏ t)
    → closure-height ⊑ t
  closure-least t above =
    below (λ v → above (named-derivable Q Φ L (v , refl)))

  -- A tree's derivation lies below its stage.
  least-below-closing : closure-height ⊑ closing Q Φ L
  least-below-closing =
    below
      (λ v →
        under v
          (derived-height Q Φ
            (index (Families.view L (Naming.Value.family v)))
            (Trees.Request.stage (Naming.Value.origin v))
            (Trees.Request.tree (Naming.Value.origin v))
            (Trees.Request.selection (Naming.Value.origin v))))

  ----------------------------------------------------------------------
  -- Every derivation lies strictly below the closure height

  module _
    (extensionality : (X : Set ℓ) → FunExt X (λ _ → C))
    where

    -- A family node over codes of an index and of members, each with a
    -- derivation above a height, has a derivation above the node of those
    -- heights: the index's request and each member's are carried into the
    -- joined family, which keeps their derivations' heights.
    module _
      (a : C) (b : D a → C) (v : Naming.Value Q Φ L)
      (p : Naming.sort Q Φ L v ＝ a)
      (w : (x : D a) → Naming.Value Q Φ L)
      (q : (x : D a) → Naming.sort Q Φ L (w x) ＝ b x)
      where

      raised-derived :
        (t : Trees.Unary)
        (i :
          Trees.Selection
            (Naming.output Q Φ L
              (Naming.node Q Φ L extensionality t
                (v , members Q Φ L extensionality a b v p w q))))
        (h : Height ℓ) (hs : D a → Height ℓ)
        → h ⊑ derivation-height v
        → ((x : D a) → hs x ⊑ derivation-height (w x))
        → Tree.node (Lift ℓ 𝟙 ⊎ D a) (either h hs)
          ⊑ derivation-height
              (Naming.selecting Q Φ L
                (Naming.node Q Φ L extensionality t
                  (v , members Q Φ L extensionality a b v p w q))
                i)
      raised-derived t i h hs below-index below-members =
        let ms = members Q Φ L extensionality a b v p w q
            n = Naming.node Q Φ L extensionality t (v , ms)
            joint =
              index (Families.view L
                (Families.Extension.family (Naming.joined Q Φ L v ms)))
            ci = Naming.carry-index Q Φ L extensionality v ms
            cm = Naming.carry-member Q Φ L extensionality v ms
            tw = Naming.towards Q Φ L extensionality v ms
            indexed = ap D (Naming.carried-index Q Φ L extensionality v ms)
            F =
              Trees.input D
                (joint
                  (Families.Extension.left (Naming.joined Q Φ L v ms)
                    (lift ⋆)))
                (Trees.layer Q Φ joint
                  (Naming.branches Q Φ L extensionality v ms (inl (lift ⋆))))
                (λ y →
                  Trees.layer Q Φ joint
                    (Naming.branches Q Φ L extensionality v ms (inr y)))
                (Naming.Node.tree n)
            d =
              derived Q Φ joint (Trees.Request.stage ci)
                (Trees.Request.tree ci) (Trees.Request.selection ci)
            e = λ z →
              derived Q Φ joint (Trees.Request.stage (cm (tw z)))
                (Trees.Request.tree (cm (tw z)))
                (Trees.Request.selection (cm (tw z)))
            into = λ x → cast (indexed ⁻¹) (cast (ap D p ⁻¹) x)
            back = λ x →
              ap (cast (ap D p))
                (recast (Naming.pointed Q Φ L v ms)
                  (cast indexed (into x))
                ∙ recast indexed (cast (ap D p ⁻¹) x))
              ∙ recast (ap D p) x
        in
        transport
          (λ g → Tree.node (Lift ℓ 𝟙 ⊎ D a) (either h hs) ⊑ g)
          (applying-height Q Φ t F d e i ⁻¹)
          (either-below h hs (either (height d) (λ z → height (e z))) into
            (⊑-trans below-index
              (carry-derived extensionality Q Φ joint
                (Naming.index-inclusion Q Φ L v ms)
                (Naming.index-included Q Φ L v ms)
                (Naming.Value.origin v)))
            (λ x →
              ⊑-trans (below-members x)
                (⊑-trans
                  (transport
                    (λ x' → derivation-height (w x) ⊑ derivation-height (w x'))
                    (back x ⁻¹) (⊑-refl (derivation-height (w x))))
                  (carry-derived extensionality Q Φ joint
                    (Naming.member-inclusion Q Φ L v ms
                      (cast (Naming.pointed Q Φ L v ms) (tw (into x))))
                    (Naming.member-included Q Φ L v ms
                      (cast (Naming.pointed Q Φ L v ms) (tw (into x))))
                    (Naming.Value.origin
                      (ms
                        (cast (Naming.pointed Q Φ L v ms) (tw (into x)))))))))

    -- The code Heights.bounded forms from a derivation has a derivation at
    -- least as high.
    bounded-derived :
      {c : C} (d : Derivable Q Φ ∅ᶜ c)
      → height d ⊑ derivation-height (pr₁ (bounded Q Φ L extensionality d))
    bounded-derived (seed ())
    bounded-derived empty = leaf-below
    bounded-derived unit = leaf-below
    bounded-derived two = leaf-below
    bounded-derived natural = leaf-below
    bounded-derived (product a b d e) =
      raised-derived a b (pr₁ (bounded Q Φ L extensionality d))
        (pr₁ (pr₂ (bounded Q Φ L extensionality d)))
        (λ x → pr₁ (bounded Q Φ L extensionality (e x)))
        (λ x → pr₁ (pr₂ (bounded Q Φ L extensionality (e x))))
        Trees.product (lift ⋆) (height d) (λ x → height (e x))
        (bounded-derived d) (λ x → bounded-derived (e x))
    bounded-derived (sum a b d e) =
      raised-derived a b (pr₁ (bounded Q Φ L extensionality d))
        (pr₁ (pr₂ (bounded Q Φ L extensionality d)))
        (λ x → pr₁ (bounded Q Φ L extensionality (e x)))
        (λ x → pr₁ (pr₂ (bounded Q Φ L extensionality (e x))))
        Trees.sum (lift ⋆) (height d) (λ x → height (e x))
        (bounded-derived d) (λ x → bounded-derived (e x))
    bounded-derived (tree a b d e) =
      raised-derived a b (pr₁ (bounded Q Φ L extensionality d))
        (pr₁ (pr₂ (bounded Q Φ L extensionality d)))
        (λ x → pr₁ (bounded Q Φ L extensionality (e x)))
        (λ x → pr₁ (pr₂ (bounded Q Φ L extensionality (e x))))
        Trees.wellfounded (lift ⋆) (height d) (λ x → height (e x))
        (bounded-derived d) (λ x → bounded-derived (e x))
    bounded-derived (identity a x y d) =
      below (λ u → under u (bounded-derived d))
    bounded-derived (result a b d e) =
      raised-derived a b (pr₁ (bounded Q Φ L extensionality d))
        (pr₁ (pr₂ (bounded Q Φ L extensionality d)))
        (λ x → pr₁ (bounded Q Φ L extensionality (e x)))
        (λ x → pr₁ (pr₂ (bounded Q Φ L extensionality (e x))))
        Trees.operator (inl (lift ⋆)) (height d) (λ x → height (e x))
        (bounded-derived d) (λ x → bounded-derived (e x))
    bounded-derived (branch a b d e y) =
      raised-derived a b (pr₁ (bounded Q Φ L extensionality d))
        (pr₁ (pr₂ (bounded Q Φ L extensionality d)))
        (λ x → pr₁ (bounded Q Φ L extensionality (e x)))
        (λ x → pr₁ (pr₂ (bounded Q Φ L extensionality (e x))))
        Trees.operator
        (inr
          (cast
            (ap (λ G → D (pr₁ (Φ G)))
              (joint-β Q Φ L extensionality a b
                (pr₁ (bounded Q Φ L extensionality d))
                (pr₁ (pr₂ (bounded Q Φ L extensionality d)))
                (λ x → pr₁ (bounded Q Φ L extensionality (e x)))
                (λ x → pr₁ (pr₂ (bounded Q Φ L extensionality (e x))))
              ⁻¹))
            y))
        (height d) (λ x → height (e x))
        (bounded-derived d) (λ x → bounded-derived (e x))

    -- Every derivation of a derivable name lies strictly below the closure
    -- height.
    below-least :
      {c : C} (d : Derivable Q Φ ∅ᶜ c) → height d ⊏ closure-height
    below-least d =
      under (pr₁ (bounded Q Φ L extensionality d)) (bounded-derived d)
