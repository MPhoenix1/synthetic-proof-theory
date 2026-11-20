{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Heights.Comparison where

-- Heights of the two-sorted induction–recursive closure, compared with
-- derivations and with the closure built from the ambient rule. A code's
-- height has one node per constructor (`ir-height`), and it is the height
-- of the code's derivation, both ways (`exact-below`, `exact-above`). Each
-- derivation has a code naming its conclusion above it, under
-- extensionality (`ir-members`, `ir-joint`, `ir-raised`, `ir-bounded`), so
-- the fan of the codes' heights (`ir-closing`) lies strictly above every
-- derivation (`ir-below-closing`) and is the least height that does
-- (`ir-least`): it is the closure height of the derivable names. The
-- closure from the ambient rule lies above it (`ir-below-mahlo`), and in
-- both directions a code's derivation lies below a code of the other
-- closure naming the same name (`coded-below`, `sorted-below`). Every
-- presented ordinal lies below the closure height (`ir-presented-below`, by
-- Heights.Presentation). The least height formed from the ambient rule with
-- no induction–recursion (Heights.Least.closure-height) is the closure
-- height too, both ways (`ir-below-least`, `least-below-ir`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
import SPT.Foundation.Tree as Tree
import SPT.Mahlo.Ambient as Ambient
import SPT.Mahlo.Specification as Specification
open import SPT.Mahlo.DS.Cedents using
  ( ∅ᶜ; Derivable
  ; seed; empty; unit; two; natural; product; sum; tree; identity; result
  ; branch)
open import SPT.Mahlo.DS.Realization.Family using (cast)
import SPT.Mahlo.DS.Naming as Naming
open import SPT.Mahlo.DS.Naming using (recast; sorted-laws)
open import SPT.Mahlo.DS.Naming.Cedents using (named-derivable)
open import SPT.Mahlo.DS.Naming.Trees using (requests; pair)
open import SPT.Mahlo.DS.Sorted using (Sort; decode; formers)
open import SPT.Mahlo.DS.Sorted.Realization.Discriminator using
  (Code; interpret)
import SPT.Mahlo.DS.Sorted.Realization.Discriminator as IR
import SPT.Mahlo.DS.Sorted.Realization.Cedents as Coded
open import SPT.Mahlo.Heights using
  ( leaf; leaf-below; either; either-below; height; code-height; closing
  ; below-closing; bounded; identified; moved-member)
open import SPT.Mahlo.Heights.Least using
  (closure-height; closure-least; below-least)
import SPT.Mahlo.Heights.Presentation as Presentations
open import SPT.OrdinalGeometry.Height.Ordinals using (Height; whole)
open import SPT.OrdinalGeometry.Height.Simulation using
  (_⊑_; _⊏_; below; under; ⊑-refl; ⊑-trans; ⊑-⊏-trans)
import SPT.OrdinalGeometry.Presentation.CountableOrdinal as Presented

module _
  {ℓ κ : Level} {O : Set κ} (Ψ : Specification.Operator (decode ℓ O))
  where

  ------------------------------------------------------------------------
  -- A code's height is its derivation's

  ir-height : Code Ψ → Height ℓ
  ir-height IR.empty = leaf
  ir-height IR.unit = leaf
  ir-height IR.two = leaf
  ir-height IR.natural = leaf
  ir-height (IR.product a b) =
    Tree.node (Lift ℓ 𝟙 ⊎ decode ℓ O (interpret Ψ a))
      (either (ir-height a) (λ x → ir-height (b x)))
  ir-height (IR.sum a b) =
    Tree.node (Lift ℓ 𝟙 ⊎ decode ℓ O (interpret Ψ a))
      (either (ir-height a) (λ x → ir-height (b x)))
  ir-height (IR.tree a b) =
    Tree.node (Lift ℓ 𝟙 ⊎ decode ℓ O (interpret Ψ a))
      (either (ir-height a) (λ x → ir-height (b x)))
  ir-height (IR.result a b) =
    Tree.node (Lift ℓ 𝟙 ⊎ decode ℓ O (interpret Ψ a))
      (either (ir-height a) (λ x → ir-height (b x)))
  ir-height (IR.identity a x y) = Tree.node (Lift ℓ 𝟙) (λ _ → ir-height a)
  ir-height (IR.branch a b y) =
    Tree.node (Lift ℓ 𝟙 ⊎ decode ℓ O (interpret Ψ a))
      (either (ir-height a) (λ x → ir-height (b x)))

  exact-below : (k : Code Ψ) → height (Coded.derived Ψ k) ⊑ ir-height k
  exact-below IR.empty = leaf-below
  exact-below IR.unit = leaf-below
  exact-below IR.two = leaf-below
  exact-below IR.natural = leaf-below
  exact-below (IR.product a b) =
    either-below (height (Coded.derived Ψ a))
      (λ x → height (Coded.derived Ψ (b x)))
      (either (ir-height a) (λ x → ir-height (b x))) (λ x → x)
      (exact-below a) (λ x → exact-below (b x))
  exact-below (IR.sum a b) =
    either-below (height (Coded.derived Ψ a))
      (λ x → height (Coded.derived Ψ (b x)))
      (either (ir-height a) (λ x → ir-height (b x))) (λ x → x)
      (exact-below a) (λ x → exact-below (b x))
  exact-below (IR.tree a b) =
    either-below (height (Coded.derived Ψ a))
      (λ x → height (Coded.derived Ψ (b x)))
      (either (ir-height a) (λ x → ir-height (b x))) (λ x → x)
      (exact-below a) (λ x → exact-below (b x))
  exact-below (IR.result a b) =
    either-below (height (Coded.derived Ψ a))
      (λ x → height (Coded.derived Ψ (b x)))
      (either (ir-height a) (λ x → ir-height (b x))) (λ x → x)
      (exact-below a) (λ x → exact-below (b x))
  exact-below (IR.identity a x y) = below (λ u → under u (exact-below a))
  exact-below (IR.branch a b y) =
    either-below (height (Coded.derived Ψ a))
      (λ x → height (Coded.derived Ψ (b x)))
      (either (ir-height a) (λ x → ir-height (b x))) (λ x → x)
      (exact-below a) (λ x → exact-below (b x))

  exact-above : (k : Code Ψ) → ir-height k ⊑ height (Coded.derived Ψ k)
  exact-above IR.empty = leaf-below
  exact-above IR.unit = leaf-below
  exact-above IR.two = leaf-below
  exact-above IR.natural = leaf-below
  exact-above (IR.product a b) =
    either-below (ir-height a) (λ x → ir-height (b x))
      (either (height (Coded.derived Ψ a))
        (λ x → height (Coded.derived Ψ (b x))))
      (λ x → x) (exact-above a) (λ x → exact-above (b x))
  exact-above (IR.sum a b) =
    either-below (ir-height a) (λ x → ir-height (b x))
      (either (height (Coded.derived Ψ a))
        (λ x → height (Coded.derived Ψ (b x))))
      (λ x → x) (exact-above a) (λ x → exact-above (b x))
  exact-above (IR.tree a b) =
    either-below (ir-height a) (λ x → ir-height (b x))
      (either (height (Coded.derived Ψ a))
        (λ x → height (Coded.derived Ψ (b x))))
      (λ x → x) (exact-above a) (λ x → exact-above (b x))
  exact-above (IR.result a b) =
    either-below (ir-height a) (λ x → ir-height (b x))
      (either (height (Coded.derived Ψ a))
        (λ x → height (Coded.derived Ψ (b x))))
      (λ x → x) (exact-above a) (λ x → exact-above (b x))
  exact-above (IR.identity a x y) = below (λ u → under u (exact-above a))
  exact-above (IR.branch a b y) =
    either-below (ir-height a) (λ x → ir-height (b x))
      (either (height (Coded.derived Ψ a))
        (λ x → height (Coded.derived Ψ (b x))))
      (λ x → x) (exact-above a) (λ x → exact-above (b x))

  ------------------------------------------------------------------------
  -- The closure height

  -- The fan of the codes' heights.
  ir-closing : Height ℓ
  ir-closing = Tree.node (Code Ψ) ir-height

  -- Below every height strictly above all derivations.
  ir-least :
    (t : Height ℓ)
    → ({c : Sort ℓ O} (d : Derivable (formers ℓ O) Ψ ∅ᶜ c) → height d ⊏ t)
    → ir-closing ⊑ t
  ir-least t above =
    below (λ k → ⊑-⊏-trans (exact-above k) (above (Coded.derived Ψ k)))

  module _
    (extensionality : (X : Set ℓ) → FunExt X (λ _ → Sort ℓ O))
    where

    -- A code over codes of an index and of members, above their
    -- derivations.
    module _
      (a : Sort ℓ O) (b : decode ℓ O a → Sort ℓ O) (k : Code Ψ)
      (p : interpret Ψ k ＝ a) (w : (x : decode ℓ O a) → Code Ψ)
      (q : (x : decode ℓ O a) → interpret Ψ (w x) ＝ b x)
      where

      ir-members : decode ℓ O (interpret Ψ k) → Code Ψ
      ir-members x = w (cast (ap (decode ℓ O) p) x)

      ir-joint :
        _＝_ {A = Specification.Family (decode ℓ O)}
          (interpret Ψ k , (λ x → interpret Ψ (ir-members x))) (a , b)
      ir-joint =
        pair (decode ℓ O) extensionality p
          (λ x → q (cast (ap (decode ℓ O) p) x))

      ir-raised :
        (h : Height ℓ) (hs : decode ℓ O a → Height ℓ)
        → h ⊑ ir-height k → ((x : decode ℓ O a) → hs x ⊑ ir-height (w x))
        → Tree.node (Lift ℓ 𝟙 ⊎ decode ℓ O a) (either h hs)
          ⊑ Tree.node (Lift ℓ 𝟙 ⊎ decode ℓ O (interpret Ψ k))
              (either (ir-height k) (λ x → ir-height (ir-members x)))
      ir-raised h hs below-index below-members =
        either-below h hs
          (either (ir-height k) (λ x → ir-height (ir-members x)))
          (λ x → cast (ap (decode ℓ O) p ⁻¹) x) below-index
          (λ x →
            ⊑-trans (below-members x)
              (transport (λ z → ir-height (w x) ⊑ ir-height (w z))
                (recast (ap (decode ℓ O) p) x ⁻¹)
                (⊑-refl (ir-height (w x)))))

    ir-bounded :
      {c : Sort ℓ O} (d : Derivable (formers ℓ O) Ψ ∅ᶜ c)
      → Σ (Code Ψ) (λ k → (interpret Ψ k ＝ c) × (height d ⊑ ir-height k))
    ir-bounded (seed ())
    ir-bounded empty = IR.empty , (refl , leaf-below)
    ir-bounded unit = IR.unit , (refl , leaf-below)
    ir-bounded two = IR.two , (refl , leaf-below)
    ir-bounded natural = IR.natural , (refl , leaf-below)
    ir-bounded (product a b d e) =
      let k = pr₁ (ir-bounded d)
          p = pr₁ (pr₂ (ir-bounded d))
          w = λ x → pr₁ (ir-bounded (e x))
          q = λ x → pr₁ (pr₂ (ir-bounded (e x)))
      in
      IR.product k (ir-members a b k p w q) ,
      ( ap (Specification.Formers.product (formers ℓ O))
          (ir-joint a b k p w q)
      , ir-raised a b k p w q (height d) (λ x → height (e x))
          (pr₂ (pr₂ (ir-bounded d))) (λ x → pr₂ (pr₂ (ir-bounded (e x)))))
    ir-bounded (sum a b d e) =
      let k = pr₁ (ir-bounded d)
          p = pr₁ (pr₂ (ir-bounded d))
          w = λ x → pr₁ (ir-bounded (e x))
          q = λ x → pr₁ (pr₂ (ir-bounded (e x)))
      in
      IR.sum k (ir-members a b k p w q) ,
      ( ap (Specification.Formers.sum (formers ℓ O)) (ir-joint a b k p w q)
      , ir-raised a b k p w q (height d) (λ x → height (e x))
          (pr₂ (pr₂ (ir-bounded d))) (λ x → pr₂ (pr₂ (ir-bounded (e x)))))
    ir-bounded (tree a b d e) =
      let k = pr₁ (ir-bounded d)
          p = pr₁ (pr₂ (ir-bounded d))
          w = λ x → pr₁ (ir-bounded (e x))
          q = λ x → pr₁ (pr₂ (ir-bounded (e x)))
      in
      IR.tree k (ir-members a b k p w q) ,
      ( ap (Specification.Formers.tree (formers ℓ O)) (ir-joint a b k p w q)
      , ir-raised a b k p w q (height d) (λ x → height (e x))
          (pr₂ (pr₂ (ir-bounded d))) (λ x → pr₂ (pr₂ (ir-bounded (e x)))))
    ir-bounded (identity a x y d) =
      let k = pr₁ (ir-bounded d)
          p = pr₁ (pr₂ (ir-bounded d))
      in
      IR.identity k (cast (ap (decode ℓ O) p ⁻¹) x)
        (cast (ap (decode ℓ O) p ⁻¹) y) ,
      ( identified (formers ℓ O) p x y
      , below (λ u → under u (pr₂ (pr₂ (ir-bounded d)))))
    ir-bounded (result a b d e) =
      let k = pr₁ (ir-bounded d)
          p = pr₁ (pr₂ (ir-bounded d))
          w = λ x → pr₁ (ir-bounded (e x))
          q = λ x → pr₁ (pr₂ (ir-bounded (e x)))
      in
      IR.result k (ir-members a b k p w q) ,
      ( ap (λ G → pr₁ (Ψ G)) (ir-joint a b k p w q)
      , ir-raised a b k p w q (height d) (λ x → height (e x))
          (pr₂ (pr₂ (ir-bounded d))) (λ x → pr₂ (pr₂ (ir-bounded (e x)))))
    ir-bounded (branch a b d e y) =
      let k = pr₁ (ir-bounded d)
          p = pr₁ (pr₂ (ir-bounded d))
          w = λ x → pr₁ (ir-bounded (e x))
          q = λ x → pr₁ (pr₂ (ir-bounded (e x)))
      in
      IR.branch k (ir-members a b k p w q)
        (cast
          (ap (λ K → decode ℓ O (pr₁ (Ψ K))) (ir-joint a b k p w q ⁻¹)) y) ,
      ( moved-member (decode ℓ O) Ψ (ir-joint a b k p w q) y
      , ir-raised a b k p w q (height d) (λ x → height (e x))
          (pr₂ (pr₂ (ir-bounded d))) (λ x → pr₂ (pr₂ (ir-bounded (e x)))))

    ir-below-closing :
      {c : Sort ℓ O} (d : Derivable (formers ℓ O) Ψ ∅ᶜ c)
      → height d ⊏ ir-closing
    ir-below-closing d = under (pr₁ (ir-bounded d)) (pr₂ (pr₂ (ir-bounded d)))

    -- Every presented ordinal lies below the closure height.
    ir-presented-below :
      (P : Presented.Countable-Ordinal𝒫 ℓ)
      → whole (Presented.Countable-Ordinal𝒫._<_ P)
          (Presented.Countable-Ordinal𝒫.<-wf P)
        ⊏ ir-closing
    ir-presented-below P =
      ⊑-⊏-trans (Presentations.dominates-whole (formers ℓ O) Ψ sorted-laws P)
        (ir-below-closing
          (Presentations.whole-derivation (formers ℓ O) Ψ sorted-laws P))

    --------------------------------------------------------------------
    -- Against the closure from the ambient rule

    module _
      {K : Set ℓ}
      (L : Specification.Closure (Ambient.formers ℓ)
        (requests (formers ℓ O) Ψ) K)
      where

      -- The closure from the ambient rule lies above the closure height.
      ir-below-mahlo : ir-closing ⊑ closing (formers ℓ O) Ψ L
      ir-below-mahlo =
        ir-least (closing (formers ℓ O) Ψ L)
          (λ d → below-closing (formers ℓ O) Ψ L extensionality d)

      -- Each code lies below a tree naming its interpretation.
      coded-below :
        (k : Code Ψ)
        → Σ (Naming.Value (formers ℓ O) Ψ L)
            (λ v →
              (Naming.sort (formers ℓ O) Ψ L v ＝ interpret Ψ k)
              × (ir-height k ⊑ code-height (formers ℓ O) Ψ L v))
      coded-below k =
        pr₁ (bounded (formers ℓ O) Ψ L extensionality (Coded.derived Ψ k)) ,
        ( pr₁ (pr₂
            (bounded (formers ℓ O) Ψ L extensionality (Coded.derived Ψ k)))
        , ⊑-trans (exact-above k)
            (pr₂ (pr₂
              (bounded (formers ℓ O) Ψ L extensionality
                (Coded.derived Ψ k)))))

      -- Each tree's derivation lies below a code naming its name.
      sorted-below :
        (v : Naming.Value (formers ℓ O) Ψ L)
        → Σ (Code Ψ)
            (λ k →
              (interpret Ψ k ＝ Naming.sort (formers ℓ O) Ψ L v)
              × (height (named-derivable (formers ℓ O) Ψ L (v , refl))
                 ⊑ ir-height k))
      sorted-below v =
        ir-bounded (named-derivable (formers ℓ O) Ψ L (v , refl))

      -- The least height from the ambient rule, with no
      -- induction–recursion, is the closure height, both ways.
      ir-below-least : ir-closing ⊑ closure-height (formers ℓ O) Ψ L
      ir-below-least =
        ir-least (closure-height (formers ℓ O) Ψ L)
          (λ d → below-least (formers ℓ O) Ψ L extensionality d)

      least-below-ir : closure-height (formers ℓ O) Ψ L ⊑ ir-closing
      least-below-ir =
        closure-least (formers ℓ O) Ψ L ir-closing
          (λ d → ir-below-closing d)
