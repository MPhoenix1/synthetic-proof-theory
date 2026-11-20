{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Heights.Regular where

-- The Mahlo rule of the ambient family is the existence, for every
-- operator Φ, of a small height regular for the stages of Φ's codes
-- (Heights.Stages), under extensionality for families of types, with no
-- induction–recursion. A node is regular for the stages of a layer Λ
-- (Regular) when it has a child and every code of its stage, with a
-- family of its codes indexed by that code's decoding, lies below one
-- child, each strictly:
--
--   a : Stage Λ t, b : decoding Λ t a → Stage Λ t
--     ⊢ Σ z. f (pr₁ a) ⊏ f z × Π y. f (pr₁ (b y)) ⊏ f z.
--
-- At a regular node of a functorial layer with Φ's codes the stage is a
-- closure of the ambient formers and Φ (`closure`): each former and Φ at a
-- family of codes is a code of Φ at the bounding child, over the family
-- raised into that child's stage (`over`, `head`, `tail`, `moved`,
-- `coded`). So heights regular for the stages of Φ's codes give the rule
-- (`mahlo`). Conversely, a closure L that names every code of a layer's
-- stage at the fan of the heights of L's trees makes that fan regular
-- (`trees-regular`): a code and a family of codes lie below the tree over
-- L's two code that joins the code's own tree with the tree of the family's
-- trees (`joined`, `gathered`). A closure of Φ names the stages of Φ's
-- codes (`named`, `named-β`), so the rule gives heights regular for them
-- (`regular`). A closure of any operator names the operator's own stages,
-- the stage over each of its trees being a family of its codes (`staged`,
-- `member`, `stage-name`), so the rule gives heights regular for the stages
-- of every operator (`reflection-regular`). A node over a single child is
-- not regular (`successor-irregular`). At a regular node the witnesses of a
-- total relation upward closed along ⊏ are the decoding of no stage code
-- (`witness-below`, `witnesses-are-not-decodings`): regularity for
-- relations (Heights.Univalent) is not had by collecting all witnesses into
-- one code.

open import SPT.Base
open import SPT.Foundation.Covers using (Covered; covered-is-not-refuted)
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Isomorphisms using
  (_≅_; forward; backward; forward-backward)
import SPT.Foundation.Tree as Tree
import SPT.Mahlo.Ambient as Ambient
open import SPT.Foundation.Tree.W using (W; sup)
open import SPT.Mahlo.DS.Naming using (recast)
open import SPT.Mahlo.DS.Realization.Family using (cast)
import SPT.Mahlo.Specification as Specification
open import SPT.OrdinalGeometry.Height.Ordinals using (Height)
open import SPT.OrdinalGeometry.Height.Simulation using
  (_⊑_; _⊏_; under; ⊑-refl; ⊏-trans; ⊏-irrefl)
open import SPT.Mahlo.Heights.Stages using
  ( Code; decode; codes; Has-Codes; Functorial; codes-have-codes
  ; Stage; decoding; raise; raised; family; reidentified
  ; empty; unit; two; natural; product; sum; tree; result; identity
  ; branch )
open import SPT.Mahlo.Heights.Stages.Map using (codes-are-functorial)

------------------------------------------------------------------------
-- Regular heights

-- A node regular for the stages of the layer Λ.
record Regular {ℓ : Level} (Λ : Ambient.Operator ℓ) (X : Set ℓ)
  (f : X → Height ℓ) : Set (lsuc ℓ) where
  field
    point : X
    bound :
      (a : Stage Λ (Tree.node X f))
      (b : decoding Λ (Tree.node X f) a → Stage Λ (Tree.node X f))
      → Σ X
          (λ z →
            (f (pr₁ a) ⊏ f z)
            × ((y : decoding Λ (Tree.node X f) a) → f (pr₁ (b y)) ⊏ f z))

------------------------------------------------------------------------
-- The closure at a regular node

module _
  {ℓ : Level} {Φ Λ : Ambient.Operator ℓ}
  (extensionality : (X : Set ℓ) → FunExt X (λ _ → Set ℓ))
  (has-codes : Has-Codes Φ Λ) (functorial : Functorial Λ)
  {X : Set ℓ} {f : X → Height ℓ} (regular : Regular Λ X f)
  where

  -- The child above a family of the stage's codes.
  over :
    Specification.Family
      (Specification.Decode (λ (A : Set ℓ) → A)
        (decoding Λ (Tree.node X f)))
    → X
  over F = pr₁ (Regular.bound regular (pr₁ F) (pr₂ F))

  -- The family's index, raised into that child's stage.
  head :
    (F :
      Specification.Family
        (Specification.Decode (λ (A : Set ℓ) → A)
          (decoding Λ (Tree.node X f))))
    → Stage Λ (f (over F))
  head F =
    raise functorial (pr₁ (pr₂ (Regular.bound regular (pr₁ F) (pr₂ F))))
      (pr₂ (pr₁ F))

  head-β :
    (F :
      Specification.Family
        (Specification.Decode (λ (A : Set ℓ) → A)
          (decoding Λ (Tree.node X f))))
    → decoding Λ (f (over F)) (head F)
      ＝ decoding Λ (Tree.node X f) (pr₁ F)
  head-β F =
    raised functorial (pr₁ (pr₂ (Regular.bound regular (pr₁ F) (pr₂ F))))
      (pr₂ (pr₁ F))

  -- Its members, raised along the index's identity.
  tail :
    (F :
      Specification.Family
        (Specification.Decode (λ (A : Set ℓ) → A)
          (decoding Λ (Tree.node X f))))
    → decoding Λ (f (over F)) (head F) → Stage Λ (f (over F))
  tail F y =
    raise functorial
      (pr₂ (pr₂ (Regular.bound regular (pr₁ F) (pr₂ F)))
        (cast (head-β F) y))
      (pr₂ (pr₂ F (cast (head-β F) y)))

  -- The raised family is the given one.
  moved :
    (F :
      Specification.Family
        (Specification.Decode (λ (A : Set ℓ) → A)
          (decoding Λ (Tree.node X f))))
    → _＝_ {A = Specification.Family (λ (A : Set ℓ) → A)}
        ( decoding Λ (f (over F)) (head F)
        , (λ y → decoding Λ (f (over F)) (tail F y)))
        (Specification.map (λ (A : Set ℓ) → A)
          (decoding Λ (Tree.node X f)) F)
  moved F =
    family extensionality (head-β F)
      (λ y →
        raised functorial
          (pr₂ (pr₂ (Regular.bound regular (pr₁ F) (pr₂ F)))
            (cast (head-β F) y))
          (pr₂ (pr₂ F (cast (head-β F) y))))

  -- A code of Φ over a child's stage, as a code of the node.
  coded :
    (x : X) → Code Φ (Stage Λ (f x)) (decoding Λ (f x))
    → Stage Λ (Tree.node X f)
  coded x c = x , Has-Codes.code has-codes c

  coded-β :
    (x : X) (c : Code Φ (Stage Λ (f x)) (decoding Λ (f x)))
    → decoding Λ (Tree.node X f) (coded x c) ＝ decode c
  coded-β x c = Has-Codes.code-β has-codes c

  closure :
    Specification.Closure (Ambient.formers ℓ) Φ (Stage Λ (Tree.node X f))
  closure = record
    { interpret = decoding Λ (Tree.node X f)
    ; empty =
        coded (Regular.point regular) empty
        , coded-β (Regular.point regular) empty
    ; unit =
        coded (Regular.point regular) unit
        , coded-β (Regular.point regular) unit
    ; two =
        coded (Regular.point regular) two
        , coded-β (Regular.point regular) two
    ; natural =
        coded (Regular.point regular) natural
        , coded-β (Regular.point regular) natural
    ; product = λ F →
        coded (over F) (product (head F) (tail F))
        , ( coded-β (over F) (product (head F) (tail F))
          ∙ ap (Specification.Formers.product (Ambient.formers ℓ))
              (moved F))
    ; sum = λ F →
        coded (over F) (sum (head F) (tail F))
        , ( coded-β (over F) (sum (head F) (tail F))
          ∙ ap (Specification.Formers.sum (Ambient.formers ℓ)) (moved F))
    ; tree = λ F →
        coded (over F) (tree (head F) (tail F))
        , ( coded-β (over F) (tree (head F) (tail F))
          ∙ ap (Specification.Formers.tree (Ambient.formers ℓ)) (moved F))
    ; identity = λ a x y →
        coded (over (a , (λ _ → a)))
          (identity (head (a , (λ _ → a)))
            (cast (head-β (a , (λ _ → a)) ⁻¹) x)
            (cast (head-β (a , (λ _ → a)) ⁻¹) y))
        , ( coded-β (over (a , (λ _ → a)))
              (identity (head (a , (λ _ → a)))
                (cast (head-β (a , (λ _ → a)) ⁻¹) x)
                (cast (head-β (a , (λ _ → a)) ⁻¹) y))
          ∙ reidentified (head-β (a , (λ _ → a))) x y)
    ; inner = λ F →
        coded (over F) (result (head F) (tail F))
        , (λ i →
            coded (over F)
              (branch (head F) (tail F)
                (cast (coded-β (over F) (result (head F) (tail F))) i)))
    ; inner-β = λ F →
        family extensionality
          (coded-β (over F) (result (head F) (tail F)))
          (λ i →
            coded-β (over F)
              (branch (head F) (tail F)
                (cast (coded-β (over F) (result (head F) (tail F))) i)))
        ∙ ap Φ (moved F)
    }

-- Heights regular for the stages of Φ's codes give the Mahlo rule.
mahlo :
  {ℓ : Level}
  (extensionality : (X : Set ℓ) → FunExt X (λ _ → Set ℓ))
  → ((Φ : Ambient.Operator ℓ)
    → Σ (Set ℓ) (λ X → Σ (X → Height ℓ) (Regular (codes Φ) X)))
  → Specification.Mahlo (Ambient.formers ℓ)
mahlo extensionality heights = record
  { reflect = λ Φ → record
      { carrier =
          Stage (codes Φ)
            (Tree.node (pr₁ (heights Φ)) (pr₁ (pr₂ (heights Φ))))
      ; closure =
          closure extensionality (codes-have-codes Φ)
            (codes-are-functorial extensionality Φ) (pr₂ (pr₂ (heights Φ)))
      }
  }

------------------------------------------------------------------------
-- A closure names the stage codes

-- Φ's members along an identity of families.
along :
  {ℓ : Level} {G H : Specification.Family (λ (A : Set ℓ) → A)}
  (e : G ＝ H) (i : pr₁ H)
  → pr₂ G (cast (ap pr₁ e ⁻¹) i) ＝ pr₂ H i
along refl i = refl

-- Two trees side by side over a closure's two code (`pick`), and the tree
-- joining them (`v ⊔⟨ L ⟩ w`).

module _
  {ℓ : Level} {Φ : Ambient.Operator ℓ} {K : Set ℓ}
  where

  pick :
    (L : Specification.Closure (Ambient.formers ℓ) Φ K)
    → W K (Specification.Closure.interpret L)
    → W K (Specification.Closure.interpret L)
    → Lift ℓ 𝟚 → W K (Specification.Closure.interpret L)
  pick L v w (lift ₀) = v
  pick L v w (lift ₁) = w

  joined :
    (L : Specification.Closure (Ambient.formers ℓ) Φ K)
    → W K (Specification.Closure.interpret L)
    → W K (Specification.Closure.interpret L)
    → W K (Specification.Closure.interpret L)
  joined L v w =
    sup (pr₁ (Specification.Closure.two L))
      (λ y → pick L v w (cast (pr₂ (Specification.Closure.two L)) y))

  infixl 35 joined
  syntax joined L v w = v ⊔⟨ L ⟩ w

module _
  {ℓ : Level} {Φ : Ambient.Operator ℓ} {K : Set ℓ}
  (L : Specification.Closure (Ambient.formers ℓ) Φ K)
  where

  open Specification.Closure L using (interpret)

  -- The trees of L's codes, and their heights.
  embed : W K interpret → Height ℓ
  embed (sup k g) = Tree.node (interpret k) (λ y → embed (g y))

  joined-left : (v w : W K interpret) → embed v ⊏ embed (v ⊔⟨ L ⟩ w)
  joined-left v w =
    under (cast (pr₂ (Specification.Closure.two L) ⁻¹) (lift ₀))
      (transport (λ u → embed v ⊑ embed (pick L v w u))
        (recast (pr₂ (Specification.Closure.two L)) (lift ₀) ⁻¹)
        (⊑-refl (embed v)))

  joined-right : (v w : W K interpret) → embed w ⊏ embed (v ⊔⟨ L ⟩ w)
  joined-right v w =
    under (cast (pr₂ (Specification.Closure.two L) ⁻¹) (lift ₁))
      (transport (λ u → embed w ⊑ embed (pick L v w u))
        (recast (pr₂ (Specification.Closure.two L)) (lift ₁) ⁻¹)
        (⊑-refl (embed w)))

  module _
    (extensionality : (X : Set ℓ) → FunExt X (λ _ → Set ℓ))
    where

    mutual
      -- L's name of each code of the stages of Φ's codes.
      named : (s : Height ℓ) → Stage (codes Φ) s → K
      named (Tree.hole ())
      named (Tree.node X f) (x , c) = named-code (f x) c

      named-code :
        (s : Height ℓ) → Code Φ (Stage (codes Φ) s) (decoding (codes Φ) s)
        → K
      named-code s empty = pr₁ (Specification.Closure.empty L)
      named-code s unit = pr₁ (Specification.Closure.unit L)
      named-code s two = pr₁ (Specification.Closure.two L)
      named-code s natural = pr₁ (Specification.Closure.natural L)
      named-code s (product a b) =
        pr₁ (Specification.Closure.product L (named-family s a b))
      named-code s (sum a b) =
        pr₁ (Specification.Closure.sum L (named-family s a b))
      named-code s (tree a b) =
        pr₁ (Specification.Closure.tree L (named-family s a b))
      named-code s (result a b) =
        pr₁ (Specification.Closure.inner L (named-family s a b))
      named-code s (identity a x y) =
        pr₁
          (Specification.Closure.identity L (named s a)
            (cast (named-β s a ⁻¹) x) (cast (named-β s a ⁻¹) y))
      named-code s (branch a b i) =
        pr₂ (Specification.Closure.inner L (named-family s a b))
          (cast (ap pr₁ (inner-named s a b) ⁻¹) i)

      -- A family of stage codes, named in L.
      named-family :
        (s : Height ℓ) (a : Stage (codes Φ) s)
        (b : decoding (codes Φ) s a → Stage (codes Φ) s)
        → Specification.Family
            (Specification.Decode (λ (A : Set ℓ) → A) interpret)
      named-family s a b =
        named s a , (λ y → named s (b (cast (named-β s a) y)))

      named-β :
        (s : Height ℓ) (u : Stage (codes Φ) s)
        → interpret (named s u) ＝ decoding (codes Φ) s u
      named-β (Tree.hole ())
      named-β (Tree.node X f) (x , c) = named-code-β (f x) c

      named-code-β :
        (s : Height ℓ)
        (c : Code Φ (Stage (codes Φ) s) (decoding (codes Φ) s))
        → interpret (named-code s c) ＝ decode c
      named-code-β s empty = pr₂ (Specification.Closure.empty L)
      named-code-β s unit = pr₂ (Specification.Closure.unit L)
      named-code-β s two = pr₂ (Specification.Closure.two L)
      named-code-β s natural = pr₂ (Specification.Closure.natural L)
      named-code-β s (product a b) =
        pr₂ (Specification.Closure.product L (named-family s a b))
        ∙ ap (Specification.Formers.product (Ambient.formers ℓ))
            (named-moved s a b)
      named-code-β s (sum a b) =
        pr₂ (Specification.Closure.sum L (named-family s a b))
        ∙ ap (Specification.Formers.sum (Ambient.formers ℓ))
            (named-moved s a b)
      named-code-β s (tree a b) =
        pr₂ (Specification.Closure.tree L (named-family s a b))
        ∙ ap (Specification.Formers.tree (Ambient.formers ℓ))
            (named-moved s a b)
      named-code-β s (result a b) = ap pr₁ (inner-named s a b)
      named-code-β s (identity a x y) =
        pr₂
          (Specification.Closure.identity L (named s a)
            (cast (named-β s a ⁻¹) x) (cast (named-β s a ⁻¹) y))
        ∙ reidentified (named-β s a) x y
      named-code-β s (branch a b i) = along (inner-named s a b) i

      -- The named family decodes to the stage family.
      named-moved :
        (s : Height ℓ) (a : Stage (codes Φ) s)
        (b : decoding (codes Φ) s a → Stage (codes Φ) s)
        → _＝_ {A = Specification.Family (λ (A : Set ℓ) → A)}
            (Specification.map (λ (A : Set ℓ) → A) interpret
              (named-family s a b))
            (decoding (codes Φ) s a , (λ x → decoding (codes Φ) s (b x)))
      named-moved s a b =
        family extensionality (named-β s a)
          (λ y → named-β s (b (cast (named-β s a) y)))

      -- L's inner family at the named family, and Φ at the stage family.
      inner-named :
        (s : Height ℓ) (a : Stage (codes Φ) s)
        (b : decoding (codes Φ) s a → Stage (codes Φ) s)
        → _＝_ {A = Specification.Family (λ (A : Set ℓ) → A)}
            (Specification.map (λ (A : Set ℓ) → A) interpret
              (Specification.Closure.inner L (named-family s a b)))
            (Φ (decoding (codes Φ) s a , (λ x → decoding (codes Φ) s (b x))))
      inner-named s a b =
        Specification.Closure.inner-β L (named-family s a b)
        ∙ ap Φ (named-moved s a b)

    mutual
      -- The stage of Φ over a tree of L's codes, as a family of L's codes.
      staged :
        W K interpret →
        Specification.Family
          (Specification.Decode (λ (A : Set ℓ) → A) interpret)
      staged (sup k g) =
        pr₁ (Specification.Closure.sum L (layers (sup k g)))
        , (λ s →
            member (g (pr₁ (cast (indexed (sup k g)) s)))
              (pr₂ (cast (indexed (sup k g)) s)))

      -- Φ's index at the stages of the children, as L's codes over the
      -- root code.
      layers :
        W K interpret →
        Specification.Family
          (Specification.Decode (λ (A : Set ℓ) → A) interpret)
      layers (sup k g) =
        k , (λ y → pr₁ (Specification.Closure.inner L (staged (g y))))

      -- The sum of the layers decodes to the stage.
      indexed :
        (w : W K interpret) →
        interpret (pr₁ (Specification.Closure.sum L (layers w)))
          ＝ Stage Φ (embed w)
      indexed (sup k g) =
        pr₂ (Specification.Closure.sum L (layers (sup k g)))
        ∙ ap (Σ (interpret k))
            (extensionality (interpret k)
              (λ y →
                interpret
                  (pr₁ (Specification.Closure.inner L (staged (g y)))))
              (λ y →
                pr₁ (Φ (Stage Φ (embed (g y)) , decoding Φ (embed (g y)))))
              (λ y → ap pr₁ (layered (g y))))

      -- L's inner family at the staged family is Φ at the stage.
      layered :
        (w : W K interpret) →
        _＝_ {A = Specification.Family (λ (A : Set ℓ) → A)}
          (Specification.map (λ (A : Set ℓ) → A) interpret
            (Specification.Closure.inner L (staged w)))
          (Φ (Stage Φ (embed w) , decoding Φ (embed w)))
      layered w =
        Specification.Closure.inner-β L (staged w) ∙ ap Φ (staged-β w)

      -- L's name of each code of Φ over the stage of a tree.
      member :
        (w : W K interpret) →
        pr₁ (Φ (Stage Φ (embed w) , decoding Φ (embed w))) → K
      member w u =
        pr₂ (Specification.Closure.inner L (staged w))
          (cast (ap pr₁ (layered w) ⁻¹) u)

      member-β :
        (w : W K interpret)
        (u : pr₁ (Φ (Stage Φ (embed w) , decoding Φ (embed w)))) →
        interpret (member w u)
          ＝ pr₂ (Φ (Stage Φ (embed w) , decoding Φ (embed w))) u
      member-β w u = along (layered w) u

      -- The staged family decodes to the stage.
      staged-β :
        (w : W K interpret) →
        _＝_ {A = Specification.Family (λ (A : Set ℓ) → A)}
          (Specification.map (λ (A : Set ℓ) → A) interpret (staged w))
          (Stage Φ (embed w) , decoding Φ (embed w))
      staged-β (sup k g) =
        family extensionality (indexed (sup k g))
          (λ s →
            member-β (g (pr₁ (cast (indexed (sup k g)) s)))
              (pr₂ (cast (indexed (sup k g)) s)))

    -- L's name of every code of Φ's stage at the fan of its trees.
    stage-name : Stage Φ (Tree.node (W K interpret) embed) → K
    stage-name a = member (pr₁ a) (pr₂ a)

    stage-name-β :
      (a : Stage Φ (Tree.node (W K interpret) embed)) →
      interpret (stage-name a) ＝ decoding Φ (Tree.node (W K interpret) embed) a
    stage-name-β a = member-β (pr₁ a) (pr₂ a)

  ----------------------------------------------------------------------
  -- The fan of the trees is regular

  module _
    (Λ : Ambient.Operator ℓ)
    (name : Stage Λ (Tree.node (W K interpret) embed) → K)
    (name-β :
      (a : Stage Λ (Tree.node (W K interpret) embed)) →
      interpret (name a) ＝ decoding Λ (Tree.node (W K interpret) embed) a)
    where

    -- The tree of a family's trees, over L's name of the index's
    -- decoding.
    gathered :
      (a : Stage Λ (Tree.node (W K interpret) embed))
      → (decoding Λ (Tree.node (W K interpret) embed) a
        → Stage Λ (Tree.node (W K interpret) embed))
      → W K interpret
    gathered a b = sup (name a) (λ y → pr₁ (b (cast (name-β a) y)))

    gathered-above :
      (a : Stage Λ (Tree.node (W K interpret) embed))
      (b :
        decoding Λ (Tree.node (W K interpret) embed) a
        → Stage Λ (Tree.node (W K interpret) embed))
      (y : decoding Λ (Tree.node (W K interpret) embed) a)
      → embed (pr₁ (b y)) ⊏ embed (gathered a b)
    gathered-above a b y =
      under (cast (name-β a ⁻¹) y)
        (transport (λ u → embed (pr₁ (b y)) ⊑ embed (pr₁ (b u)))
          (recast (name-β a) y ⁻¹)
          (⊑-refl (embed (pr₁ (b y)))))

    trees-regular : Regular Λ (W K interpret) embed
    trees-regular = record
      { point =
          sup (pr₁ (Specification.Closure.empty L))
            (λ y →
              𝟘-elim (lower (cast (pr₂ (Specification.Closure.empty L)) y)))
      ; bound = λ a b →
          (pr₁ a ⊔⟨ L ⟩ gathered a b)
          , ( joined-left (pr₁ a) (gathered a b)
            , (λ y →
                ⊏-trans (gathered-above a b y)
                  (joined-right (pr₁ a) (gathered a b))))
      }

-- The Mahlo rule gives heights regular for the stages of Φ's codes, at the
-- fan of the trees of Φ's reflection.
regular :
  {ℓ : Level}
  (extensionality : (X : Set ℓ) → FunExt X (λ _ → Set ℓ))
  → Specification.Mahlo (Ambient.formers ℓ)
  → (Φ : Ambient.Operator ℓ)
  → Σ (Set ℓ) (λ X → Σ (X → Height ℓ) (Regular (codes Φ) X))
regular extensionality M Φ =
  let L = Specification.Reflection.closure (Specification.Mahlo.reflect M Φ)
      t = Tree.node
            (W
              (Specification.Reflection.carrier
                (Specification.Mahlo.reflect M Φ))
              (Specification.Closure.interpret L))
            (embed L)
  in
  W (Specification.Reflection.carrier (Specification.Mahlo.reflect M Φ))
    (Specification.Closure.interpret L)
  , embed L
  , trees-regular L (codes Φ) (named L extensionality t)
      (named-β L extensionality t)

-- The Mahlo rule gives heights regular for the stages of every operator,
-- at the fan of the trees of its reflection.
reflection-regular :
  {ℓ : Level}
  (extensionality : (X : Set ℓ) → FunExt X (λ _ → Set ℓ))
  → Specification.Mahlo (Ambient.formers ℓ)
  → (Λ : Ambient.Operator ℓ)
  → Σ (Set ℓ) (λ X → Σ (X → Height ℓ) (Regular Λ X))
reflection-regular extensionality M Λ =
  let L = Specification.Reflection.closure (Specification.Mahlo.reflect M Λ)
  in
  W (Specification.Reflection.carrier (Specification.Mahlo.reflect M Λ))
    (Specification.Closure.interpret L)
  , embed L
  , trees-regular L Λ (stage-name L extensionality)
      (stage-name-β L extensionality)

------------------------------------------------------------------------
-- Discriminator: regularity is a condition

-- A node over one child is not regular: a code at that child would lie
-- strictly below the child itself.
successor-irregular :
  {ℓ : Level} {Φ Λ : Ambient.Operator ℓ} → Has-Codes Φ Λ → (s : Height ℓ)
  → ¬ Regular Λ (Lift ℓ 𝟙) (λ _ → s)
successor-irregular {ℓ} {Φ} {Λ} has-codes s regular =
  let a : Stage Λ (Tree.node (Lift ℓ 𝟙) (λ _ → s))
      a = Regular.point regular , Has-Codes.code has-codes empty
  in ⊏-irrefl s (pr₁ (pr₂ (Regular.bound regular a (λ _ → a))))

------------------------------------------------------------------------
-- Discriminator: witnesses are not stage decodings

-- Were the witnesses Σ y. Σ x. P y x of a relation P from a code's
-- decoding to the children the decoding of a stage code c, the children
-- read off c's points would form a family of stage codes, and its bound
-- would lie strictly above the child of every witness.

module _
  {ℓ : Level} {Φ Λ : Ambient.Operator ℓ} (has-codes : Has-Codes Φ Λ)
  {X : Set ℓ} {f : X → Height ℓ} (regular : Regular Λ X f)
  (a c : Stage Λ (Tree.node X f))
  (P : decoding Λ (Tree.node X f) a → X → Set ℓ)
  (e :
    decoding Λ (Tree.node X f) c
      ≅ Σ (decoding Λ (Tree.node X f) a) (λ y → Σ X (P y)))
  where

  witness-below :
    (s : Σ (decoding Λ (Tree.node X f) a) (λ y → Σ X (P y))) →
    f (pr₁ (pr₂ s))
      ⊏ f (pr₁ (Regular.bound regular c
            (λ v →
              pr₁ (pr₂ (forward e v)) , Has-Codes.code has-codes empty)))
  witness-below s =
    transport
      (λ u →
        f (pr₁ (pr₂ u))
          ⊏ f (pr₁ (Regular.bound regular c
                (λ v →
                  pr₁ (pr₂ (forward e v)) , Has-Codes.code has-codes empty))))
      (forward-backward e s)
      (pr₂ (pr₂ (Regular.bound regular c
        (λ v → pr₁ (pr₂ (forward e v)) , Has-Codes.code has-codes empty)))
        (backward e s))

-- When P is total and upward closed along ⊏, a witness at a point gives
-- one at the bound itself, which would then lie strictly below itself.
witnesses-are-not-decodings :
  {ℓ : Level} {Φ Λ : Ambient.Operator ℓ} (has-codes : Has-Codes Φ Λ)
  {X : Set ℓ} {f : X → Height ℓ} →
  Regular Λ X f →
  (a : Stage Λ (Tree.node X f))
  (P : decoding Λ (Tree.node X f) a → X → Set ℓ) →
  ((y : decoding Λ (Tree.node X f) a) (x z : X) →
    P y x → f x ⊏ f z → P y z) →
  ((y : decoding Λ (Tree.node X f) a) → Covered ℓ (Σ X (P y))) →
  Covered ℓ (decoding Λ (Tree.node X f) a) →
  (c : Stage Λ (Tree.node X f)) →
  ¬ (decoding Λ (Tree.node X f) c
      ≅ Σ (decoding Λ (Tree.node X f) a) (λ y → Σ X (P y)))
witnesses-are-not-decodings has-codes {X} {f} regular a P upward total
  inhabited c e =
  covered-is-not-refuted inhabited
    (λ y →
      covered-is-not-refuted (total y)
        (λ q →
          let z = pr₁ (Regular.bound regular c
                    (λ v →
                      pr₁ (pr₂ (forward e v))
                      , Has-Codes.code has-codes empty))
          in
          ⊏-irrefl (f z)
            (witness-below has-codes regular a c P e
              (y , z ,
                upward y (pr₁ q) z (pr₂ q)
                  (witness-below has-codes regular a c P e (y , q))))))
