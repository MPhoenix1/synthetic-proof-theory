{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Naming where

-- The ambient Mahlo rule gives the Mahlo rule for every family (C , D) that
-- admits the small types, under extensionality for families of names. A
-- family admits the small types when every small type is a retract of the
-- decoding of a name (`Admission`); a family naming every small type does
-- (`naming`). A closure moves along a retraction of carriers (`transfer`).
--
-- For formers Q and an operator Φ, a closure L of the ambient operator of
-- their requests (Naming.Trees.requests) gives the codes: a family of L's
-- codes with a request over it, read as the element it selects (`Value`,
-- `sort`). Every former and Φ at a family of codes is one tree (`node`):
-- the family joins the index's family and the members' families with L's
-- name of the index's decoding (`gather`, `first`, `joined`), the node sits
-- at that name, and each request is carried into the joined family
-- (`carry-index`, `carry-member`). The node's input is the given family
-- along extensionality (`node-β`); every selection of its output is a code
-- by refl, so the decoding equations are ap of `node-β`. The constant and
-- identity formers name by refl. Hence the closure (`closure`) and the
-- theorem (`mahlo`). The two-sorted family is an instance (`sorted`), with
-- outputs in O alone (`outputs`, `outputs-law`) and from smallness for
-- outputs in types (`types`, `smallness`).
--
-- Conversely, for a family naming every small type whose formers decode
-- as the ambient ones (DecodingLaws), its Mahlo rule gives the ambient
-- rule: an ambient operator acts on the names of its types (`lifted`), and
-- a closure under it decodes to an ambient closure (`typed`, `ambient`).
-- So for such a family the two rules are equivalent, under extensionality;
-- the two-sorted family is one (`sorted-laws`, `unsorted`). No
-- induction–recursion.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
import SPT.Mahlo.Ambient as Ambient
open import SPT.Foundation.Tree.W using (sup)
open import SPT.Mahlo.Decoding using (DecodingLaws)
import SPT.Mahlo.Specification as Specification

open import SPT.IR.Algebra using (Algebra; Law)
import SPT.Mahlo.DS.Ambient as Types
open import SPT.IR.Description using (Desc; carrier; index)
import SPT.Mahlo.DS.Realization.Family as Families
open import SPT.Mahlo.DS.Realization.Family using (cast; cancel)
import SPT.IR.Smallness as Ambient-Smallness
open import SPT.Mahlo.DS.Sorted using (Sort; decode)
import SPT.Mahlo.DS.Sorted as Sorted
import SPT.Mahlo.DS.Sorted.Mahlo as Two-sorted
open import SPT.Mahlo.DS.Sorted.Smallness using (Smallness)
open import SPT.Mahlo.DS.Naming.Trees using
  ( Nullary; empty; unit; two; natural
  ; Unary; product; sum; wellfounded; operator
  ; applied; identity; Stage; leaf; Output; Selection; pair
  ; layer; Request; request; requested; requests; carry; carried)

------------------------------------------------------------------------
-- Families admitting the small types

recast :
  {ℓ : Level} {A B : Set ℓ} (e : A ＝ B) (x : B)
  → cast e (cast (e ⁻¹) x) ＝ x
recast refl x = refl

-- Every small type is a retract of the decoding of a name.
record Admission {κ ℓ : Level} {C : Set κ} (D : C → Set ℓ)
  : Set (κ ⊔ lsuc ℓ) where
  field
    admit : Set ℓ → C
    out : (X : Set ℓ) → D (admit X) → X
    into : (X : Set ℓ) → X → D (admit X)
    out-into : (X : Set ℓ) (x : X) → out X (into X x) ＝ x

-- A family naming every small type admits them.
naming :
  {κ ℓ : Level} {C : Set κ} (D : C → Set ℓ)
  → ((X : Set ℓ) → Specification.Name D X) → Admission D
naming D n = record
  { admit = λ X → pr₁ (n X)
  ; out = λ X → cast (pr₂ (n X))
  ; into = λ X → cast (pr₂ (n X) ⁻¹)
  ; out-into = λ X → recast (pr₂ (n X))
  }

------------------------------------------------------------------------
-- A closure moves along a retraction of carriers

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  {Q : Specification.Formers C D} {Φ : Specification.Operator D}
  (extensionality : (X : Set ℓ) → FunExt X (λ _ → C))
  {X Y : Set ℓ} (out : Y → X) (into : X → Y)
  (out-into : (x : X) → out (into x) ＝ x)
  (M : Specification.Closure Q Φ X)
  where

  open Specification.Closure M using (interpret)

  renamed :
    (c : C) → Specification.Name interpret c
    → Specification.Name (λ y → interpret (out y)) c
  renamed c n = into (pr₁ n) , (ap interpret (out-into (pr₁ n)) ∙ pr₂ n)

  pushed :
    Specification.Family
      (Specification.Decode D (λ y → interpret (out y)))
    → Specification.Family (Specification.Decode D interpret)
  pushed F = out (pr₁ F) , (λ x → out (pr₂ F x))

  pulled :
    Specification.Family (Specification.Decode D interpret)
    → Specification.Family
        (Specification.Decode D (λ y → interpret (out y)))
  pulled G =
    into (pr₁ G) ,
    (λ x →
      into (pr₂ G (cast (ap D (ap interpret (out-into (pr₁ G)))) x)))

  pulled-β :
    (G : Specification.Family (Specification.Decode D interpret))
    → Specification.map D (λ y → interpret (out y)) (pulled G)
      ＝ Specification.map D interpret G
  pulled-β G =
    pair D extensionality (ap interpret (out-into (pr₁ G)))
      (λ x →
        ap interpret
          (out-into
            (pr₂ G (cast (ap D (ap interpret (out-into (pr₁ G)))) x))))

  transfer : Specification.Closure Q Φ Y
  transfer = record
    { interpret = λ y → interpret (out y)
    ; empty =
        renamed (Specification.Formers.empty Q)
          (Specification.Closure.empty M)
    ; unit =
        renamed (Specification.Formers.unit Q)
          (Specification.Closure.unit M)
    ; two =
        renamed (Specification.Formers.two Q)
          (Specification.Closure.two M)
    ; natural =
        renamed (Specification.Formers.natural Q)
          (Specification.Closure.natural M)
    ; product = λ F →
        renamed
          (Specification.Formers.product Q
            (Specification.map D interpret (pushed F)))
          (Specification.Closure.product M (pushed F))
    ; sum = λ F →
        renamed
          (Specification.Formers.sum Q
            (Specification.map D interpret (pushed F)))
          (Specification.Closure.sum M (pushed F))
    ; tree = λ F →
        renamed
          (Specification.Formers.tree Q
            (Specification.map D interpret (pushed F)))
          (Specification.Closure.tree M (pushed F))
    ; identity = λ a x y →
        renamed (Specification.Formers.identity Q (interpret (out a)) x y)
          (Specification.Closure.identity M (out a) x y)
    ; inner = λ F → pulled (Specification.Closure.inner M (pushed F))
    ; inner-β = λ F →
        pulled-β (Specification.Closure.inner M (pushed F))
        ∙ Specification.Closure.inner-β M (pushed F)
    }

------------------------------------------------------------------------
-- Codes over a closure of the requests

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Specification.Formers C D) (Φ : Specification.Operator D)
  {K : Set ℓ}
  (L : Specification.Closure (Ambient.formers ℓ) (requests Q Φ) K)
  where

  open Specification.Closure L using (interpret)

  -- A family of L's codes with a request over it.
  record Value : Set ℓ where
    field
      family :
        Specification.Family (Specification.Decode (λ X → X) interpret)
      origin : Request Q Φ (index (Families.view L family))

  sort : Value → C
  sort v = requested Q Φ (Value.origin v)

  -- L names the decoding of each value.
  decoded : (v : Value) → Specification.Name interpret (D (sort v))
  decoded v = Families.action L (Value.family v) (Value.origin v)

  -- A family of L's codes with a stage and a tree over it.
  record Node : Set ℓ where
    field
      family :
        Specification.Family (Specification.Decode (λ X → X) interpret)
      stage :
        Stage (carrier (Families.view L family))
          (index (Families.view L family))
      tree : pr₁ (layer Q Φ (index (Families.view L family)) stage)

  output : Node → Output ℓ C
  output n =
    pr₂ (layer Q Φ (index (Families.view L (Node.family n))) (Node.stage n))
      (Node.tree n)

  selecting : (n : Node) → Selection (output n) → Value
  selecting n i = record
    { family = Node.family n
    ; origin = request (Node.stage n) (Node.tree n) i
    }

  constant-node : Nullary → Node
  constant-node t = record
    { family = Families.unit L
    ; stage = leaf (index (Families.view L (Families.unit L))) t
    ; tree = lift ⋆
    }

  identity-node : (a : Value) (p q : D (sort a)) → Node
  identity-node a p q = record
    { family = Value.family a
    ; stage = sup identity (λ _ → Request.stage (Value.origin a))
    ; tree =
        ( Request.tree (Value.origin a)
        , Request.selection (Value.origin a)) ,
        (p , q)
    }

  ----------------------------------------------------------------------
  -- The family joining an index with its members

  gathered :
    (c : Value) (d : D (sort c) → Value)
    → Specification.Name interpret
        (Σ (D (sort c)) (λ z → interpret (pr₁ (Value.family (d z)))))
  gathered c d =
    Families.sum L (D (sort c)) (decoded c) (λ z → pr₁ (Value.family (d z)))

  gather :
    (c : Value) → (D (sort c) → Value)
    → Specification.Family (Specification.Decode (λ X → X) interpret)
  gather c d =
    pr₁ (gathered c d) ,
    (λ x →
      pr₂ (Value.family (d (pr₁ (cast (pr₂ (gathered c d)) x))))
        (pr₂ (cast (pr₂ (gathered c d)) x)))

  -- The index's family, adjoined to the members'.
  first :
    (c : Value) (d : D (sort c) → Value)
    → Families.Extension L (pr₂ (Value.family c)) (gather c d)
  first c d =
    Families.extend L (pr₁ (Value.family c)) refl (pr₂ (Value.family c))
      (gather c d)

  -- L's name of the index's decoding, adjoined: the node's label.
  joined :
    (c : Value) (d : D (sort c) → Value)
    → Families.Extension L (λ (_ : Lift ℓ 𝟙) → pr₁ (decoded c))
        (Families.Extension.family (first c d))
  joined c d =
    Families.extend L (pr₁ (Specification.Closure.unit L))
      (pr₂ (Specification.Closure.unit L)) (λ _ → pr₁ (decoded c))
      (Families.Extension.family (first c d))

  pointed :
    (c : Value) (d : D (sort c) → Value)
    → index (Families.view L (Families.Extension.family (joined c d)))
        (Families.Extension.left (joined c d) (lift ⋆))
      ＝ D (sort c)
  pointed c d =
    ap (λ h → h (lift ⋆)) (Families.Extension.left-β (joined c d))
    ∙ pr₂ (decoded c)

  index-inclusion :
    (c : Value) (d : D (sort c) → Value)
    → interpret (pr₁ (Value.family c))
    → carrier (Families.view L (Families.Extension.family (joined c d)))
  index-inclusion c d p =
    Families.Extension.right (joined c d)
      (Families.Extension.left (first c d) p)

  index-included :
    (c : Value) (d : D (sort c) → Value)
    → (λ p →
        index (Families.view L (Families.Extension.family (joined c d)))
          (index-inclusion c d p))
      ＝ index (Families.view L (Value.family c))
  index-included c d =
    ap (λ h → λ p → h (Families.Extension.left (first c d) p))
      (Families.Extension.right-β (joined c d))
    ∙ Families.Extension.left-β (first c d)

  member-inclusion :
    (c : Value) (d : D (sort c) → Value) (z : D (sort c))
    → interpret (pr₁ (Value.family (d z)))
    → carrier (Families.view L (Families.Extension.family (joined c d)))
  member-inclusion c d z p =
    Families.Extension.right (joined c d)
      (Families.Extension.right (first c d)
        (cast (pr₂ (gathered c d) ⁻¹) (z , p)))

  member-included :
    (c : Value) (d : D (sort c) → Value) (z : D (sort c))
    → (λ p →
        index (Families.view L (Families.Extension.family (joined c d)))
          (member-inclusion c d z p))
      ＝ index (Families.view L (Value.family (d z)))
  member-included c d z =
    ap (λ h → λ p →
          h (Families.Extension.right (first c d)
              (cast (pr₂ (gathered c d) ⁻¹) (z , p))))
      (Families.Extension.right-β (joined c d))
    ∙ ( ap (λ h → λ p → h (cast (pr₂ (gathered c d) ⁻¹) (z , p)))
          (Families.Extension.right-β (first c d))
      ∙ ap (λ h → λ p → h (z , p))
          (cancel (pr₂ (gathered c d))
            (λ w → interpret (pr₂ (Value.family (d (pr₁ w))) (pr₂ w)))))

  ----------------------------------------------------------------------
  -- Nodes and the closure

  module _
    (extensionality : (X : Set ℓ) → FunExt X (λ _ → C))
    where

    -- The index's request and each member's, carried into the joined
    -- family.
    carry-index :
      (c : Value) (d : D (sort c) → Value)
      → Request Q Φ
          (index (Families.view L (Families.Extension.family (joined c d))))
    carry-index c d =
      carry extensionality Q Φ
        (index (Families.view L (Families.Extension.family (joined c d))))
        (index-inclusion c d) (index-included c d) (Value.origin c)

    carried-index :
      (c : Value) (d : D (sort c) → Value)
      → requested Q Φ (carry-index c d) ＝ sort c
    carried-index c d =
      carried extensionality Q Φ
        (index (Families.view L (Families.Extension.family (joined c d))))
        (index-inclusion c d) (index-included c d) (Value.origin c)

    carry-member :
      (c : Value) (d : D (sort c) → Value)
      (y :
        index (Families.view L (Families.Extension.family (joined c d)))
          (Families.Extension.left (joined c d) (lift ⋆)))
      → Request Q Φ
          (index (Families.view L (Families.Extension.family (joined c d))))
    carry-member c d y =
      carry extensionality Q Φ
        (index (Families.view L (Families.Extension.family (joined c d))))
        (member-inclusion c d (cast (pointed c d) y))
        (member-included c d (cast (pointed c d) y))
        (Value.origin (d (cast (pointed c d) y)))

    carried-member :
      (c : Value) (d : D (sort c) → Value)
      (y :
        index (Families.view L (Families.Extension.family (joined c d)))
          (Families.Extension.left (joined c d) (lift ⋆)))
      → requested Q Φ (carry-member c d y) ＝ sort (d (cast (pointed c d) y))
    carried-member c d y =
      carried extensionality Q Φ
        (index (Families.view L (Families.Extension.family (joined c d))))
        (member-inclusion c d (cast (pointed c d) y))
        (member-included c d (cast (pointed c d) y))
        (Value.origin (d (cast (pointed c d) y)))

    branches :
      (c : Value) (d : D (sort c) → Value)
      → Lift ℓ 𝟙
        ⊎ index (Families.view L (Families.Extension.family (joined c d)))
            (Families.Extension.left (joined c d) (lift ⋆))
      → Stage
          (carrier (Families.view L (Families.Extension.family (joined c d))))
          (index (Families.view L (Families.Extension.family (joined c d))))
    branches c d (inl _) = Request.stage (carry-index c d)
    branches c d (inr y) = Request.stage (carry-member c d y)

    -- From the index's decoding into the node's branching type.
    towards :
      (c : Value) (d : D (sort c) → Value)
      → D (requested Q Φ (carry-index c d))
      → index (Families.view L (Families.Extension.family (joined c d)))
          (Families.Extension.left (joined c d) (lift ⋆))
    towards c d z =
      cast (pointed c d ⁻¹) (cast (ap D (carried-index c d)) z)

    node : Unary → Specification.Family (Specification.Decode D sort) → Node
    node t F = record
      { family = Families.Extension.family (joined (pr₁ F) (pr₂ F))
      ; stage =
          sup
            (applied t
              (Families.Extension.left (joined (pr₁ F) (pr₂ F)) (lift ⋆)))
            (branches (pr₁ F) (pr₂ F))
      ; tree =
          ( Request.tree (carry-index (pr₁ F) (pr₂ F))
          , Request.selection (carry-index (pr₁ F) (pr₂ F))) ,
          ( towards (pr₁ F) (pr₂ F)
          , (λ y →
              Request.tree (carry-member (pr₁ F) (pr₂ F) y) ,
              Request.selection (carry-member (pr₁ F) (pr₂ F) y)))
      }

    -- The family the node applies its tag to, and its identity with the
    -- given family.
    carried-family :
      (c : Value) (d : D (sort c) → Value) → Specification.Family D
    carried-family c d =
      requested Q Φ (carry-index c d) ,
      (λ z → requested Q Φ (carry-member c d (towards c d z)))

    node-β :
      (c : Value) (d : D (sort c) → Value)
      → carried-family c d ＝ Specification.map D sort (c , d)
    node-β c d =
      pair D extensionality (carried-index c d)
        (λ z →
          carried-member c d (towards c d z)
          ∙ ap (λ w → sort (d w))
              (recast (pointed c d) (cast (ap D (carried-index c d)) z)))

    closure : Specification.Closure Q Φ Value
    closure = record
      { interpret = sort
      ; empty = selecting (constant-node empty) (lift ⋆) , refl
      ; unit = selecting (constant-node unit) (lift ⋆) , refl
      ; two = selecting (constant-node two) (lift ⋆) , refl
      ; natural = selecting (constant-node natural) (lift ⋆) , refl
      ; product = λ F →
          selecting (node product F) (lift ⋆) ,
          ap (Specification.Formers.product Q) (node-β (pr₁ F) (pr₂ F))
      ; sum = λ F →
          selecting (node sum F) (lift ⋆) ,
          ap (Specification.Formers.sum Q) (node-β (pr₁ F) (pr₂ F))
      ; tree = λ F →
          selecting (node wellfounded F) (lift ⋆) ,
          ap (Specification.Formers.tree Q) (node-β (pr₁ F) (pr₂ F))
      ; identity = λ a p q →
          selecting (identity-node a p q) (lift ⋆) , refl
      ; inner = λ F →
          selecting (node operator F) (inl (lift ⋆)) ,
          (λ x → selecting (node operator F) (inr x))
      ; inner-β = λ F → ap Φ (node-β (pr₁ F) (pr₂ F))
      }

------------------------------------------------------------------------
-- The theorem

-- Each operator's reflection is the closure over the ambient reflection
-- of its requests, moved to the admitted name of its codes.

mahlo :
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Specification.Formers C D}
  → ((X : Set ℓ) → FunExt X (λ _ → C)) → Admission D
  → Specification.Mahlo (Ambient.formers ℓ) → Specification.Mahlo Q
mahlo {κ} {ℓ} {C} {D} {Q} extensionality admission reflections = record
  { reflect = λ Φ →
      let L =
            Specification.Reflection.closure
              (Specification.Mahlo.reflect reflections (requests Q Φ))
      in record
        { carrier = Admission.admit admission (Value Q Φ L)
        ; closure =
            transfer extensionality
              (Admission.out admission (Value Q Φ L))
              (Admission.into admission (Value Q Φ L))
              (Admission.out-into admission (Value Q Φ L))
              (closure Q Φ L extensionality)
        }
  }

-- The two-sorted family names every small type on the left.
sorted :
  {ℓ κ : Level} {O : Set κ}
  → ((X : Set ℓ) → FunExt X (λ _ → Sort ℓ O))
  → Specification.Mahlo (Ambient.formers ℓ)
  → Specification.Mahlo (Sorted.formers ℓ O)
sorted {ℓ} {κ} {O} extensionality =
  mahlo extensionality (naming (decode ℓ O) (λ X → inl X , refl))

-- Extensionality for families of types, from families of names.
types :
  {ℓ κ : Level} {O : Set κ}
  → ((X : Set ℓ) → FunExt X (λ _ → Sort ℓ O))
  → (X : Set ℓ) → FunExt X (λ _ → Set ℓ)
types {ℓ} {κ} {O} extensionality X f g h =
  ap (λ u → λ x → decode ℓ O (u x))
    (extensionality X (λ x → inl (f x)) (λ x → inl (g x))
      (λ x → ap inl (h x)))

-- With outputs in O alone.
outputs :
  {ℓ κ : Level} {O : Set κ}
  → ((X : Set ℓ) → FunExt X (λ _ → Sort ℓ O))
  → Specification.Mahlo (Ambient.formers ℓ)
  → (γ : Desc {s = ℓ} O) → Algebra ℓ γ
outputs extensionality reflections =
  Two-sorted.outputs (sorted extensionality reflections)

outputs-law :
  {ℓ κ : Level} {O : Set κ}
  (extensionality : (X : Set ℓ) → FunExt X (λ _ → Sort ℓ O))
  (reflections : Specification.Mahlo (Ambient.formers ℓ))
  (γ : Desc {s = ℓ} O) → Law (outputs extensionality reflections γ)
outputs-law extensionality reflections =
  Two-sorted.outputs-law (sorted extensionality reflections)

-- Smallness for outputs in types gives it for outputs in Sort ℓ O.
smallness :
  {ℓ κ : Level} {O : Set κ}
  → ((X : Set ℓ) → FunExt X (λ _ → Sort ℓ O))
  → Ambient-Smallness.Smallness ℓ → Smallness ℓ O
smallness extensionality small =
  Two-sorted.smallness
    (sorted extensionality (Types.mahlo (types extensionality) small))

------------------------------------------------------------------------
-- The converse

-- The types a family of names decodes to.
decoding :
  {κ ℓ : Level} {C : Set κ} (D : C → Set ℓ)
  → Specification.Family D → Specification.Family (λ (X : Set ℓ) → X)
decoding D F = D (pr₁ F) , (λ x → D (pr₂ F x))

-- An ambient operator, acting on the names of the types.
module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (n : (X : Set ℓ) → Specification.Name D X)
  where

  lifted : Ambient.Operator ℓ → Specification.Operator D
  lifted Ψ F =
    pr₁ (n (pr₁ (Ψ (decoding D F)))) ,
    (λ y →
      pr₁
        (n (pr₂ (Ψ (decoding D F))
          (cast (pr₂ (n (pr₁ (Ψ (decoding D F))))) y))))

  -- A closure under the lifted operator decodes to an ambient closure,
  -- along the decoding laws and the names' identities.
  module _
    (extensionality : (X : Set ℓ) → FunExt X (λ _ → Set ℓ))
    {Q : Specification.Formers C D} (laws : DecodingLaws Q)
    (Ψ : Ambient.Operator ℓ) {A : Set ℓ}
    (M : Specification.Closure Q (lifted Ψ) A)
    where

    open Specification.Closure M using (interpret)

    decoded-name :
      {c : C} {X : Set ℓ} → Specification.Name interpret c → D c ＝ X
      → Specification.Name (λ a → D (interpret a)) X
    decoded-name m e = pr₁ m , (ap D (pr₂ m) ∙ e)

    typed : Specification.Closure (Ambient.formers ℓ) Ψ A
    typed = record
      { interpret = λ a → D (interpret a)
      ; empty =
          decoded-name (Specification.Closure.empty M)
            (DecodingLaws.empty-β laws)
      ; unit =
          decoded-name (Specification.Closure.unit M)
            (DecodingLaws.unit-β laws)
      ; two =
          decoded-name (Specification.Closure.two M)
            (DecodingLaws.two-β laws)
      ; natural =
          decoded-name (Specification.Closure.natural M)
            (DecodingLaws.natural-β laws)
      ; product = λ F →
          decoded-name (Specification.Closure.product M F)
            (DecodingLaws.product-β laws (interpret (pr₁ F))
              (λ x → interpret (pr₂ F x)))
      ; sum = λ F →
          decoded-name (Specification.Closure.sum M F)
            (DecodingLaws.sum-β laws (interpret (pr₁ F))
              (λ x → interpret (pr₂ F x)))
      ; tree = λ F →
          decoded-name (Specification.Closure.tree M F)
            (DecodingLaws.tree-β laws (interpret (pr₁ F))
              (λ x → interpret (pr₂ F x)))
      ; identity = λ a x y →
          decoded-name (Specification.Closure.identity M a x y)
            (DecodingLaws.identity-β laws (interpret a) x y)
      ; inner = Specification.Closure.inner M
      ; inner-β = λ F →
          ap (decoding D) (Specification.Closure.inner-β M F)
          ∙ Types.pair extensionality
              (pr₂
                (n (pr₁ (Ψ (decoding D (Specification.map D interpret F))))))
              (λ y →
                pr₂
                  (n (pr₂ (Ψ (decoding D (Specification.map D interpret F)))
                    (cast
                      (pr₂
                        (n (pr₁
                          (Ψ (decoding D (Specification.map D interpret F))))))
                      y))))
      }

-- For a family naming every small type whose formers decode as the
-- ambient ones, its Mahlo rule gives the ambient rule: each ambient
-- operator acts on names, and its reflection decodes.
ambient :
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Specification.Formers C D}
  → ((X : Set ℓ) → FunExt X (λ _ → Set ℓ))
  → ((X : Set ℓ) → Specification.Name D X) → DecodingLaws Q
  → Specification.Mahlo Q → Specification.Mahlo (Ambient.formers ℓ)
ambient {κ} {ℓ} {C} {D} extensionality n laws reflections = record
  { reflect = λ Ψ → record
      { carrier =
          D (Specification.Reflection.carrier
              (Specification.Mahlo.reflect reflections (lifted n Ψ)))
      ; closure =
          typed n extensionality laws Ψ
            (Specification.Reflection.closure
              (Specification.Mahlo.reflect reflections (lifted n Ψ)))
      }
  }

-- The two-sorted family's formers decode as the ambient ones, by refl, so
-- its rule gives the ambient rule (the converse of `sorted`).
sorted-laws :
  {ℓ κ : Level} {O : Set κ} → DecodingLaws (Sorted.formers ℓ O)
sorted-laws = record
  { empty-β = refl
  ; unit-β = refl
  ; two-β = refl
  ; natural-β = refl
  ; product-β = λ a b → refl
  ; sum-β = λ a b → refl
  ; tree-β = λ a b → refl
  ; identity-β = λ a x y → refl
  }

unsorted :
  {ℓ κ : Level} {O : Set κ}
  → ((X : Set ℓ) → FunExt X (λ _ → Set ℓ))
  → Specification.Mahlo (Sorted.formers ℓ O)
  → Specification.Mahlo (Ambient.formers ℓ)
unsorted {ℓ} {κ} {O} extensionality =
  ambient extensionality (λ X → inl X , refl) sorted-laws
