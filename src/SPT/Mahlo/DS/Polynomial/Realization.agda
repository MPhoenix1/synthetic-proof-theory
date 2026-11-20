{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Polynomial.Realization where

-- Small algebras of indexed polynomial rules from closures of the ambient
-- family. The frontier operator of rules r returns, at a family of types,
-- the requests of every rule, a path or a complete argument, each with the
-- type it asks to be named (`constant`, `Request`, `requested`,
-- `operator`). Let L be any closure of the ambient family under it. A
-- family of codes of L is one indexed family (`view`), and the operator's
-- returned family names its requests (`ready`, `action`). Every argument
-- over the whole carrier is covered by an argument over one family of codes
-- with the same information (`Cover`, `cover`): a sum joins the covers of
-- its parts (`union`, `from-left`, `from-right`, `agreement`, `second`,
-- `joined`), and a product gathers the covers of its components over its
-- named arity (`gather`, `inclusion`, `gathered`). So L is a small algebra
-- of r (`operation`, `operation-β`, `algebra`), and a Mahlo reflection
-- gives one for every r (`reflected`). Extensionality is used for the
-- information functions of products.

open import SPT.Base
import SPT.Mahlo.Ambient as Ambient
import SPT.Mahlo.Specification as Specification

open import SPT.IR.Polynomial using
  (Poly; var; con; sigma; pi; Family; carrier; readout; Args; info;
   shape; output; Rules; scheme; Extensionality)
import SPT.IR.Polynomial.Action as Action
open import SPT.IR.Polynomial.Algebra using (Algebra)
import SPT.IR.Polynomial.Frontier as Frontier
import SPT.Mahlo.DS.Realization.Family as Families
open import SPT.Mahlo.DS.Realization.Family using (cast; cancel)

------------------------------------------------------------------------
-- The frontier operator

-- A family of types (A , B) is the indexed family with carrier A at every
-- index, read out by B.

constant :
  {ℓ : Level} (r : Rules ℓ) → Σ (Set ℓ) (λ A → A → Set ℓ)
  → Family ℓ (lsuc ℓ) (λ (_ : Rules.Index r) → Set ℓ)
constant r F = record
  { carrier = λ _ → pr₁ F
  ; readout = λ _ x → pr₂ F x
  }

Request :
  {ℓ : Level} (r : Rules ℓ)
  → Family ℓ (lsuc ℓ) (λ (_ : Rules.Index r) → Set ℓ) → Set ℓ
Request r Z =
  Σ (Rules.Index r)
    (λ i →
      Frontier.Path (shape (Rules.rule r i)) Z
      ⊎ Args (shape (Rules.rule r i)) Z)

requested :
  {ℓ : Level} (r : Rules ℓ)
  (Z : Family ℓ (lsuc ℓ) (λ (_ : Rules.Index r) → Set ℓ))
  → Request r Z → Set ℓ
requested r Z (i , inl z) = Frontier.requested (shape (Rules.rule r i)) Z z
requested r Z (i , inr a) =
  output (Rules.rule r i) (info (shape (Rules.rule r i)) Z a)

operator : {ℓ : Level} → Rules ℓ → Ambient.Operator ℓ
operator r F = Request r (constant r F) , requested r (constant r F)

------------------------------------------------------------------------
-- Families of codes and their names

module _
  {ℓ : Level} (r : Rules ℓ) {K : Set ℓ}
  (L : Specification.Closure (Ambient.formers ℓ) (operator r) K)
  where

  open Specification.Closure L using (interpret)

  -- A family of codes, as the indexed family of its decodings; and the
  -- whole carrier.

  view :
    Specification.Family (Specification.Decode (λ X → X) interpret)
    → Family ℓ (lsuc ℓ) (λ (_ : Rules.Index r) → Set ℓ)
  view F = constant r (Specification.map (λ X → X) interpret F)

  whole : Family ℓ (lsuc ℓ) (λ (_ : Rules.Index r) → Set ℓ)
  whole = record
    { carrier = λ _ → K
    ; readout = λ _ → interpret
    }

  -- Every path of p over every family of codes requests a named type.
  Ready :
    {X : Set (lsuc ℓ)}
    → Poly ℓ (lsuc ℓ) (λ (_ : Rules.Index r) → Set ℓ) X → Set (lsuc ℓ)
  Ready p =
    (F : Specification.Family (Specification.Decode (λ X → X) interpret))
    (z : Frontier.Path p (view F))
    → Specification.Name interpret (Frontier.requested p (view F) z)

  ready : (i : Rules.Index r) → Ready (shape (Rules.rule r i))
  ready i F z = Families.action L F (i , inl z)

  action :
    (i : Rules.Index r)
    (F : Specification.Family (Specification.Decode (λ X → X) interpret))
    (u : Args (shape (Rules.rule r i)) (view F))
    → Specification.Name interpret
        (output (Rules.rule r i) (info (shape (Rules.rule r i)) (view F) u))
  action i F u = Families.action L F (i , inr u)

------------------------------------------------------------------------
-- Unions and gathered families

  -- The union of two families of codes adjoins the members of E, along
  -- E's own code, to C (Families.extend); its two inclusions keep the
  -- decodings.

  union :
    (C E :
      Specification.Family (Specification.Decode (λ X → X) interpret))
    → Specification.Family (Specification.Decode (λ X → X) interpret)
  union C E =
    Families.Extension.family (Families.extend L (pr₁ E) refl (pr₂ E) C)

  from-left :
    (C E :
      Specification.Family (Specification.Decode (λ X → X) interpret))
    → Action.Map (view C) (view (union C E))
  from-left C E = record
    { function = λ _ →
        Families.Extension.right (Families.extend L (pr₁ E) refl (pr₂ E) C)
    ; preserve = λ _ x →
        ap (λ h → h x)
          ( Families.Extension.right-β
              (Families.extend L (pr₁ E) refl (pr₂ E) C)
          ⁻¹)
    }

  from-right :
    (C E :
      Specification.Family (Specification.Decode (λ X → X) interpret))
    → Action.Map (view E) (view (union C E))
  from-right C E = record
    { function = λ _ →
        Families.Extension.left (Families.extend L (pr₁ E) refl (pr₂ E) C)
    ; preserve = λ _ x →
        ap (λ h → h x)
          ( Families.Extension.left-β
              (Families.extend L (pr₁ E) refl (pr₂ E) C)
          ⁻¹)
    }

  -- Families of codes over a named arity, gathered by the closure's sum
  -- into one family containing each of them.

  gather :
    {A : Set ℓ} → Specification.Name interpret A
    → (A → Specification.Family (Specification.Decode (λ X → X) interpret))
    → Specification.Family (Specification.Decode (λ X → X) interpret)
  gather {A} n F =
    let named = Families.sum L A n (λ x → pr₁ (F x))
    in
    pr₁ named ,
    (λ y → pr₂ (F (pr₁ (cast (pr₂ named) y))) (pr₂ (cast (pr₂ named) y)))

  inclusion :
    {A : Set ℓ} (n : Specification.Name interpret A)
    (F : A → Specification.Family (Specification.Decode (λ X → X) interpret))
    (x : A) → Action.Map (view (F x)) (view (gather n F))
  inclusion {A} n F x =
    let named = Families.sum L A n (λ y → pr₁ (F y))
    in record
      { function = λ _ w → cast (pr₂ named ⁻¹) (x , w)
      ; preserve = λ _ w →
          ap (λ h → h (x , w))
            ( cancel (pr₂ named)
                (λ v → interpret (pr₂ (F (pr₁ v)) (pr₂ v)))
            ⁻¹)
      }

------------------------------------------------------------------------
-- Covers

  -- A cover of an argument over the whole carrier: one family of codes
  -- and an argument over it with the same information.

  record Cover {X : Set (lsuc ℓ)}
    (p : Poly ℓ (lsuc ℓ) (λ (_ : Rules.Index r) → Set ℓ) X)
    (a : Args p whole) : Set (lsuc ℓ) where
    field
      family :
        Specification.Family (Specification.Decode (λ X → X) interpret)
      argument : Args p (view family)
      information : info p (view family) argument ＝ info p whole a

  first :
    {X : Set (lsuc ℓ)} {Y : X → Set (lsuc ℓ)}
    (p : Poly ℓ (lsuc ℓ) (λ (_ : Rules.Index r) → Set ℓ) X)
    (q : (x : X) → Poly ℓ (lsuc ℓ) (λ (_ : Rules.Index r) → Set ℓ) (Y x))
    → Ready (sigma p q) → Ready p
  first p q h F z = h F (inl z)

  component :
    (A : Set ℓ) {Y : A → Set (lsuc ℓ)}
    (p : (a : A) → Poly ℓ (lsuc ℓ) (λ (_ : Rules.Index r) → Set ℓ) (Y a))
    → Ready (pi A p) → (x : A) → Ready (p x)
  component A p h x F z = h F (inr (x , z))

  -- The first part of a cover, moved into a union, keeps its information.
  agreement :
    (extensionality : Extensionality ℓ (lsuc ℓ)) {X : Set (lsuc ℓ)}
    (p : Poly ℓ (lsuc ℓ) (λ (_ : Rules.Index r) → Set ℓ) X)
    (a : Args p whole) (c : Cover p a)
    (E : Specification.Family (Specification.Decode (λ X → X) interpret))
    → info p (view (union (Cover.family c) E))
        (Action.map extensionality (from-left (Cover.family c) E) p
          (Cover.argument c))
      ＝ info p whole a
  agreement extensionality p a c E =
    Action.map-info extensionality (from-left (Cover.family c) E) p
      (Cover.argument c)
    ∙ Cover.information c

  -- A path of a sum's continuation, at the information of a covered first
  -- argument, is a path of the sum through the union of the cover and the
  -- path's own family.

  second :
    Extensionality ℓ (lsuc ℓ) → {X : Set (lsuc ℓ)} {Y : X → Set (lsuc ℓ)}
    (p : Poly ℓ (lsuc ℓ) (λ (_ : Rules.Index r) → Set ℓ) X)
    (q : (x : X) → Poly ℓ (lsuc ℓ) (λ (_ : Rules.Index r) → Set ℓ) (Y x))
    → Ready (sigma p q) → (a : Args p whole) → Cover p a
    → Ready (q (info p whole a))
  second extensionality p q h a c F z =
    let named =
          h (union (Cover.family c) F)
            ( inr
                ( Action.map extensionality (from-left (Cover.family c) F) p
                    (Cover.argument c)
                , Frontier.shift q (view (union (Cover.family c) F))
                    (agreement extensionality p a c F ⁻¹)
                    (Frontier.map extensionality (q (info p whole a))
                      (from-right (Cover.family c) F) z)))
    in
    pr₁ named ,
    ( pr₂ named
    ∙ ( Frontier.requested-shift q (view (union (Cover.family c) F))
          (agreement extensionality p a c F ⁻¹)
          (Frontier.map extensionality (q (info p whole a))
            (from-right (Cover.family c) F) z)
      ∙ Frontier.requested-map extensionality (q (info p whole a))
          (from-right (Cover.family c) F) z))

  -- The covers of a sum's two parts cover the sum through the union of
  -- their families; the second part is moved along the first agreement.

  joined :
    Extensionality ℓ (lsuc ℓ) → {X : Set (lsuc ℓ)} {Y : X → Set (lsuc ℓ)}
    (p : Poly ℓ (lsuc ℓ) (λ (_ : Rules.Index r) → Set ℓ) X)
    (q : (x : X) → Poly ℓ (lsuc ℓ) (λ (_ : Rules.Index r) → Set ℓ) (Y x))
    (a : Args p whole) (b : Args (q (info p whole a)) whole)
    (c : Cover p a) (d : Cover (q (info p whole a)) b)
    → Cover (sigma p q) (a , b)
  joined extensionality {Y = Y} p q a b c d = record
    { family = union (Cover.family c) (Cover.family d)
    ; argument =
        Action.map extensionality
          (from-left (Cover.family c) (Cover.family d)) p
          (Cover.argument c) ,
        transport
          (λ x → Args (q x) (view (union (Cover.family c) (Cover.family d))))
          (agreement extensionality p a c (Cover.family d) ⁻¹)
          (Action.map extensionality
            (from-right (Cover.family c) (Cover.family d))
            (q (info p whole a)) (Cover.argument d))
    ; information =
        Action.pair-info
          (λ x → Args (q x) (view (union (Cover.family c) (Cover.family d))))
          Y
          (λ x → info (q x) (view (union (Cover.family c) (Cover.family d))))
          (agreement extensionality p a c (Cover.family d) ⁻¹)
          (Action.map extensionality
            (from-right (Cover.family c) (Cover.family d))
            (q (info p whole a)) (Cover.argument d))
        ∙ ap (λ y → (info p whole a , y))
            ( Action.map-info extensionality
                (from-right (Cover.family c) (Cover.family d))
                (q (info p whole a)) (Cover.argument d)
            ∙ Cover.information d)
    }

  -- The covers of a product's components cover the product through the
  -- families gathered over its named arity.

  gathered :
    Extensionality ℓ (lsuc ℓ) → (A : Set ℓ) {Y : A → Set (lsuc ℓ)}
    (p : (a : A) → Poly ℓ (lsuc ℓ) (λ (_ : Rules.Index r) → Set ℓ) (Y a))
    (f : (a : A) → Args (p a) whole)
    (n : Specification.Name interpret A) (c : (x : A) → Cover (p x) (f x))
    → Cover (pi A p) f
  gathered extensionality A {Y} p f n c = record
    { family = gather n (λ x → Cover.family (c x))
    ; argument = λ x →
        Action.map extensionality
          (inclusion n (λ y → Cover.family (c y)) x) (p x)
          (Cover.argument (c x))
    ; information =
        extensionality A Y
          (λ x →
            info (p x) (view (gather n (λ y → Cover.family (c y))))
              (Action.map extensionality
                (inclusion n (λ y → Cover.family (c y)) x) (p x)
                (Cover.argument (c x))))
          (λ x → info (p x) whole (f x))
          (λ x →
            Action.map-info extensionality
              (inclusion n (λ y → Cover.family (c y)) x) (p x)
              (Cover.argument (c x))
            ∙ Cover.information (c x))
    }

  cover :
    Extensionality ℓ (lsuc ℓ) → {X : Set (lsuc ℓ)}
    (p : Poly ℓ (lsuc ℓ) (λ (_ : Rules.Index r) → Set ℓ) X)
    → Ready p → (a : Args p whole) → Cover p a
  cover extensionality (var i) h a = record
    { family = pr₁ (Specification.Closure.unit L) , (λ _ → a)
    ; argument = cast (pr₂ (Specification.Closure.unit L) ⁻¹) (lift ⋆)
    ; information = refl
    }
  cover extensionality (con A) h a = record
    { family = Families.unit L
    ; argument = a
    ; information = refl
    }
  cover extensionality (sigma p q) h (a , b) =
    let c = cover extensionality p (first p q h) a
    in
    joined extensionality p q a b c
      ( cover extensionality (q (info p whole a))
          (second extensionality p q h a c) b)
  cover extensionality (pi A p) h f =
    gathered extensionality A p f (h (Families.unit L) (inl (lift ⋆)))
      (λ x → cover extensionality (p x) (component A p h x) (f x))

------------------------------------------------------------------------
-- The small algebra

  -- An argument over the whole carrier is sent to the name of its output,
  -- through its cover.

  operation :
    Extensionality ℓ (lsuc ℓ) → (i : Rules.Index r)
    → Args (shape (Rules.rule r i)) whole → K
  operation extensionality i a =
    let c = cover extensionality (shape (Rules.rule r i)) (ready i) a
    in pr₁ (action i (Cover.family c) (Cover.argument c))

  operation-β :
    (extensionality : Extensionality ℓ (lsuc ℓ)) (i : Rules.Index r)
    (a : Args (shape (Rules.rule r i)) whole)
    → interpret (operation extensionality i a)
      ＝ output (Rules.rule r i) (info (shape (Rules.rule r i)) whole a)
  operation-β extensionality i a =
    let c = cover extensionality (shape (Rules.rule r i)) (ready i) a
    in
    pr₂ (action i (Cover.family c) (Cover.argument c))
    ∙ ap (output (Rules.rule r i)) (Cover.information c)

  algebra : Extensionality ℓ (lsuc ℓ) → Algebra (scheme r)
  algebra extensionality = record
    { family = whole
    ; operation = operation extensionality
    ; law = operation-β extensionality
    }

------------------------------------------------------------------------
-- From a Mahlo reflection

reflected :
  {ℓ : Level} → Extensionality ℓ (lsuc ℓ)
  → Specification.Mahlo (Ambient.formers ℓ) → (r : Rules ℓ)
  → Algebra (scheme r)
reflected extensionality reflections r =
  algebra r
    ( Specification.Reflection.closure
        (Specification.Mahlo.reflect reflections (operator r)))
    extensionality
