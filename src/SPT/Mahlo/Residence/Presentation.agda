{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Residence.Presentation where

-- Small presentations of generated totals. A presentation of the generated
-- total of Q and Ψ is a small type with a map to the names, a witness that
-- each of its points names a generated member, and a point naming each
-- generated member (`Generated-Presentation`). Every closure names the
-- generated members (`name-in`), and the codes of a least closure are
-- generated members (`members`), so a small least closure is a presentation
-- (`least-presentation`). A presentation carries a closure
-- (`presented-closure`), and a named one a reflection. Hence absorption
-- gives named presentations (`absorption-presentations`), and named
-- presentations give Mahlo (`presented-mahlo`). Induction–recursion
-- presents the generated total for names at any level
-- (`inductive-presentation`); for the ambient family this is a weak
-- presentation of a raised type preserving names (`inductive-resizes`).
-- Function extensionality is taken for the maps into the names only. The
-- lemmas on names of formed codes are those of Residence.Names.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Impredicative.WeakResizing using (Weak-Presentation)
import SPT.Mahlo.Ambient as Ambient
open import SPT.Mahlo.Specification using
  (Family; Operator; Formers; Decode; Name; Closure; Reflection; Mahlo)
open import SPT.Mahlo.Residence.Absorption using
  (Methods; Induction; Small-Least; Absorbed; Absorption; absorbed-small)
open import SPT.Mahlo.Residence.Inductive using (inductive-small)
open import SPT.Mahlo.Residence.Membership using
  ( along; Form; emptyᶠ; unitᶠ; twoᶠ; naturalᶠ; productᶠ; sumᶠ; treeᶠ
  ; identityᶠ; resultᶠ; branchᶠ
  )
open import SPT.Mahlo.Residence.Names using
  ( branch-along; family-join; realized-family; former-name; result-name
  ; branch-name; identity-name
  )

------------------------------------------------------------------------
-- Presentations, and the members of a least closure

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Formers C D) (Ψ : Operator D)
  where

  -- Mathematical shape: a small type I, code : I → C, member : every
  -- point codes a generated member, realize : every generated member is
  -- coded by a point.
  record Generated-Presentation : Set (κ ⊔ lsuc ℓ) where
    field
      carrier : Set ℓ
      code : carrier → C
      member : (a : carrier) → Form Q Ψ (code a)
      realize :
          {c : C}
        → Form Q Ψ c
        → Σ carrier (λ a → code a ＝ c)

  Named : Generated-Presentation → Set (κ ⊔ lsuc ℓ)
  Named p = Σ C (λ c → D c ＝ Generated-Presentation.carrier p)

  -- The family of witnessed names of a family of codes.
  witnessed :
      {A : Set ℓ}
      (L : Closure Q Ψ A)
      (φ : Family (Decode D (Closure.interpret L)))
    → Form Q Ψ (Closure.interpret L (pr₁ φ))
    → ((x : Decode D (Closure.interpret L) (pr₁ φ))
      → Form Q Ψ (Closure.interpret L (pr₂ φ x)))
    → Family (λ (w : Σ C (Form Q Ψ)) → D (pr₁ w))
  witnessed L φ head branches =
    (Closure.interpret L (pr₁ φ) , head)
    , (λ x → Closure.interpret L (pr₂ φ x) , branches x)

  -- Each code of a least closure names a generated member: the closure's
  -- naming equations move the constructors' witnesses to its codes.
  member-methods :
      {A : Set ℓ}
      (L : Closure Q Ψ A)
    → Methods L (λ a → Form Q Ψ (Closure.interpret L a))
  member-methods L = record
    { on-empty = transport (Form Q Ψ) (pr₂ (Closure.empty L) ⁻¹) emptyᶠ
    ; on-unit = transport (Form Q Ψ) (pr₂ (Closure.unit L) ⁻¹) unitᶠ
    ; on-two = transport (Form Q Ψ) (pr₂ (Closure.two L) ⁻¹) twoᶠ
    ; on-natural =
        transport (Form Q Ψ) (pr₂ (Closure.natural L) ⁻¹) naturalᶠ
    ; on-product = λ φ head branches →
        transport (Form Q Ψ) (pr₂ (Closure.product L φ) ⁻¹)
          ( productᶠ (witnessed L φ head branches))
    ; on-sum = λ φ head branches →
        transport (Form Q Ψ) (pr₂ (Closure.sum L φ) ⁻¹)
          ( sumᶠ (witnessed L φ head branches))
    ; on-tree = λ φ head branches →
        transport (Form Q Ψ) (pr₂ (Closure.tree L φ) ⁻¹)
          ( treeᶠ (witnessed L φ head branches))
    ; on-identity = λ a x y head →
        transport (Form Q Ψ) (pr₂ (Closure.identity L a x y) ⁻¹)
          ( identityᶠ (Closure.interpret L a , head) x y)
    ; on-result = λ φ head branches →
        transport (Form Q Ψ) (ap pr₁ (Closure.inner-β L φ) ⁻¹)
          ( resultᶠ (witnessed L φ head branches))
    ; on-branch = λ φ y head branches →
        transport (Form Q Ψ) (branch-along D (Closure.inner-β L φ) y ⁻¹)
          ( branchᶠ (witnessed L φ head branches)
              ( transport D (ap pr₁ (Closure.inner-β L φ)) y))
    }

  members :
      {A : Set ℓ}
      (L : Closure Q Ψ A)
    → Induction L (κ ⊔ ℓ)
    → (a : A)
    → Form Q Ψ (Closure.interpret L a)
  members L ind =
    Induction.induction ind
      ( λ a → Form Q Ψ (Closure.interpret L a))
      ( member-methods L)

  -- A closure on the decoding of a name is a reflection.
  reflection-on :
      {X : Set ℓ}
      (c : C)
    → D c ＝ X
    → Closure Q Ψ X
    → Reflection Q Ψ
  reflection-on c refl L = record { carrier = c ; closure = L }

  -- The witnessed family of a family of presented codes.
  lifted :
      (p : Generated-Presentation)
    → Family (λ a → D (Generated-Presentation.code p a))
    → Family (λ (w : Σ C (Form Q Ψ)) → D (pr₁ w))
  lifted p F =
    ( Generated-Presentation.code p (pr₁ F)
    , Generated-Presentation.member p (pr₁ F))
    , (λ x →
        Generated-Presentation.code p (pr₂ F x)
        , Generated-Presentation.member p (pr₂ F x))

  -- The inner family of a presentation, from a point naming Ψ's result.
  inner-from :
      (p : Generated-Presentation)
      (F : Family (λ a → D (Generated-Presentation.code p a)))
    → Σ (Generated-Presentation.carrier p) (λ a →
        Generated-Presentation.code p a
        ＝ pr₁ (Ψ (along D (Generated-Presentation.code p) F)))
    → Family (λ a → D (Generated-Presentation.code p a))
  inner-from p F (r , e) =
    r
    , (λ y →
        pr₁
          ( Generated-Presentation.realize p
              ( branchᶠ (lifted p F) (transport D e y))))

------------------------------------------------------------------------
-- Names of generated members, and the closure of a presentation

-- A generated member is named in any closure, by recursion on its
-- witness: the closure's operations name the formed codes, and the
-- branches are joined by extensionality. A presentation's codes carry the
-- closure whose operations are its realizations.

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Formers C D) (Ψ : Operator D)
  (extensionality : (X : Set ℓ) → FunExt X (λ _ → C))
  where

  name-in :
      {A : Set ℓ}
      (L : Closure Q Ψ A)
      {c : C}
    → Form Q Ψ c
    → Name (Closure.interpret L) c
  name-in L emptyᶠ = Closure.empty L
  name-in L unitᶠ = Closure.unit L
  name-in L twoᶠ = Closure.two L
  name-in L naturalᶠ = Closure.natural L
  name-in L (productᶠ X) =
    former-name Q Ψ L (Formers.product Q) (Closure.product L)
      ( realized-family Q Ψ extensionality L (λ x → pr₁ (pr₂ X x))
          ( name-in L (pr₂ (pr₁ X)))
          ( λ x → name-in L (pr₂ (pr₂ X x))))
  name-in L (sumᶠ X) =
    former-name Q Ψ L (Formers.sum Q) (Closure.sum L)
      ( realized-family Q Ψ extensionality L (λ x → pr₁ (pr₂ X x))
          ( name-in L (pr₂ (pr₁ X)))
          ( λ x → name-in L (pr₂ (pr₂ X x))))
  name-in L (treeᶠ X) =
    former-name Q Ψ L (Formers.tree Q) (Closure.tree L)
      ( realized-family Q Ψ extensionality L (λ x → pr₁ (pr₂ X x))
          ( name-in L (pr₂ (pr₁ X)))
          ( λ x → name-in L (pr₂ (pr₂ X x))))
  name-in L (identityᶠ a x y) =
    identity-name Q Ψ L (name-in L (pr₂ a)) x y
  name-in L (resultᶠ X) =
    result-name Q Ψ L
      ( realized-family Q Ψ extensionality L (λ x → pr₁ (pr₂ X x))
          ( name-in L (pr₂ (pr₁ X)))
          ( λ x → name-in L (pr₂ (pr₂ X x))))
  name-in L (branchᶠ X y) =
    branch-name Q Ψ L
      ( realized-family Q Ψ extensionality L (λ x → pr₁ (pr₂ X x))
          ( name-in L (pr₂ (pr₁ X)))
          ( λ x → name-in L (pr₂ (pr₂ X x))))
      y

  least-presentation :
      Small-Least Q Ψ (κ ⊔ ℓ)
    → Generated-Presentation Q Ψ
  least-presentation small = record
    { carrier = Small-Least.carrier small
    ; code = Closure.interpret (Small-Least.closure small)
    ; member =
        members Q Ψ (Small-Least.closure small) (Small-Least.induction small)
    ; realize = name-in (Small-Least.closure small)
    }

  inner-from-β :
      (p : Generated-Presentation Q Ψ)
      (F : Family (λ a → D (Generated-Presentation.code p a)))
      (r : Σ (Generated-Presentation.carrier p) (λ a →
        Generated-Presentation.code p a
        ＝ pr₁ (Ψ (along D (Generated-Presentation.code p) F))))
    → along D (Generated-Presentation.code p) (inner-from Q Ψ p F r)
      ＝ Ψ (along D (Generated-Presentation.code p) F)
  inner-from-β p F r =
    family-join D (Generated-Presentation.code p) (pr₁ r) (pr₂ r)
      ( pr₂ (Ψ (along D (Generated-Presentation.code p) F)))
      ( λ y →
          Generated-Presentation.realize p (branchᶠ (lifted Q Ψ p F) y))
      ( extensionality
          ( D (pr₁ (Ψ (along D (Generated-Presentation.code p) F)))))

  presented-closure :
      (p : Generated-Presentation Q Ψ)
    → Closure Q Ψ (Generated-Presentation.carrier p)
  presented-closure p = record
    { interpret = Generated-Presentation.code p
    ; empty = Generated-Presentation.realize p emptyᶠ
    ; unit = Generated-Presentation.realize p unitᶠ
    ; two = Generated-Presentation.realize p twoᶠ
    ; natural = Generated-Presentation.realize p naturalᶠ
    ; product = λ F →
        Generated-Presentation.realize p (productᶠ (lifted Q Ψ p F))
    ; sum = λ F →
        Generated-Presentation.realize p (sumᶠ (lifted Q Ψ p F))
    ; tree = λ F →
        Generated-Presentation.realize p (treeᶠ (lifted Q Ψ p F))
    ; identity = λ a x y →
        Generated-Presentation.realize p
          ( identityᶠ
              ( Generated-Presentation.code p a
              , Generated-Presentation.member p a)
              x
              y)
    ; inner = λ F →
        inner-from Q Ψ p F
          ( Generated-Presentation.realize p (resultᶠ (lifted Q Ψ p F)))
    ; inner-β = λ F →
        inner-from-β p F
          ( Generated-Presentation.realize p (resultᶠ (lifted Q Ψ p F)))
    }

  presented-reflection :
      (p : Generated-Presentation Q Ψ)
    → Named Q Ψ p
    → Reflection Q Ψ
  presented-reflection p name =
    reflection-on Q Ψ (pr₁ name) (pr₂ name) (presented-closure p)

  absorbed-presentation :
      Absorbed Q Ψ (κ ⊔ ℓ)
    → Σ (Generated-Presentation Q Ψ) (Named Q Ψ)
  absorbed-presentation absorbed =
    least-presentation (absorbed-small absorbed)
    , Reflection.carrier (Absorbed.reflection absorbed) , refl

  -- Induction–recursion presents the generated total, for names at any
  -- level.
  inductive-presentation : Generated-Presentation Q Ψ
  inductive-presentation =
    least-presentation (inductive-small Q Ψ (κ ⊔ ℓ))

------------------------------------------------------------------------
-- Absorption, presentations and Mahlo

-- Mathematical shape:
--   Absorption ⇒ Π Ψ. a named presentation of Ψ's generated total ⇒ Mahlo.

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Formers C D)
  (extensionality : (X : Set ℓ) → FunExt X (λ _ → C))
  where

  absorption-presentations :
      Absorption Q (κ ⊔ ℓ)
    → (Ψ : Operator D)
    → Σ (Generated-Presentation Q Ψ) (Named Q Ψ)
  absorption-presentations absorption Ψ =
    absorbed-presentation Q Ψ extensionality (Absorption.absorb absorption Ψ)

  presented-mahlo :
      ((Ψ : Operator D) → Σ (Generated-Presentation Q Ψ) (Named Q Ψ))
    → Mahlo Q
  presented-mahlo presentations = record
    { reflect = λ Ψ →
        presented-reflection Q Ψ extensionality
          ( pr₁ (presentations Ψ))
          ( pr₂ (presentations Ψ))
    }

------------------------------------------------------------------------
-- The ambient family

-- The generated total of an operator on the types of level ℓ lies one
-- level up. The induction–recursive codes present it: a weak
-- presentation of a raised type, whose maps preserve the names.

module _
  {ℓ : Level}
  (extensionality : (X : Set ℓ) → FunExt X (λ _ → Set ℓ))
  (Ψ : Operator (λ (X : Set ℓ) → X))
  where

  inductive-resizes :
    Weak-Presentation ℓ (Σ (Set ℓ) (Form (Ambient.formers ℓ) Ψ))
  inductive-resizes =
    Generated-Presentation.carrier
      ( inductive-presentation (Ambient.formers ℓ) Ψ extensionality)
    , ( λ a →
          Generated-Presentation.code
            ( inductive-presentation (Ambient.formers ℓ) Ψ extensionality)
            a
          , Generated-Presentation.member
              ( inductive-presentation (Ambient.formers ℓ) Ψ extensionality)
              a)
    , ( λ w →
          pr₁
            ( Generated-Presentation.realize
                ( inductive-presentation (Ambient.formers ℓ) Ψ extensionality)
                ( pr₂ w)))

  -- Returning from the small code keeps the name.
  inductive-resizes-names :
      (w : Σ (Set ℓ) (Form (Ambient.formers ℓ) Ψ))
    → pr₁
        ( pr₁ (pr₂ inductive-resizes)
            ( pr₂ (pr₂ inductive-resizes) w))
      ＝ pr₁ w
  inductive-resizes-names w =
    pr₂
      ( Generated-Presentation.realize
          ( inductive-presentation (Ambient.formers ℓ) Ψ extensionality)
          ( pr₂ w))
