{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Stationary.Derivable where

-- No reflection names its own carrier from below. A closure names every
-- name derivable, by the formers and its operator, from names it already
-- names (Cedents.least at Cedents.named-closed), so a carrier code
-- derivable from them would be named by the closure itself, and the
-- closure's code type would be the decoding of one of its own codes: the
-- tree paradox (Residence.Unreflected.no-retract; `carrier-unnamed`). Hence
-- `not-derivable-from`, and `not-derivable` with no seeds. Operators
-- indexed by the points of a code combine into one through the formers
-- (`combined`): names closed under each are closed under the combination
-- (`combined-closed`), whose derivable names are closed under each
-- (`combined-derivable`). So no carrier is derivable by several operators
-- together either (`not-derivable-together`). The operator must be the
-- closure's own: the constant operator at a code derives the code
-- (`constant-derivable`), and no reflection of it has that code as carrier
-- (`constant-unreflected`). A universe naming only derivable names is not
-- of degree one (`derivable-not-mahlo`), and the reflector Naming builds
-- through an admission has no degree one (`naming-degree-zero`). That
-- admission needs codes above their decodings: a family with small codes
-- does not admit every small type (`admission-not-small`). For parents
-- whose formers decode up to retraction.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
import SPT.Mahlo.Ambient as Ambient
open import SPT.Mahlo.Decoding using (child-formers)
open import SPT.Mahlo.Retraction using
  (Retract; Retracts; inherited-retracts)
import SPT.Mahlo.Specification as Specification
open import SPT.Mahlo.Residence.Unreflected using (no-retract)
open import SPT.Mahlo.DS.Cedents using
  ( Ced; Closed; Derivable; ∅ᶜ; _⊆_; derivable-closed; least
  ; named-closed; result; unit; branch)
import SPT.Mahlo.DS.Naming as Naming
import SPT.Mahlo.DS.Naming.Cedents as Named
import SPT.Mahlo.DS.Naming.Trees as Trees
import SPT.Mahlo.DS.Stationary as Stationarity

------------------------------------------------------------------------
-- No reflection names its carrier from below

-- A closure L of Ψ does not name the carrier: a code x naming it would
-- make L's code type the decoding of x, along that naming identity, a
-- retraction of the child's codes onto one of their decodings, which
-- no-retract refutes with the retractions L inherits. The names of L form
-- a closed cedent, so L names every name derivable from seeds it names,
-- and the carrier is not derivable from them. With no seeds this is
-- `not-derivable`.

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} (Q : Specification.Formers C D)
  where

  carrier-unnamed :
    Retracts Q
    → (Ψ : Specification.Operator D)
      (r : Specification.Reflection Q Ψ)
    → ¬ Specification.Name
        (Specification.Closure.interpret (Specification.Reflection.closure r))
        (Specification.Reflection.carrier r)
  carrier-unnamed retracts Ψ r n =
    let K = Specification.Reflection.closure r
        e = pr₂ n
    in no-retract (child-formers K) (inherited-retracts retracts K) (pr₁ n)
         ( transport D e) (transport D (e ⁻¹))
         ( back-and-forth-transport D e)

  not-derivable-from :
    {ν : Level}
    → Retracts Q
    → ((X : Set ℓ) → FunExt X (λ _ → C))
    → (Ψ : Specification.Operator D)
      (r : Specification.Reflection Q Ψ)
      (Γ : Ced ν C)
    → Γ ⊆ Specification.Name
        (Specification.Closure.interpret (Specification.Reflection.closure r))
    → ¬ Derivable Q Ψ Γ (Specification.Reflection.carrier r)
  not-derivable-from retracts extensionality Ψ r Γ named d =
    carrier-unnamed retracts Ψ r
      ( least {Γ = Γ} named
          ( named-closed extensionality (Specification.Reflection.closure r))
          d)

  not-derivable :
    Retracts Q
    → ((X : Set ℓ) → FunExt X (λ _ → C))
    → (Ψ : Specification.Operator D)
      (r : Specification.Reflection Q Ψ)
    → ¬ Derivable Q Ψ ∅ᶜ (Specification.Reflection.carrier r)
  not-derivable retracts extensionality Ψ r =
    not-derivable-from retracts extensionality Ψ r ∅ᶜ (λ p → 𝟘-elim p)

------------------------------------------------------------------------
-- Several operators, combined through the formers

-- Operators Φ x indexed by the points x of a code i combine into one
-- (`combined`). At a family F its index is the sum over i of the codes
-- `whole (Φ x F)`, and `whole G` decodes, up to the retractions, to one
-- point for G's index and the points of that index for G's members
-- (`member`). Names closed under the formers and every Φ x, with i among
-- them, are closed under the combined operator (`combined-closed`); by the
-- retraction laws the names it derives are closed under every Φ x
-- (`combined-derivable`). So the combined operator derives what the
-- formers and the Φ x derive together, with i as a seed, and no
-- reflection's carrier is derivable so from seeds its closure names when
-- its names include i and are closed under every Φ x
-- (`not-derivable-together`).

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Specification.Formers C D) (retracts : Retracts Q)
  where

  -- A code chosen by a point of the decoded two-element type.
  pick : D (Specification.Formers.two Q) → C → C → C
  pick s c c′ = 𝟚-cases c′ c (Retract.out (Retracts.two retracts) s)

  -- A point for a family's index, then the points of that index.
  whole : Specification.Family D → C
  whole G =
    Specification.Formers.sum Q
      ( Specification.Formers.two Q
      , (λ s → pick s (Specification.Formers.unit Q) (pr₁ G)))

  -- The decoding of whole G, up to retraction.
  spread :
    (G : Specification.Family D)
    → Retract (D (whole G))
        (Σ (D (Specification.Formers.two Q))
          (λ s → D (pick s (Specification.Formers.unit Q) (pr₁ G))))
  spread G =
    Retracts.sum retracts (Specification.Formers.two Q)
      (λ s → pick s (Specification.Formers.unit Q) (pr₁ G))

  choose :
    (G : Specification.Family D) (t : 𝟚)
    → D (𝟚-cases (pr₁ G) (Specification.Formers.unit Q) t) → C
  choose G ₁ v = pr₁ G
  choose G ₀ v = pr₂ G v

  -- The code at a point of whole G: G's index, or one of its members.
  member : (G : Specification.Family D) → D (whole G) → C
  member G w =
    let p = Retract.out (spread G) w
    in choose G (Retract.out (Retracts.two retracts) (pr₁ p)) (pr₂ p)

  -- The decoding of the combined index, up to retraction.
  parts :
    (i : C) (Φ : D i → Specification.Operator D)
    (F : Specification.Family D)
    → Retract (D (Specification.Formers.sum Q (i , (λ x → whole (Φ x F)))))
        (Σ (D i) (λ x → D (whole (Φ x F))))
  parts i Φ F = Retracts.sum retracts i (λ x → whole (Φ x F))

  -- The operators Φ x, for the points x of i, as one operator.
  combined :
    (i : C) → (D i → Specification.Operator D) → Specification.Operator D
  combined i Φ F =
    ( Specification.Formers.sum Q (i , (λ x → whole (Φ x F)))
    , (λ y →
         let p = Retract.out (parts i Φ F) y
         in member (Φ (pr₁ p) F) (pr₂ p)))

  -- The decoded points of whole G for its index and for its members.
  index-pair :
    (G : Specification.Family D)
    → Σ (D (Specification.Formers.two Q))
        (λ s → D (pick s (Specification.Formers.unit Q) (pr₁ G)))
  index-pair G =
    ( Retract.into (Retracts.two retracts) ₁
    , transport
        (λ t → D (𝟚-cases (pr₁ G) (Specification.Formers.unit Q) t))
        (Retract.out-into (Retracts.two retracts) ₁ ⁻¹)
        (Retracts.point retracts))

  member-pair :
    (G : Specification.Family D) → D (pr₁ G)
    → Σ (D (Specification.Formers.two Q))
        (λ s → D (pick s (Specification.Formers.unit Q) (pr₁ G)))
  member-pair G z =
    ( Retract.into (Retracts.two retracts) ₀
    , transport
        (λ t → D (𝟚-cases (pr₁ G) (Specification.Formers.unit Q) t))
        (Retract.out-into (Retracts.two retracts) ₀ ⁻¹)
        z)

  index-point : (G : Specification.Family D) → D (whole G)
  index-point G = Retract.into (spread G) (index-pair G)

  member-point : (G : Specification.Family D) → D (pr₁ G) → D (whole G)
  member-point G z = Retract.into (spread G) (member-pair G z)

  choose-index :
    (G : Specification.Family D) (t : 𝟚) (e : t ＝ ₁)
    (v : D (Specification.Formers.unit Q))
    → choose G t
        (transport
          (λ t′ → D (𝟚-cases (pr₁ G) (Specification.Formers.unit Q) t′))
          (e ⁻¹) v)
      ＝ pr₁ G
  choose-index G t refl v = refl

  choose-member :
    (G : Specification.Family D) (t : 𝟚) (e : t ＝ ₀) (z : D (pr₁ G))
    → choose G t
        (transport
          (λ t′ → D (𝟚-cases (pr₁ G) (Specification.Formers.unit Q) t′))
          (e ⁻¹) z)
      ＝ pr₂ G z
  choose-member G t refl z = refl

  index-point-β :
    (G : Specification.Family D) → member G (index-point G) ＝ pr₁ G
  index-point-β G =
    ap
      (λ p →
        choose G (Retract.out (Retracts.two retracts) (pr₁ p)) (pr₂ p))
      (Retract.out-into (spread G) (index-pair G))
    ∙ choose-index G
        (Retract.out (Retracts.two retracts)
          (Retract.into (Retracts.two retracts) ₁))
        (Retract.out-into (Retracts.two retracts) ₁)
        (Retracts.point retracts)

  member-point-β :
    (G : Specification.Family D) (z : D (pr₁ G))
    → member G (member-point G z) ＝ pr₂ G z
  member-point-β G z =
    ap
      (λ p →
        choose G (Retract.out (Retracts.two retracts) (pr₁ p)) (pr₂ p))
      (Retract.out-into (spread G) (member-pair G z))
    ∙ choose-member G
        (Retract.out (Retracts.two retracts)
          (Retract.into (Retracts.two retracts) ₀))
        (Retract.out-into (Retracts.two retracts) ₀)
        z

  -- The point of the combined index at the x-th operator.
  component :
    (i : C) (Φ : D i → Specification.Operator D)
    (F : Specification.Family D)
    (x : D i) → D (whole (Φ x F)) → D (pr₁ (combined i Φ F))
  component i Φ F x w = Retract.into (parts i Φ F) (x , w)

  component-β :
    (i : C) (Φ : D i → Specification.Operator D)
    (F : Specification.Family D)
    (x : D i) (w : D (whole (Φ x F)))
    → pr₂ (combined i Φ F) (component i Φ F x w) ＝ member (Φ x F) w
  component-β i Φ F x w =
    ap (λ p → member (Φ (pr₁ p) F) (pr₂ p))
      (Retract.out-into (parts i Φ F) (x , w))

  module _ {μ : Level} {Δ : Ced μ C} where

    picked :
      (t : 𝟚) {c c′ : C} → Δ c → Δ c′ → Δ (𝟚-cases c′ c t)
    picked ₁ n n′ = n
    picked ₀ n n′ = n′

    chosen :
      (G : Specification.Family D) → Δ (pr₁ G)
      → ((z : D (pr₁ G)) → Δ (pr₂ G z))
      → (t : 𝟚)
        (v : D (𝟚-cases (pr₁ G) (Specification.Formers.unit Q) t))
      → Δ (choose G t v)
    chosen G n m ₁ v = n
    chosen G n m ₀ v = m v

    whole-closed :
      {Φ₀ : Specification.Operator D}
      → Closed Q Φ₀ Δ
      → (G : Specification.Family D) → Δ (pr₁ G) → Δ (whole G)
    whole-closed base G n =
      Closed.on-sum base (Specification.Formers.two Q)
        (λ s → pick s (Specification.Formers.unit Q) (pr₁ G))
        (Closed.on-two base)
        (λ s →
          picked (Retract.out (Retracts.two retracts) s)
            (Closed.on-unit base) n)

    member-closed :
      (G : Specification.Family D) → Δ (pr₁ G)
      → ((z : D (pr₁ G)) → Δ (pr₂ G z))
      → (w : D (whole G)) → Δ (member G w)
    member-closed G n m w =
      let p = Retract.out (spread G) w
      in chosen G n m (Retract.out (Retracts.two retracts) (pr₁ p)) (pr₂ p)

    -- Names closed under the formers and every Φ x, with i among them.
    combined-closed :
      {Φ₀ : Specification.Operator D}
      → Closed Q Φ₀ Δ
      → (i : C) (Φ : D i → Specification.Operator D) → Δ i
      → ((x : D i) → Closed Q (Φ x) Δ)
      → Closed Q (combined i Φ) Δ
    combined-closed base i Φ index closed = record
      { on-empty = Closed.on-empty base
      ; on-unit = Closed.on-unit base
      ; on-two = Closed.on-two base
      ; on-natural = Closed.on-natural base
      ; on-product = Closed.on-product base
      ; on-sum = Closed.on-sum base
      ; on-tree = Closed.on-tree base
      ; on-identity = Closed.on-identity base
      ; on-result = λ a b n m →
          Closed.on-sum base i (λ x → whole (Φ x (a , b))) index
            (λ x →
              whole-closed base (Φ x (a , b))
                (Closed.on-result (closed x) a b n m))
      ; on-branch = λ a b n m y →
          let p = Retract.out (parts i Φ (a , b)) y
          in member-closed (Φ (pr₁ p) (a , b))
               (Closed.on-result (closed (pr₁ p)) a b n m)
               (Closed.on-branch (closed (pr₁ p)) a b n m)
               (pr₂ p)
      }

  -- The names the combined operator derives are closed under each Φ x.
  combined-derivable :
    {ν : Level} (Γ : Ced ν C) (i : C) (Φ : D i → Specification.Operator D)
    (x : D i)
    → Closed Q (Φ x) (Derivable Q (combined i Φ) Γ)
  combined-derivable Γ i Φ x =
    let derived = derivable-closed Q (combined i Φ) Γ
    in record
      { on-empty = Closed.on-empty derived
      ; on-unit = Closed.on-unit derived
      ; on-two = Closed.on-two derived
      ; on-natural = Closed.on-natural derived
      ; on-product = Closed.on-product derived
      ; on-sum = Closed.on-sum derived
      ; on-tree = Closed.on-tree derived
      ; on-identity = Closed.on-identity derived
      ; on-result = λ a b n m →
          transport (Derivable Q (combined i Φ) Γ)
            ( component-β i Φ (a , b) x (index-point (Φ x (a , b)))
            ∙ index-point-β (Φ x (a , b)))
            ( branch a b n m
                (component i Φ (a , b) x (index-point (Φ x (a , b)))))
      ; on-branch = λ a b n m z →
          transport (Derivable Q (combined i Φ) Γ)
            ( component-β i Φ (a , b) x (member-point (Φ x (a , b)) z)
            ∙ member-point-β (Φ x (a , b)) z)
            ( branch a b n m
                (component i Φ (a , b) x (member-point (Φ x (a , b)) z)))
      }

  -- No reflection's carrier is derivable by several operators together.
  not-derivable-together :
    ((X : Set ℓ) → FunExt X (λ _ → C))
    → (Ψ : Specification.Operator D)
      (r : Specification.Reflection Q Ψ)
      (i : C) (Φ : D i → Specification.Operator D)
    → Specification.Name
        (Specification.Closure.interpret (Specification.Reflection.closure r))
        i
    → ((x : D i)
       → Closed Q (Φ x)
           (Specification.Name
             (Specification.Closure.interpret
               (Specification.Reflection.closure r))))
    → {ν : Level} (Γ : Ced ν C)
    → Γ ⊆ Specification.Name
        (Specification.Closure.interpret (Specification.Reflection.closure r))
    → ¬ Derivable Q (combined i Φ) Γ (Specification.Reflection.carrier r)
  not-derivable-together extensionality Ψ r i Φ index closed Γ named d =
    let L = Specification.Reflection.closure r
    in carrier-unnamed Q retracts Ψ r
         ( least {Γ = Γ} named
             ( combined-closed (named-closed extensionality L) i Φ index
                 closed)
             d)

------------------------------------------------------------------------
-- The operator must be the closure's own

-- The constant operator at a code c derives c from nothing, as its index
-- at the unit family. So a carrier is derivable by an operator its
-- closure need not be closed under, and no reflection of the constant
-- operator at c has carrier c.

module _ {κ ℓ : Level} {C : Set κ} (D : C → Set ℓ) where

  -- The constant operator at a code c: the family of c with c at every
  -- point of its decoding.
  constant : C → Specification.Operator D
  constant c F = c , (λ _ → c)

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} (Q : Specification.Formers C D)
  where

  constant-derivable :
    (c : C) → Derivable Q (constant D c) ∅ᶜ c
  constant-derivable c =
    result (Specification.Formers.unit Q)
      (λ _ → Specification.Formers.unit Q)
      unit (λ _ → unit)

  constant-unreflected :
    Retracts Q
    → ((X : Set ℓ) → FunExt X (λ _ → C))
    → (c : C)
      (r : Specification.Reflection Q (constant D c))
    → ¬ (Specification.Reflection.carrier r ＝ c)
  constant-unreflected retracts extensionality c r e =
    not-derivable Q retracts extensionality (constant D c) r
      ( transport (Derivable Q (constant D c) ∅ᶜ) (e ⁻¹)
          (constant-derivable c))

------------------------------------------------------------------------
-- Universes named from below are not of degree one

-- If every name of a universe u is derivable, u's child is not Mahlo: the
-- child's reflection of the identity, read in the parent, is a universe
-- whose carrier code is a name of u, hence derivable, against
-- `not-derivable`.

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} (Q : Specification.Formers C D)
  where

  derivable-not-mahlo :
    Retracts Q
    → ((X : Set ℓ) → FunExt X (λ _ → C))
    → (u : Stationarity.Universe Q)
    → Specification.Name
        (Specification.Closure.interpret (Specification.Reflection.closure u))
      ⊆ Derivable Q (λ F → F) ∅ᶜ
    → ¬ Stationarity.Mahlo-Of Q (suc zero) u
  derivable-not-mahlo retracts extensionality u named m =
    let L = Specification.Reflection.closure u
        r = pr₁ (m (λ F → F))
    in not-derivable Q retracts extensionality (λ F → F)
         ( Stationarity.included Q u
           ( Stationarity.universe (child-formers L) r))
         ( named (Specification.Reflection.carrier r , refl))

------------------------------------------------------------------------
-- The reflector Naming builds has degree zero

-- Naming's closure for an operator names only derivable names
-- (Naming.Cedents.named-derivable), and so does its move along the
-- admission's retraction. So its universe for the identity is not of
-- degree one, whatever the degree of the ambient reflector it is built
-- from.

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} (Q : Specification.Formers C D)
  where

  naming-degree-zero :
    Retracts Q
    → (extensionality : (X : Set ℓ) → FunExt X (λ _ → C))
      (admission : Naming.Admission D)
      (reflections : Specification.Mahlo (Ambient.formers ℓ))
    → ¬ Stationarity.Degree Q (suc zero)
          (Naming.mahlo extensionality admission reflections)
  naming-degree-zero retracts extensionality admission reflections d =
    let L = Specification.Reflection.closure
              (Specification.Mahlo.reflect reflections
                (Trees.requests Q (λ F → F)))
    in derivable-not-mahlo Q retracts extensionality
         ( Stationarity.universe Q
           ( Specification.Mahlo.reflect
             ( Naming.mahlo extensionality admission reflections)
             ( λ F → F)))
         ( λ n →
           Named.named-derivable Q (λ F → F) L
             ( Naming.Admission.out admission
                 (Naming.Value Q (λ F → F) L) (pr₁ n)
             , pr₂ n))
         ( d (λ F → F))

------------------------------------------------------------------------
-- Admission needs codes above their decodings

-- A family whose codes form a small type, with formers that decode up to
-- retraction, does not admit every small type: its own code type would be
-- a retract of the decoding of the code admitting it, which no-retract
-- refutes. So the admission `naming-degree-zero` assumes lives only at
-- families whose codes lie above their decodings.

module _
  {ℓ : Level} {C : Set ℓ} {D : C → Set ℓ} (Q : Specification.Formers C D)
  where

  admission-not-small : Retracts Q → ¬ Naming.Admission D
  admission-not-small retracts admission =
    no-retract Q retracts (Naming.Admission.admit admission C)
      (Naming.Admission.out admission C)
      (Naming.Admission.into admission C)
      (Naming.Admission.out-into admission C)
