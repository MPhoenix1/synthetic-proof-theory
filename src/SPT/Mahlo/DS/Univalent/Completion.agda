{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Univalent.Completion where

-- Unique names from collection, over a univalent parent. A univalent parent
-- is a family of codes D : C → Set ℓ with formers and their decoding laws
-- (Mahlo.Decoding), extensionality for the dependent functions of level ℓ
-- and for the families of codes, and its identifications of codes read as
-- the equivalences of their decodings (`Univalent-Parent`). The parent of
-- small sets and the ambient parent are univalent parents under univalence
-- and extensionality (Univalent.Sets, Univalent.Types).
--
-- A closure of an operator lives on a small type (`Small-Closure`). It has
-- unique names when the names of every code form a proposition
-- (`Has-Unique-Names`); it collects names when every family of codes over
-- a code whose members are each covered by names up to isomorphism is
-- covered by a named cover (`Collects-Names`). A completion of a family of
-- codes over a small type is a small type with an embedding into the codes
-- and a covering map from the index that commutes with them (`Completion`).
--
-- * Given a completion of its decoding, a closure that collects names has
--   one with unique names on the completion (`completed-closure`,
--   `completed-closure-has-unique-names`). A name of the closure is carried
--   to the completion; a code covered by such names is named there,
--   through a proposition of level ℓ that the parent's identifications
--   identify with the names (`names-in-the-completion`). Every family of
--   the completion is covered by families of the closure with the same
--   image (`families-are-covered`), by the covering map and the names of
--   Univalent.Gluing, so the closure's names of the formers and of Ψ's
--   family name them in the completion.
-- * A closure with unique names collects names, over the arity itself
--   (`unique-names-name-covered-codes`, `unique-names-collect-names`).
--
-- So, with completions of every family of codes (`Completions`),
--
--   Π Ψ. Σ (L : Small-Closure Ψ). Has-Unique-Names L
--     ⇔  Σ (R : Π Ψ. Small-Closure Ψ). Π Ψ. Collects-Names (R Ψ)
--
-- (`unique-names-from-collection`, `collection-from-unique-names`; the
-- second direction needs no completion).

open import SPT.Base
open import SPT.Foundation.Covers using
  ( Covered; Cover; map-covered; bind-covered; extract-proposition
  ; covered-by-point; identity-is-cover )
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Fibers using (fiber)
open import SPT.Foundation.Isomorphisms using
  (_≅_; forward; backward; Σ-cong; transport-is-isomorphism)
open import SPT.Foundation.Propositions using (is-proposition)
open import SPT.Foundation.Propositions.Closure using
  (isomorphic-to-a-proposition)
open import SPT.Foundation.Univalence using
  (Equivalence; isomorphism-to-equivalence; equivalence-to-isomorphism)
open import SPT.Mahlo.Decoding using
  (DecodingLaws; child-formers; child-decoding)
import SPT.Mahlo.Specification as Specification
open import SPT.Mahlo.DS.Cedents using (member-name)
open import SPT.Mahlo.DS.Naming.Trees using (pair)
open import SPT.Mahlo.DS.Realization.Family using (cast)
open import SPT.Mahlo.DS.Univalent.Names using (Isomorphic-Name)
open import SPT.Mahlo.DS.Univalent.Gluing using
  (Named-Cover; named-covers-name-their-members)

------------------------------------------------------------------------
-- Univalent parents and their closures

-- Mathematical shape: formers on D with their decoding laws,
-- extensionality for the dependent functions of level ℓ and for the
-- families of codes, and (c ＝ c′) ≅ Equivalence (D c) (D c′).
record Univalent-Parent {κ ℓ : Level} {C : Set κ} (D : C → Set ℓ) :
  Set (κ ⊔ lsuc ℓ) where
  field
    formers : Specification.Formers C D
    laws : DecodingLaws formers
    functions : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y
    code-families : (X : Set ℓ) → FunExt X (λ _ → C)
    identifications : (c c′ : C) → (c ＝ c′) ≅ Equivalence (D c) (D c′)

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} (P : Univalent-Parent D)
  where

  open Univalent-Parent P

  -- A closure of Ψ on a small type.
  Small-Closure : Specification.Operator D → Set (κ ⊔ lsuc ℓ)
  Small-Closure Ψ = Σ (Set ℓ) (λ K → Specification.Closure formers Ψ K)

  -- Identity types moved along an identification of codes.
  identities-along : (c c′ : C) (e : c ＝ c′) (x y : D c) →
    Specification.Formers.identity formers c′ (cast (ap D e) x)
      (cast (ap D e) y)
      ＝ Specification.Formers.identity formers c x y
  identities-along c .c refl x y = refl

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} (P : Univalent-Parent D)
  {Ψ : Specification.Operator D} {K : Set ℓ} where

  open Univalent-Parent P

  -- The names of every code form a proposition.
  Has-Unique-Names : Specification.Closure formers Ψ K → Set (κ ⊔ ℓ)
  Has-Unique-Names L = (c : C) →
    is-proposition (Specification.Name (Specification.Closure.interpret L) c)

  -- Members covered by names up to isomorphism have a covered named cover.
  Collects-Names : Specification.Closure formers Ψ K → Set (κ ⊔ lsuc ℓ)
  Collects-Names L = (a : K)
    (B : Specification.Decode D (Specification.Closure.interpret L) a →
      C) →
    ((x : Specification.Decode D (Specification.Closure.interpret L) a) →
      Covered ℓ
        (Isomorphic-Name
          (Specification.Decode D (Specification.Closure.interpret L))
          (D (B x)))) →
    Covered ℓ
      (Named-Cover
        (Specification.Decode D (Specification.Closure.interpret L)) a
        (λ x → D (B x)))

------------------------------------------------------------------------
-- Completions

-- Mathematical shape: a small type with an embedding into the codes and a
-- covering map from K that commutes with them and S.
record Completion {κ ℓ : Level} {C : Set κ} {K : Set ℓ} (S : K → C) :
  Set (κ ⊔ lsuc ℓ) where
  field
    completed : Set ℓ
    decode : completed → C
    include : K → completed
    include-decodes : (k : K) → decode (include k) ＝ S k
    decode-is-an-embedding : (c : C) → is-proposition (fiber decode c)
    include-covers : Cover ℓ include

-- Completions of every family of codes over a small type.
Completions : {κ : Level} (ℓ : Level) (C : Set κ) → Set (κ ⊔ lsuc ℓ)
Completions ℓ C = (K : Set ℓ) (S : K → C) → Completion S

------------------------------------------------------------------------
-- Names in a completion

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} (P : Univalent-Parent D)
  {K : Set ℓ} {S : K → C} (Cm : Completion S) where

  open Univalent-Parent P
  open Completion Cm

  -- A name of the family gives one in the completion.
  carried : (c : C) → Specification.Name S c → Specification.Name decode c
  carried c n = include (pr₁ n) , include-decodes (pr₁ n) ∙ pr₂ n

  -- Names in the completion, read as equivalences of decodings.
  names-as-equivalences : (c : C) →
    Specification.Name decode c
      ≅ Σ completed (λ ρ → Equivalence (D (decode ρ)) (D c))
  names-as-equivalences c = Σ-cong (λ ρ → identifications (decode ρ) c)

  -- These form a proposition of level ℓ, since decoding is an embedding.
  equivalence-names-are-propositions : (c : C) →
    is-proposition (Σ completed (λ ρ → Equivalence (D (decode ρ)) (D c)))
  equivalence-names-are-propositions c =
    isomorphic-to-a-proposition (names-as-equivalences c)
      (decode-is-an-embedding c)

  -- A code covered by names of the family is named in the completion.
  names-in-the-completion : (c : C) →
    Covered ℓ (Specification.Name S c) → Specification.Name decode c
  names-in-the-completion c named =
    backward (names-as-equivalences c)
      (extract-proposition
        (map-covered (λ n → forward (names-as-equivalences c) (carried c n))
          named)
        (equivalence-names-are-propositions c))

------------------------------------------------------------------------
-- The closure on the completion

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} (P : Univalent-Parent D)
  {Ψ : Specification.Operator D} {K : Set ℓ}
  (L : Specification.Closure (Univalent-Parent.formers P) Ψ K)
  (collection : Collects-Names P L)
  (Cm : Completion (Specification.Closure.interpret L)) where

  open Univalent-Parent P
  open Specification.Closure L using (interpret)
  open Completion Cm

  ----------------------------------------------------------------------
  -- Families of the completion are covered by families of the closure

  -- The members of a family of the completion at include a, read at the
  -- points of a.
  members : (a : K) → (D (decode (include a)) → completed) →
    Specification.Decode D interpret a → C
  members a b′ x = decode (b′ (cast (ap D (include-decodes a ⁻¹)) x))

  -- Each member is covered by names of the closure: its code is covered by
  -- images of the closure's codes.
  members-are-merely-named : (a : K)
    (b′ : D (decode (include a)) → completed)
    (x : Specification.Decode D interpret a) →
    Covered ℓ
      (Isomorphic-Name (Specification.Decode D interpret)
        (D (members a b′ x)))
  members-are-merely-named a b′ x =
    map-covered
      (λ w → pr₁ w ,
        transport-is-isomorphism id
          (ap D (include-decodes (pr₁ w) ⁻¹ ∙ ap decode (pr₂ w))))
      (include-covers (b′ (cast (ap D (include-decodes a ⁻¹)) x)))

  -- The names of the members over a named cover (Univalent.Gluing).
  glued-names : (a : K) (b′ : D (decode (include a)) → completed) →
    Named-Cover (Specification.Decode D interpret) a
      (λ x → D (members a b′ x)) →
    (x : Specification.Decode D interpret a) →
    Isomorphic-Name (Specification.Decode D interpret) (D (members a b′ x))
  glued-names a b′ N =
    named-covers-name-their-members N (child-formers L)
      (child-decoding laws L) functions

  -- Through the parent's identifications, a name up to isomorphism
  -- identifies the codes.
  glued-identifications : (a : K) (b′ : D (decode (include a)) → completed)
    (N : Named-Cover (Specification.Decode D interpret) a
      (λ x → D (members a b′ x)))
    (x : Specification.Decode D interpret a) →
    interpret (pr₁ (glued-names a b′ N x)) ＝ members a b′ x
  glued-identifications a b′ N x =
    backward
      (identifications (interpret (pr₁ (glued-names a b′ N x)))
        (members a b′ x))
      (isomorphism-to-equivalence (pr₂ (glued-names a b′ N x)))

  -- A family of the completion at include a is covered by families of the
  -- closure with the same image.
  covered-family : (a : K) (b′ : D (decode (include a)) → completed) →
    Covered ℓ
      (Σ (Specification.Family (Specification.Decode D interpret))
        (λ F → Specification.map D interpret F
          ＝ Specification.map D decode (include a , b′)))
  covered-family a b′ =
    map-covered
      (λ N → (a , λ x → pr₁ (glued-names a b′ N x)) ,
        pair D code-families (include-decodes a ⁻¹)
          (glued-identifications a b′ N))
      (collection a (members a b′) (members-are-merely-named a b′))

  covered-family-at : (a′ : completed) → fiber include a′ →
    (b′ : D (decode a′) → completed) →
    Covered ℓ
      (Σ (Specification.Family (Specification.Decode D interpret))
        (λ F → Specification.map D interpret F
          ＝ Specification.map D decode (a′ , b′)))
  covered-family-at .(include a) (a , refl) b′ = covered-family a b′

  families-are-covered :
    (F′ : Specification.Family (Specification.Decode D decode)) →
    Covered ℓ
      (Σ (Specification.Family (Specification.Decode D interpret))
        (λ F → Specification.map D interpret F
          ＝ Specification.map D decode F′))
  families-are-covered F′ =
    bind-covered (include-covers (pr₁ F′))
      (λ w → covered-family-at (pr₁ F′) w (pr₂ F′))

  ----------------------------------------------------------------------
  -- Names in the completion

  -- An identity type at a code of the completion, from one at a code of
  -- the closure with the same image.
  identity-at : (a′ : completed) → fiber include a′ →
    (x y : D (decode a′)) →
    Specification.Name interpret
      (Specification.Formers.identity formers (decode a′) x y)
  identity-at .(include a) (a , refl) x y =
    transport (Specification.Name interpret)
      (identities-along P (decode (include a)) (interpret a)
        (include-decodes a) x y)
      (Specification.Closure.identity L a
        (cast (ap D (include-decodes a)) x)
        (cast (ap D (include-decodes a)) y))

  -- The index of Ψ's family is named in the completion.
  operator-index-is-named :
    (F′ : Specification.Family (Specification.Decode D decode)) →
    Specification.Name decode (pr₁ (Ψ (Specification.map D decode F′)))
  operator-index-is-named F′ =
    names-in-the-completion P Cm
      (pr₁ (Ψ (Specification.map D decode F′)))
      (map-covered
        (λ w → pr₁ (Specification.Closure.inner L (pr₁ w)) ,
          ap pr₁ (Specification.Closure.inner-β L (pr₁ w) ∙ ap Ψ (pr₂ w)))
        (families-are-covered F′))

  -- So is each of its members, read along the index's name.
  operator-members-are-named :
    (F′ : Specification.Family (Specification.Decode D decode))
    (z : D (decode (pr₁ (operator-index-is-named F′)))) →
    Specification.Name decode
      (pr₂ (Ψ (Specification.map D decode F′))
        (cast (ap D (pr₂ (operator-index-is-named F′))) z))
  operator-members-are-named F′ z =
    names-in-the-completion P Cm
      (pr₂ (Ψ (Specification.map D decode F′))
        (cast (ap D (pr₂ (operator-index-is-named F′))) z))
      (map-covered
        (λ w → member-name code-families L
          (Specification.Closure.inner L (pr₁ w))
          (Specification.Closure.inner-β L (pr₁ w) ∙ ap Ψ (pr₂ w))
          (cast (ap D (pr₂ (operator-index-is-named F′))) z))
        (families-are-covered F′))

  ----------------------------------------------------------------------
  -- The closure

  completed-closure : Specification.Closure formers Ψ completed
  completed-closure = record
    { interpret = decode
    ; empty =
        carried P Cm (Specification.Formers.empty formers)
          (Specification.Closure.empty L)
    ; unit =
        carried P Cm (Specification.Formers.unit formers)
          (Specification.Closure.unit L)
    ; two =
        carried P Cm (Specification.Formers.two formers)
          (Specification.Closure.two L)
    ; natural =
        carried P Cm (Specification.Formers.natural formers)
          (Specification.Closure.natural L)
    ; product = λ F′ →
        names-in-the-completion P Cm
          (Specification.Formers.product formers
            (Specification.map D decode F′))
          (map-covered
            (λ w → transport (Specification.Name interpret)
              (ap (Specification.Formers.product formers) (pr₂ w))
              (Specification.Closure.product L (pr₁ w)))
            (families-are-covered F′))
    ; sum = λ F′ →
        names-in-the-completion P Cm
          (Specification.Formers.sum formers (Specification.map D decode F′))
          (map-covered
            (λ w → transport (Specification.Name interpret)
              (ap (Specification.Formers.sum formers) (pr₂ w))
              (Specification.Closure.sum L (pr₁ w)))
            (families-are-covered F′))
    ; tree = λ F′ →
        names-in-the-completion P Cm
          (Specification.Formers.tree formers
            (Specification.map D decode F′))
          (map-covered
            (λ w → transport (Specification.Name interpret)
              (ap (Specification.Formers.tree formers) (pr₂ w))
              (Specification.Closure.tree L (pr₁ w)))
            (families-are-covered F′))
    ; identity = λ a′ x y →
        names-in-the-completion P Cm
          (Specification.Formers.identity formers (decode a′) x y)
          (map-covered (λ w → identity-at a′ w x y) (include-covers a′))
    ; inner = λ F′ →
        pr₁ (operator-index-is-named F′) ,
        (λ z → pr₁ (operator-members-are-named F′ z))
    ; inner-β = λ F′ →
        pair D code-families (pr₂ (operator-index-is-named F′))
          (λ z → pr₂ (operator-members-are-named F′ z))
    }

  completed-closure-has-unique-names : Has-Unique-Names P completed-closure
  completed-closure-has-unique-names = decode-is-an-embedding

------------------------------------------------------------------------
-- The characterization

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} (P : Univalent-Parent D)
  where

  open Univalent-Parent P

  -- Given completions, collection in the closures of every operator gives
  -- closures with unique names.
  unique-names-from-collection : Completions ℓ C →
    (R : (Ψ : Specification.Operator D) → Small-Closure P Ψ) →
    ((Ψ : Specification.Operator D) → Collects-Names P (pr₂ (R Ψ))) →
    (Ψ : Specification.Operator D) →
    Σ (Small-Closure P Ψ) (λ L → Has-Unique-Names P (pr₂ L))
  unique-names-from-collection completions R collect Ψ =
    ( Completion.completed
        (completions (pr₁ (R Ψ))
          (Specification.Closure.interpret (pr₂ (R Ψ))))
    , completed-closure P (pr₂ (R Ψ)) (collect Ψ)
        (completions (pr₁ (R Ψ))
          (Specification.Closure.interpret (pr₂ (R Ψ)))) ) ,
    completed-closure-has-unique-names P (pr₂ (R Ψ)) (collect Ψ)
      (completions (pr₁ (R Ψ)) (Specification.Closure.interpret (pr₂ (R Ψ))))

  -- In a closure with unique names, a code whose decoding is covered by
  -- names up to isomorphism is named: the names, read as equivalences, are
  -- a proposition of level ℓ.
  unique-names-name-covered-codes : {Ψ : Specification.Operator D}
    {K : Set ℓ} (L : Specification.Closure formers Ψ K) →
    Has-Unique-Names P L → (c : C) →
    Covered ℓ
      (Isomorphic-Name
        (Specification.Decode D (Specification.Closure.interpret L)) (D c)) →
    Isomorphic-Name
      (Specification.Decode D (Specification.Closure.interpret L)) (D c)
  unique-names-name-covered-codes L unique c named =
    let w = extract-proposition
              (map-covered
                (λ n → pr₁ n , isomorphism-to-equivalence (pr₂ n)) named)
              (isomorphic-to-a-proposition
                (Σ-cong (λ k →
                  identifications (Specification.Closure.interpret L k) c))
                (unique c))
    in pr₁ w , equivalence-to-isomorphism (pr₂ w)

  -- So a closure with unique names collects names, over the arity itself.
  unique-names-collect-names : {Ψ : Specification.Operator D} {K : Set ℓ}
    (L : Specification.Closure formers Ψ K) →
    Has-Unique-Names P L → Collects-Names P L
  unique-names-collect-names L unique a B merely =
    covered-by-point (record
      { domain = a
      ; owner = id
      ; names = λ x →
          pr₁ (unique-names-name-covered-codes L unique (B x) (merely x))
      ; named = λ x →
          pr₂ (unique-names-name-covered-codes L unique (B x) (merely x))
      ; covers = identity-is-cover
      })

  collection-from-unique-names :
    ((Ψ : Specification.Operator D) →
      Σ (Small-Closure P Ψ) (λ L → Has-Unique-Names P (pr₂ L))) →
    Σ ((Ψ : Specification.Operator D) → Small-Closure P Ψ)
      (λ R → (Ψ : Specification.Operator D) → Collects-Names P (pr₂ (R Ψ)))
  collection-from-unique-names U =
    (λ Ψ → pr₁ (U Ψ)) ,
    (λ Ψ → unique-names-collect-names (pr₂ (pr₁ (U Ψ))) (pr₂ (U Ψ)))
