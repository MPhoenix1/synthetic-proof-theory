{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Univalent.Types where

-- The passage of the smallness principle to its form with unique names,
-- for type-valued descriptions (`type-names-passage`):
--
--   Type-Hypotheses ℓ → Completions ℓ (Set ℓ) →
--     Global-Weakly-Initial-Covers ℓ → Names-Passage ℓ,
--
-- where Names-Passage ℓ = Smallness ℓ → Univalent-Smallness ℓ
-- (Univalent.Smallness). Under univalence and extensionality at ℓ
-- (`Type-Hypotheses`) the ambient parent (Mahlo.Ambient) is a univalent
-- parent (`type-parent`, Univalent.Completion), its identifications being
-- the equivalences (`type-identifications`).
--
-- The sum of two ambient operators returns one family whose members are
-- the first family's index, its members and the second family's members
-- (`first-type-codes`, `joined-type-codes`, `joined-type-members`,
-- Ψ ⊎ᵒ Φ); a closure of it names them (`first-type-index-is-named`,
-- `first-type-members-are-named`, `second-type-members-are-named`).
-- Weakly initial covers of every small type, with no set asked for
-- (Foundation.Covers.WeaklyInitial), give the operator returning the
-- covers of the index of a family (`type-covering`) and the covering
-- operators of the ambient parent (`type-covering-operators`). Univalent.
-- Covering then gives closures of every operator that collect names, and
-- with completions into the small types closures with unique names, a
-- reflector (`reflector-of-unique-names`, Univalent.Reflector) and so the
-- principle with unique names.
--
-- A named cover names its members through the limits of the maps out of
-- the iterated joins (Univalent.Gluing), so no set hypothesis and no
-- coherence above identity types is used; no excluded middle, choice or
-- resizing either.
--
-- Covered Strong Collection in the closures of the reflector from
-- smallness (Universes.ChildCollection's `Covered-Collection-Rule`) covers
-- every family of covered names by one naming function
-- (Univalent.Collection's `families-are-named`): a named cover over the
-- arity itself, owned by the identity. So these closures collect names,
-- and with completions smallness gives smallness with unique names
-- (`collection-passage`).

open import SPT.Base
open import SPT.Foundation.Covers using (map-covered; identity-is-cover)
open import SPT.Foundation.Covers.WeaklyInitial using
  (Weakly-Initial-Covers; Global-Weakly-Initial-Covers)
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Isomorphisms using
  (_≅_; transport-is-isomorphism)
open import SPT.Foundation.Univalence using
  (Equivalence; is-univalent; idtoeq; equivalence-to-isomorphism)
import SPT.Mahlo.Ambient as Ambient
import SPT.Mahlo.Specification as Specification
open import SPT.Mahlo.DS.Ambient using (mahlo)
open import SPT.Mahlo.DS.Cedents using (member-name)
open import SPT.IR.Smallness using (Smallness)
open import SPT.Mahlo.DS.Univalent.Collection using (families-are-named)
open import SPT.Mahlo.DS.Univalent.Completion using
  ( Univalent-Parent; Small-Closure; Has-Unique-Names; Completions
  ; unique-names-from-collection )
open import SPT.Mahlo.DS.Univalent.Covering using
  (Covering-Operators; unique-names-from-covers)
open import SPT.Mahlo.DS.Univalent.Gluing using (Named-Cover)
open import SPT.Mahlo.DS.Univalent.Reflector using (Reflector)
open import SPT.Mahlo.DS.Univalent.Smallness using
  (Univalent-Smallness; Names-Passage; smallness-of-reflector)
open import SPT.Universes.ChildCollection using (Covered-Collection-Rule)

------------------------------------------------------------------------
-- The ambient parent is univalent

-- Mathematical shape: extensionality for the dependent functions and the
-- families of types of level ℓ, and univalence at ℓ.
record Type-Hypotheses (ℓ : Level) : Set (lsuc ℓ) where
  field
    functions : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y
    families : (X : Set ℓ) → FunExt X (λ _ → Set ℓ)
    univalence : is-univalent ℓ

-- Identifications of small types are their equivalences.
type-identifications : {ℓ : Level} → is-univalent ℓ → (X Y : Set ℓ) →
  (X ＝ Y) ≅ Equivalence X Y
type-identifications univalence X Y =
  equivalence-to-isomorphism (idtoeq X Y , univalence X Y)

type-parent : {ℓ : Level} → Type-Hypotheses ℓ →
  Univalent-Parent (λ (A : Set ℓ) → A)
type-parent {ℓ} H = record
  { formers = Ambient.formers ℓ
  ; laws = Ambient.laws ℓ
  ; functions = Type-Hypotheses.functions H
  ; code-families = Type-Hypotheses.families H
  ; identifications = type-identifications (Type-Hypotheses.univalence H)
  }

------------------------------------------------------------------------
-- Joined operators

-- The joined family is indexed by a sum over the two points: first a
-- header and the first family's members, then the second family's members.

module _ {ℓ : Level} where

  first-type-codes : Specification.Family (λ (A : Set ℓ) → A) →
    Lift ℓ 𝟚 → Set ℓ
  first-type-codes G (lift ₀) =
    Specification.Formers.unit (Ambient.formers ℓ)
  first-type-codes G (lift ₁) = pr₁ G

  joined-type-codes : (G V : Specification.Family (λ (A : Set ℓ) → A)) →
    Lift ℓ 𝟚 → Set ℓ
  joined-type-codes G V (lift ₀) =
    Specification.Formers.sum (Ambient.formers ℓ)
      (Specification.Formers.two (Ambient.formers ℓ) , first-type-codes G)
  joined-type-codes G V (lift ₁) = pr₁ V

  joined-type-members :
    (G V : Specification.Family (λ (A : Set ℓ) → A)) →
    Specification.Formers.sum (Ambient.formers ℓ)
      (Specification.Formers.two (Ambient.formers ℓ) ,
        joined-type-codes G V) →
    Set ℓ
  joined-type-members G V (lift ₀ , lift ₀ , u) = pr₁ G
  joined-type-members G V (lift ₀ , lift ₁ , y) = pr₂ G y
  joined-type-members G V (lift ₁ , i) = pr₂ V i

-- The sum of two operators: at each family, the joined family of theirs.
infixr 10 _⊎ᵒ_

_⊎ᵒ_ : {ℓ : Level} → Ambient.Operator ℓ → Ambient.Operator ℓ →
  Ambient.Operator ℓ
_⊎ᵒ_ {ℓ} Ψ Φ F =
  Specification.Formers.sum (Ambient.formers ℓ)
    (Specification.Formers.two (Ambient.formers ℓ) ,
      joined-type-codes (Ψ F) (Φ F)) ,
  joined-type-members (Ψ F) (Φ F)

-- The members of the joined family are named, so the first family's
-- index and members are, and so are the second family's members.

module _ {ℓ : Level} (families : (X : Set ℓ) → FunExt X (λ _ → Set ℓ))
  (Ψ Φ : Ambient.Operator ℓ) {K : Set ℓ}
  (L : Specification.Closure (Ambient.formers ℓ) (Ψ ⊎ᵒ Φ) K)
  where

  open Specification.Closure L using (interpret; inner; inner-β)

  first-type-index-is-named :
    (F : Specification.Family (Specification.Decode (λ X → X) interpret)) →
    Specification.Name interpret
      (pr₁ (Ψ (Specification.map (λ X → X) interpret F)))
  first-type-index-is-named F =
    member-name families L (inner F) (inner-β F) (lift ₀ , lift ₀ , lift ⋆)

  first-type-members-are-named :
    (F : Specification.Family (Specification.Decode (λ X → X) interpret))
    (y : pr₁ (Ψ (Specification.map (λ X → X) interpret F))) →
    Specification.Name interpret
      (pr₂ (Ψ (Specification.map (λ X → X) interpret F)) y)
  first-type-members-are-named F y =
    member-name families L (inner F) (inner-β F) (lift ₀ , lift ₁ , y)

  second-type-members-are-named :
    (F : Specification.Family (Specification.Decode (λ X → X) interpret))
    (i : pr₁ (Φ (Specification.map (λ X → X) interpret F))) →
    Specification.Name interpret
      (pr₂ (Φ (Specification.map (λ X → X) interpret F)) i)
  second-type-members-are-named F i =
    member-name families L (inner F) (inner-β F) (lift ₁ , i)

------------------------------------------------------------------------
-- The covering operator

module _ {ℓ : Level} (W : Global-Weakly-Initial-Covers ℓ) where

  -- The weakly initial covers of the index of a family, as a family.
  type-covering : Ambient.Operator ℓ
  type-covering F =
    Weakly-Initial-Covers.index (W (pr₁ F)) ,
    Weakly-Initial-Covers.domain (W (pr₁ F))

-- An operator joined with the covering one: a closure of it names the
-- domains of the covers of every arity, the covering family's members at
-- the constant family over that arity.

module _ {ℓ : Level} (H : Type-Hypotheses ℓ)
  (W : Global-Weakly-Initial-Covers ℓ) where

  type-covering-operators : Covering-Operators (type-parent H)
  type-covering-operators = record
    { covers = W
    ; joined = λ Ψ → Ψ ⊎ᵒ type-covering W
    ; index-is-named = λ Ψ L F →
        first-type-index-is-named (Type-Hypotheses.families H) Ψ
          (type-covering W) L F
    ; members-are-named = λ Ψ L F y →
        first-type-members-are-named (Type-Hypotheses.families H) Ψ
          (type-covering W) L F y
    ; domains-are-named = λ Ψ L a i →
        pr₁
          (second-type-members-are-named (Type-Hypotheses.families H) Ψ
            (type-covering W) L (a , λ x → a) i) ,
        transport-is-isomorphism id
          (pr₂
            (second-type-members-are-named (Type-Hypotheses.families H) Ψ
              (type-covering W) L (a , λ x → a) i))
    }

------------------------------------------------------------------------
-- The passage

-- Closures with unique names of every operator are a reflector.
reflector-of-unique-names : {ℓ : Level} (H : Type-Hypotheses ℓ) →
  ((Ψ : Ambient.Operator ℓ) →
    Σ (Small-Closure (type-parent H) Ψ)
      (λ L → Has-Unique-Names (type-parent H) (pr₂ L))) →
  Reflector ℓ
reflector-of-unique-names H U = record
  { mahlo = record
      { reflect = λ Ψ → record
          { carrier = pr₁ (pr₁ (U Ψ))
          ; closure = pr₂ (pr₁ (U Ψ))
          }
      }
  ; unique = λ Ψ → pr₂ (U Ψ)
  }

type-names-passage : {ℓ : Level} → Type-Hypotheses ℓ →
  Completions ℓ (Set ℓ) → Global-Weakly-Initial-Covers ℓ → Names-Passage ℓ
type-names-passage H completions W small =
  smallness-of-reflector
    (reflector-of-unique-names H
      (unique-names-from-covers (type-parent H) (type-covering-operators H W)
        completions
        (λ Ψ →
          Specification.Reflection.carrier
            (Specification.Mahlo.reflect
              (mahlo (Type-Hypotheses.families H) small) Ψ) ,
          Specification.Reflection.closure
            (Specification.Mahlo.reflect
              (mahlo (Type-Hypotheses.families H) small) Ψ))))

------------------------------------------------------------------------
-- The passage from collection in the reflector's closures

collection-passage : {ℓ : Level} (H : Type-Hypotheses ℓ) →
  Completions ℓ (Set ℓ) → (small : Smallness ℓ) →
  Covered-Collection-Rule (mahlo (Type-Hypotheses.families H) small) →
  Univalent-Smallness ℓ
collection-passage H completions small rule =
  smallness-of-reflector
    (reflector-of-unique-names H
      (unique-names-from-collection (type-parent H) completions
        (λ Ψ →
          Specification.Reflection.carrier
            (Specification.Mahlo.reflect
              (mahlo (Type-Hypotheses.families H) small) Ψ) ,
          Specification.Reflection.closure
            (Specification.Mahlo.reflect
              (mahlo (Type-Hypotheses.families H) small) Ψ))
        (λ Ψ a B merely →
          map-covered
            (λ ns → record
              { domain = a
              ; owner = id
              ; names = λ x → pr₁ (ns x)
              ; named = λ x → pr₂ (ns x)
              ; covers = identity-is-cover
              })
            (families-are-named
              (Specification.Reflection.closure
                (Specification.Mahlo.reflect
                  (mahlo (Type-Hypotheses.families H) small) Ψ))
              (Type-Hypotheses.functions H) (rule Ψ) a B merely))))
