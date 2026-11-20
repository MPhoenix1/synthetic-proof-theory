{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Univalent.Sets where

-- Unique names for the parent of sets. A closure of the parent of small
-- sets (Mahlo.Sets) lives on a small type, since on a set no closure naming
-- the two-point set has unique names. Under univalence and extensionality
-- (`Hypotheses`) the parent of small sets is a univalent parent
-- (`set-parent`, Univalent.Completion): small sets are identified exactly
-- when their points are equivalent (`small-set-identifications` of
-- Mahlo.Sets). So a closure that collects names has one with unique names
-- on a completion of its decoding, and a closure with unique names collects
-- names (Univalent.Completion).
--
-- The sum of two operators of the parent of sets returns one family whose
-- members are the first family's index, its members and the second
-- family's members, over a sum built with the parent's own formers
-- (`first-codes`, `joined-codes`, `joined-members`, `joined-operator`,
-- Ψ ⊎⟨ H ⟩ Φ); a closure of it names them (`first-index-is-named`,
-- `first-members-are-named`, `second-members-are-named`). Global weakly
-- initial covers by sets give the operator returning the covers of the
-- index of a family (`covering`), and with it the covering operators of
-- the parent (`set-covering-operators`, Univalent.Covering). So:
--
--   plain rule  →  Global-Weakly-Initial-Set-Covers ℓ  →
--     Σ (R : Π Ψ. Small-Closure Ψ). Π Ψ. Collects-Names (R Ψ),
--
-- and with completions closures with unique names for every operator
-- (`unique-names-from-covers` of Univalent.Covering), with no excluded
-- middle and no choice; choice for the small sets is one source of the
-- covers (`unique-names-from-choice`). A closure that collects names
-- refines every cover by a set whose fibers are covered by names
-- (`collection-refines-set-covers`).

open import SPT.Base
open import SPT.Foundation.Covers using (Covered; Cover)
open import SPT.Foundation.Covers.WeaklyInitial using
  ( Weakly-Initial-Covers; Weakly-Initial-Set-Covers
  ; Global-Weakly-Initial-Set-Covers; Projective
  ; choice-gives-weakly-initial-set-covers )
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Fibers using (fiber)
open import SPT.Foundation.Isomorphisms using
  (≅-refl; transport-is-isomorphism)
open import SPT.Foundation.Propositions using (is-set; propositions-are-sets)
open import SPT.Foundation.Sets using (sums-of-sets-are-sets)
open import SPT.Foundation.Univalence using (is-univalent)
import SPT.Mahlo.Specification as Specification
open import SPT.Mahlo.Sets using
  ( Small-Set; small-set; points; points-form-a-set; Operator; set-formers
  ; set-laws; small-set-identifications )
open import SPT.Mahlo.DS.Cedents using (member-name)
open import SPT.Mahlo.DS.Univalent.Names using (Isomorphic-Name)
open import SPT.Mahlo.DS.Univalent.Completion using
  (Univalent-Parent; Small-Closure; Has-Unique-Names; Collects-Names
  ; Completions)
open import SPT.Mahlo.DS.Univalent.Covering using
  ( Covering-Operators; Named-Refinement; collection-refines-covers
  ; unique-names-from-covers )

------------------------------------------------------------------------
-- The parent of sets is univalent

-- Mathematical shape: extensionality for the dependent functions of level
-- ℓ and for families of small sets over a type of level ℓ, and univalence
-- at ℓ.
record Hypotheses (ℓ : Level) : Set (lsuc ℓ) where
  field
    functions : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y
    code-families : (X : Set ℓ) → FunExt X (λ _ → Small-Set ℓ)
    univalence : is-univalent ℓ

set-parent : {ℓ : Level} → Hypotheses ℓ →
  Univalent-Parent {C = Small-Set ℓ} points
set-parent H = record
  { formers = set-formers (Hypotheses.functions H)
  ; laws = set-laws (Hypotheses.functions H)
  ; functions = Hypotheses.functions H
  ; code-families = Hypotheses.code-families H
  ; identifications =
      small-set-identifications (Hypotheses.functions H)
        (Hypotheses.univalence H)
  }

------------------------------------------------------------------------
-- Joined operators

-- The joined family is indexed by a sum over the two-point set: first a
-- header and the first family's members, then the second family's members.
-- Its members there are the first family's index, its members and the
-- second family's members.

module _ {ℓ : Level} (H : Hypotheses ℓ) where

  open Hypotheses H

  first-codes : Specification.Family {C = Small-Set ℓ} points →
    Lift ℓ 𝟚 → Small-Set ℓ
  first-codes G (lift ₀) = Specification.Formers.unit (set-formers functions)
  first-codes G (lift ₁) = pr₁ G

  joined-codes : (G V : Specification.Family {C = Small-Set ℓ} points) →
    Lift ℓ 𝟚 → Small-Set ℓ
  joined-codes G V (lift ₀) =
    Specification.Formers.sum (set-formers functions)
      (Specification.Formers.two (set-formers functions) , first-codes G)
  joined-codes G V (lift ₁) = pr₁ V

  joined-members : (G V : Specification.Family {C = Small-Set ℓ} points) →
    points
      (Specification.Formers.sum (set-formers functions)
        (Specification.Formers.two (set-formers functions) ,
          joined-codes G V)) →
    Small-Set ℓ
  joined-members G V (lift ₀ , lift ₀ , u) = pr₁ G
  joined-members G V (lift ₀ , lift ₁ , y) = pr₂ G y
  joined-members G V (lift ₁ , i) = pr₂ V i

-- The sum of two operators: at each family, the joined family of theirs.
infixr 10 joined-operator

joined-operator : {ℓ : Level} (H : Hypotheses ℓ) →
  Operator ℓ → Operator ℓ → Operator ℓ
joined-operator H Ψ Φ F =
  Specification.Formers.sum (set-formers (Hypotheses.functions H))
    (Specification.Formers.two (set-formers (Hypotheses.functions H)) ,
      joined-codes H (Ψ F) (Φ F)) ,
  joined-members H (Ψ F) (Φ F)

syntax joined-operator H Ψ Φ = Ψ ⊎⟨ H ⟩ Φ

-- The members of the joined family are named, so the first family's
-- index and members are, and so are the second family's members.

module _ {ℓ : Level} (H : Hypotheses ℓ) (Ψ Φ : Operator ℓ) {K : Set ℓ}
  (L : Specification.Closure (set-formers (Hypotheses.functions H))
    (Ψ ⊎⟨ H ⟩ Φ) K)
  where

  open Hypotheses H
  open Specification.Closure L using (interpret; inner; inner-β)

  first-index-is-named :
    (F : Specification.Family (Specification.Decode points interpret)) →
    Specification.Name interpret
      (pr₁ (Ψ (Specification.map points interpret F)))
  first-index-is-named F =
    member-name code-families L (inner F) (inner-β F)
      (lift ₀ , lift ₀ , lift ⋆)

  first-members-are-named :
    (F : Specification.Family (Specification.Decode points interpret))
    (y : points (pr₁ (Ψ (Specification.map points interpret F)))) →
    Specification.Name interpret
      (pr₂ (Ψ (Specification.map points interpret F)) y)
  first-members-are-named F y =
    member-name code-families L (inner F) (inner-β F) (lift ₀ , lift ₁ , y)

  second-members-are-named :
    (F : Specification.Family (Specification.Decode points interpret))
    (i : points (pr₁ (Φ (Specification.map points interpret F)))) →
    Specification.Name interpret
      (pr₂ (Φ (Specification.map points interpret F)) i)
  second-members-are-named F i =
    member-name code-families L (inner F) (inner-β F) (lift ₁ , i)

------------------------------------------------------------------------
-- The covering operator

-- The weakly initial covers by sets of the index of a family, as a family.

module _ {ℓ : Level} (W : Global-Weakly-Initial-Set-Covers ℓ) where

  covering : Operator ℓ
  covering F =
    small-set
      (Weakly-Initial-Covers.index
        (Weakly-Initial-Set-Covers.covers
          (W (points (pr₁ F)) (points-form-a-set (pr₁ F)))))
      (Weakly-Initial-Set-Covers.index-is-set
        (W (points (pr₁ F)) (points-form-a-set (pr₁ F)))) ,
    (λ i →
      small-set
        (Weakly-Initial-Covers.domain
          (Weakly-Initial-Set-Covers.covers
            (W (points (pr₁ F)) (points-form-a-set (pr₁ F))))
          i)
        (Weakly-Initial-Set-Covers.domains-are-sets
          (W (points (pr₁ F)) (points-form-a-set (pr₁ F))) i))

-- An operator joined with the covering one: a closure of it names the
-- domains of the covers of every arity, the covering family's members at
-- the constant family over that arity.

module _ {ℓ : Level} (H : Hypotheses ℓ) (W : Global-Weakly-Initial-Set-Covers ℓ)
  where

  set-covering-operators : Covering-Operators (set-parent H)
  set-covering-operators = record
    { covers = λ c →
        Weakly-Initial-Set-Covers.covers (W (points c) (points-form-a-set c))
    ; joined = λ Ψ → Ψ ⊎⟨ H ⟩ covering W
    ; index-is-named = λ Ψ L F → first-index-is-named H Ψ (covering W) L F
    ; members-are-named = λ Ψ L F y →
        first-members-are-named H Ψ (covering W) L F y
    ; domains-are-named = λ Ψ L a i →
        pr₁ (second-members-are-named H Ψ (covering W) L (a , λ x → a) i) ,
        transport-is-isomorphism id
          (ap points
            (pr₂
              (second-members-are-named H Ψ (covering W) L (a , λ x → a)
                i)))
    }

------------------------------------------------------------------------
-- From choice

-- Choice for the small sets gives the covers: each set covers itself.

module _ {ℓ : Level} (H : Hypotheses ℓ) where

  unique-names-from-choice : Completions ℓ (Small-Set ℓ) →
    ((A : Set ℓ) → is-set A → Projective A) →
    (R : (Ψ : Operator ℓ) → Small-Closure (set-parent H) Ψ) →
    (Ψ : Operator ℓ) →
    Σ (Small-Closure (set-parent H) Ψ)
      (λ L → Has-Unique-Names (set-parent H) (pr₂ L))
  unique-names-from-choice completions choice =
    unique-names-from-covers (set-parent H)
      (set-covering-operators H (choice-gives-weakly-initial-set-covers choice))
      completions

------------------------------------------------------------------------
-- Collection refines covers by sets

-- The fibers of a cover by a set are small sets.

module _ {ℓ : Level} (H : Hypotheses ℓ) {Ψ : Operator ℓ} {K : Set ℓ}
  (L : Specification.Closure (set-formers (Hypotheses.functions H)) Ψ K)
  where

  open Specification.Closure L using (interpret)

  collection-refines-set-covers : Collects-Names (set-parent H) L →
    (a : K) {E : Set ℓ} → is-set E →
    (q : E → Specification.Decode points interpret a) → Cover ℓ q →
    ((x : Specification.Decode points interpret a) →
      Covered ℓ
        (Isomorphic-Name (Specification.Decode points interpret)
          (fiber q x))) →
    Covered ℓ (Named-Refinement (set-parent H) L a q)
  collection-refines-set-covers collection a s q cover merely =
    collection-refines-covers (set-parent H) L collection a q cover
      (λ x →
        small-set (fiber q x)
          (sums-of-sets-are-sets s
            (λ e →
              propositions-are-sets (points-form-a-set (interpret a) (q e) x))))
      (λ x → ≅-refl)
      merely
