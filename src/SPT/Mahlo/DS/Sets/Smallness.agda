{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Sets.Smallness where

-- The smallness principle for set-valued descriptions with set arities
-- (`Set-Smallness`), and with unique names (`Univalent-Set-Smallness`).
-- Each is the rule of the parent of small sets in the corresponding form:
-- the principle gives a closure of every operator, the algebra of its
-- description (Sets.Ambient; `closures`), and closures of every operator
-- give the principle through the realization (Sets.Realization;
-- `smallness`). Both translations keep the decoding literally, so unique
-- names pass both ways (`unique-closures`, `univalent-smallness`).
--
-- The passage between the two forms (`Set-Names-Passage`) holds given
-- completions into the small sets and global weakly initial covers by
-- sets, by Univalent.Covering at the parent of sets (`set-names-passage`),
-- with no excluded middle and no choice; choice for the small sets is one
-- source of the covers (`set-names-passage-from-choice`).

open import SPT.Base
open import SPT.Foundation.Covers.WeaklyInitial using
  ( Global-Weakly-Initial-Set-Covers; Projective
  ; choice-gives-weakly-initial-set-covers )
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Propositions using (is-proposition; is-set)
import SPT.Mahlo.Specification as Specification
open import SPT.Mahlo.Sets using (Small-Set; Operator; set-formers)

open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.IR.Description using (Desc)
open import SPT.Mahlo.DS.Sets.Ambient using
  (description; description-arities; closure)
open import SPT.Mahlo.DS.Sets.Description using (Set-Arities)
open import SPT.Mahlo.DS.Sets.Realization using
  (frontier-operator; algebra-of-closures; law-of-closures)
open import SPT.Mahlo.DS.Univalent.Completion using (Completions)
open import SPT.Mahlo.DS.Univalent.Covering using (unique-names-from-covers)
open import SPT.Mahlo.DS.Univalent.Sets using
  (Hypotheses; set-parent; set-covering-operators)

------------------------------------------------------------------------
-- The principles

-- Mathematical shape: Π γ. Set-Arities γ → Σ (M : Algebra ℓ γ). Law M.
record Set-Smallness (ℓ : Level) : Set (lsuc ℓ) where
  field
    algebra : (γ : Desc {s = ℓ} (Small-Set ℓ)) → Set-Arities γ →
      Algebra ℓ γ
    law : (γ : Desc {s = ℓ} (Small-Set ℓ)) (arities : Set-Arities γ) →
      Law (algebra γ arities)

-- The same, every small set named at most once.
record Univalent-Set-Smallness (ℓ : Level) : Set (lsuc ℓ) where
  field
    algebra : (γ : Desc {s = ℓ} (Small-Set ℓ)) → Set-Arities γ →
      Algebra ℓ γ
    law : (γ : Desc {s = ℓ} (Small-Set ℓ)) (arities : Set-Arities γ) →
      Law (algebra γ arities)
    unique : (γ : Desc {s = ℓ} (Small-Set ℓ)) (arities : Set-Arities γ)
      (X : Small-Set ℓ) →
      is-proposition
        (Specification.Name (Algebra.value (algebra γ arities)) X)

forget : {ℓ : Level} → Univalent-Set-Smallness ℓ → Set-Smallness ℓ
forget small = record
  { algebra = Univalent-Set-Smallness.algebra small
  ; law = Univalent-Set-Smallness.law small
  }

-- Merely declared: the passage from the principle to its form with
-- unique names.
Set-Names-Passage : (ℓ : Level) → Set (lsuc ℓ)
Set-Names-Passage ℓ = Set-Smallness ℓ → Univalent-Set-Smallness ℓ

------------------------------------------------------------------------
-- The principle and closures

-- The algebra of an operator's description is a closure of it.

module _ {ℓ : Level}
  (functions : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y)
  (code-families : (X : Set ℓ) → FunExt X (λ _ → Small-Set ℓ))
  where

  closures : Set-Smallness ℓ → (Ψ : Operator ℓ) →
    Σ (Set ℓ) (λ K → Specification.Closure (set-formers functions) Ψ K)
  closures small Ψ =
    Algebra.K
      (Set-Smallness.algebra small (description functions Ψ)
        (description-arities functions Ψ)) ,
    closure functions code-families Ψ
      (Set-Smallness.algebra small (description functions Ψ)
        (description-arities functions Ψ))
      (Set-Smallness.law small (description functions Ψ)
        (description-arities functions Ψ))

  -- Unique names pass to the closures, which interpret by the value.
  unique-closures : Univalent-Set-Smallness ℓ → (Ψ : Operator ℓ) →
    Σ (Σ (Set ℓ) (λ K →
        Specification.Closure (set-formers functions) Ψ K))
      (λ C → (X : Small-Set ℓ) →
        is-proposition
          (Specification.Name (Specification.Closure.interpret (pr₂ C)) X))
  unique-closures small Ψ =
    ( Algebra.K
        (Univalent-Set-Smallness.algebra small (description functions Ψ)
          (description-arities functions Ψ))
    , closure functions code-families Ψ
        (Univalent-Set-Smallness.algebra small (description functions Ψ)
          (description-arities functions Ψ))
        (Univalent-Set-Smallness.law small (description functions Ψ)
          (description-arities functions Ψ)) ) ,
    Univalent-Set-Smallness.unique small (description functions Ψ)
      (description-arities functions Ψ)

-- Closures of every operator give the principle; the realized algebra
-- decodes by the closure's interpretation, so its names are the closure's.

module _ {ℓ : Level}
  (functions : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y)
  where

  smallness : ((Ψ : Operator ℓ) →
    Σ (Set ℓ) (λ K → Specification.Closure (set-formers functions) Ψ K)) →
    Set-Smallness ℓ
  smallness R = record
    { algebra = algebra-of-closures functions R
    ; law = law-of-closures functions R
    }

  univalent-smallness : ((Ψ : Operator ℓ) →
    Σ (Σ (Set ℓ) (λ K →
        Specification.Closure (set-formers functions) Ψ K))
      (λ C → (X : Small-Set ℓ) →
        is-proposition
          (Specification.Name
            (Specification.Closure.interpret (pr₂ C)) X))) →
    Univalent-Set-Smallness ℓ
  univalent-smallness U = record
    { algebra = algebra-of-closures functions (λ Ψ → pr₁ (U Ψ))
    ; law = law-of-closures functions (λ Ψ → pr₁ (U Ψ))
    ; unique = λ γ arities →
        pr₂ (U (frontier-operator functions γ arities))
    }

------------------------------------------------------------------------
-- The passage from weakly initial covers

-- The principle's closures collect names through the covering operators,
-- and their completions have unique names (Univalent.Covering); the
-- realization brings those closures back to the principle.

module _ {ℓ : Level} (H : Hypotheses ℓ) where

  set-names-passage : Completions ℓ (Small-Set ℓ) →
    Global-Weakly-Initial-Set-Covers ℓ → Set-Names-Passage ℓ
  set-names-passage completions W small =
    univalent-smallness (Hypotheses.functions H)
      (unique-names-from-covers (set-parent H) (set-covering-operators H W)
        completions
        (closures (Hypotheses.functions H) (Hypotheses.code-families H)
          small))

  set-names-passage-from-choice : Completions ℓ (Small-Set ℓ) →
    ((A : Set ℓ) → is-set A → Projective A) → Set-Names-Passage ℓ
  set-names-passage-from-choice completions choice =
    set-names-passage completions
      (choice-gives-weakly-initial-set-covers choice)
