{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Univalent.Smallness where

-- The smallness principle with unique names. Smallness (IR.Smallness) asks
-- of every type-valued description a small algebra with its law; asking
-- also that each type has at most one name in it, so that the decoding is
-- an embedding, gives the principle with unique names
-- (`Univalent-Smallness`):
--
--   Π γ. Σ (M : Algebra ℓ γ). Law M × Π X. is-proposition (Name (value M) X).
--
-- At each description this is Shulman's univalent universe without
-- elimination, on the algebra's own carrier: its path rule is the names of
-- identified decodings (Construction's `names`, `names-β`; `universe-of`),
-- whose introductions are the algebra literally
-- (`introductions-of-universe`); conversely a universe's introductions are
-- such an algebra, its names unique by Lumsdaine's lemma. So the principle
-- is Shulman's universes of every description (`universes`,
-- `smallness-of-universes`). Ambient's translations keep the decoding
-- literally, so it is also the Mahlo rule with unique names, with the
-- extensionality of the plain equivalence (`reflector-of-smallness`,
-- `smallness-of-reflector`), and the plain smallness it forgets to
-- (`forget`) is Ambient's, by refl (`forgetting-names`). Whether Smallness
-- gives the principle with unique names, the passage from small lawful
-- algebras to small lawful algebras with embedding decodings, is declared
-- and not inhabited (`Names-Passage`): it is the question whether the
-- plain Mahlo rule gives its form with unique names.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Propositions using (is-proposition)
import SPT.Mahlo.Specification as Specification

open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.Mahlo.DS.Ambient using (description; smallness; mahlo)
open import SPT.IR.Description using (Desc)
import SPT.Mahlo.DS.Realization as Realization
open import SPT.IR.Smallness using (Smallness)
open import SPT.Mahlo.DS.Univalent.Construction using (names; names-β)
open import SPT.Mahlo.DS.Univalent.Reflector using (Reflector)
import SPT.Mahlo.DS.Univalent.Reflector.Universes as Universes
open import SPT.IR.Univalent.Universe using (Universe; fibers)

------------------------------------------------------------------------
-- The principle

-- Mathematical shape: Π γ. a small algebra of γ with its law, every type
-- named at most once.
record Univalent-Smallness (ℓ : Level) : Set (lsuc ℓ) where
  field
    algebra : (γ : Desc {s = ℓ} (Set ℓ)) → Algebra ℓ γ
    law : (γ : Desc {s = ℓ} (Set ℓ)) → Law (algebra γ)
    unique : (γ : Desc {s = ℓ} (Set ℓ)) (X : Set ℓ) →
      is-proposition (Specification.Name (Algebra.value (algebra γ)) X)

-- Forgetting the names.
forget : {ℓ : Level} → Univalent-Smallness ℓ → Smallness ℓ
forget small = record
  { algebra = Univalent-Smallness.algebra small
  ; law = Univalent-Smallness.law small
  }

-- Merely declared: the passage from Smallness to its form with unique
-- names.
Names-Passage : (ℓ : Level) → Set (lsuc ℓ)
Names-Passage ℓ = Smallness ℓ → Univalent-Smallness ℓ

------------------------------------------------------------------------
-- At one description

-- A lawful algebra with unique names is Shulman's universe on its own
-- carrier: identified decodings name one point, and the decoding carries
-- that identification back.

module _
  {ℓ : Level} {γ : Desc {s = ℓ} (Set ℓ)} (M : Algebra ℓ γ) (law : Law M)
  (unique :
    (X : Set ℓ) → is-proposition (Specification.Name (Algebra.value M) X))
  where

  universe-of : Universe ℓ γ
  universe-of = record
    { Code = Algebra.K M
    ; El = Algebra.value M
    ; intro = Algebra.operation M
    ; intro-β = law
    ; ua = names M unique
    ; ua-β = names-β M unique
    }

  -- Its introductions are M, literally.
  introductions-of-universe : Universes.algebra universe-of ＝ M
  introductions-of-universe = refl

------------------------------------------------------------------------
-- Shulman's universes of every description

universes : {ℓ : Level} → Univalent-Smallness ℓ →
  (γ : Desc {s = ℓ} (Set ℓ)) → Universe ℓ γ
universes small γ =
  universe-of (Univalent-Smallness.algebra small γ)
    (Univalent-Smallness.law small γ) (Univalent-Smallness.unique small γ)

smallness-of-universes : {ℓ : Level} →
  ((γ : Desc {s = ℓ} (Set ℓ)) → Universe ℓ γ) → Univalent-Smallness ℓ
smallness-of-universes U = record
  { algebra = λ γ → Universes.algebra (U γ)
  ; law = λ γ → Universes.law (U γ)
  ; unique = λ γ → fibers (U γ)
  }

------------------------------------------------------------------------
-- The Mahlo rule with unique names

-- A closure from smallness interprets by the algebra's value, and a
-- reflected algebra decodes by its closure's interpretation, so unique
-- names pass both ways with no step.

reflector-of-smallness : {ℓ : Level} →
  ((X : Set ℓ) → FunExt X (λ _ → Set ℓ)) → Univalent-Smallness ℓ →
  Reflector ℓ
reflector-of-smallness extensionality small = record
  { mahlo = mahlo extensionality (forget small)
  ; unique = λ Ψ → Univalent-Smallness.unique small (description Ψ)
  }

smallness-of-reflector : {ℓ : Level} → Reflector ℓ → Univalent-Smallness ℓ
smallness-of-reflector R = record
  { algebra = Realization.reflected-algebra (Reflector.mahlo R)
  ; law = Realization.reflected-law (Reflector.mahlo R)
  ; unique = λ γ → Reflector.unique R (Realization.operator γ)
  }

-- The plain smallness under the rule with unique names is Ambient's.
forgetting-names : {ℓ : Level} (R : Reflector ℓ) →
  forget (smallness-of-reflector R) ＝ smallness (Reflector.mahlo R)
forgetting-names R = refl
