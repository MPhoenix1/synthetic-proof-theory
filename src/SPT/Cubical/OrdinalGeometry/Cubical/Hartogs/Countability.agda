{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Countability where

-- Countability by partial enumeration compared with mere embedding into ℕ.
-- A discrete type with a partial enumeration embeds into ℕ; an embedding
-- with decidable range gives a partial enumeration; under excluded middle,
-- for sets, the two notions coincide.

open import Agda.Primitive using (Level; lsuc)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Properties as MaybeProperties
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_)

import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Countability
  as Countability
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Woset
  as WosetPresentation

import Cubical.Data.Empty as CubicalEmpty
import Cubical.Data.Equality.Conversion as EqualityConversion
import Cubical.Data.Nat.Order.Recursive as NatOrder
import Cubical.Data.Nat.Properties as NatProperties
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.Prelude as Cubical
import Cubical.Functions.Embedding as Embedding
import Cubical.HITs.PropositionalTruncation as Truncation
import Cubical.Relation.Nullary as Nullary

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- Excluded middle and embeddings into ℕ

-- Excluded middle at level ℓ, as a hypothesis:
--
--   ExcludedMiddle(ℓ) = Π(P : Set ℓ). isProp(P) → Dec(P).

ExcludedMiddle : (level : Level) → Set (lsuc level)
ExcludedMiddle level =
  (proposition : Set level) →
  Cubical.isProp proposition →
  Nullary.Dec proposition

-- MerelyEmbedsInNat(A) = ‖A ↪ ℕ‖.

MerelyEmbedsInNat : ∀ {level} → Set level → Set level
MerelyEmbedsInNat A = Truncation.∥ Embedding._↪_ A ℕ ∥₁

isPropMerelyEmbedsInNat :
    {A : Set ℓ}
  → Cubical.isProp (MerelyEmbedsInNat A)
isPropMerelyEmbedsInNat = Truncation.isPropPropTrunc

-- Excluded middle makes a set discrete.

discreteFromExcludedMiddle :
    {A : Set ℓ}
  → ExcludedMiddle ℓ
  → Cubical.isSet A
  → Nullary.Discrete A
discreteFromExcludedMiddle excluded-middle setA left right =
  excluded-middle (left Cubical.≡ right) (setA left right)

------------------------------------------------------------------------
-- From partial enumerations to embeddings

private
  selectedEnumerationHit :
      {A : Set ℓ}
    → Nullary.Discrete A
    → (enumeration : Countability.PartialEnumeration A)
    → (point : A)
    → Σ ℕ (λ index →
        Countability.sequence enumeration index Cubical.≡ just point)
  selectedEnumerationHit discreteA enumeration point =
    Nullary.Collapsible→SplitSupport
      (NatOrder.Decidable→Collapsible
        (λ index →
          Nullary.Discrete→isSet
            (WosetPresentation.discreteMaybe discreteA)
            (Countability.sequence enumeration index)
            (just point))
        (λ index →
          WosetPresentation.discreteMaybe discreteA
            (Countability.sequence enumeration index)
            (just point)))
      (Countability.covers enumeration point)

  partialEnumerationCode :
      {A : Set ℓ}
    → Nullary.Discrete A
    → Countability.PartialEnumeration A
    → A → ℕ
  partialEnumerationCode discreteA enumeration point =
    Cubical.fst (selectedEnumerationHit discreteA enumeration point)

  partialEnumerationCode-injective :
      {A : Set ℓ}
    → (discreteA : Nullary.Discrete A)
    → (enumeration : Countability.PartialEnumeration A)
    → {left right : A}
    → partialEnumerationCode discreteA enumeration left
        Cubical.≡
      partialEnumerationCode discreteA enumeration right
    → left Cubical.≡ right
  partialEnumerationCode-injective
      discreteA enumeration {left} {right} code-path =
    EqualityConversion.eqToPath
      (MaybeProperties.just-injective
        (EqualityConversion.pathToEq
          (Cubical._∙_
            (Cubical.sym left-hit)
            (Cubical._∙_
              (Cubical.cong
                (Countability.sequence enumeration)
                code-path)
              right-hit))))
    where
      left-hit :
        Countability.sequence enumeration
          (partialEnumerationCode discreteA enumeration left)
          Cubical.≡ just left
      left-hit =
        Cubical.snd (selectedEnumerationHit discreteA enumeration left)

      right-hit :
        Countability.sequence enumeration
          (partialEnumerationCode discreteA enumeration right)
          Cubical.≡ just right
      right-hit =
        Cubical.snd (selectedEnumerationHit discreteA enumeration right)

-- Discrete(A) → PartialEnumeration(A) → (A ↪ ℕ): a point goes to the least
-- index at which it is enumerated, found by deciding equality.

enumeration→embedding :
    {A : Set ℓ}
  → Nullary.Discrete A
  → Countability.PartialEnumeration A
  → Embedding._↪_ A ℕ
enumeration→embedding discreteA enumeration =
  partialEnumerationCode discreteA enumeration
  , Embedding.injEmbedding
      NatProperties.isSetℕ
      (partialEnumerationCode-injective discreteA enumeration)

------------------------------------------------------------------------
-- From embeddings to partial enumerations

-- Decidability of the range of an embedding f : A ↪ ℕ,
--
--   RangeDecidable(f) = Π(n : ℕ). Dec(Σ(a : A). f(a) = n).

RangeDecidable :
    {A : Set ℓ}
  → Embedding._↪_ A ℕ
  → Set ℓ
RangeDecidable embedding =
  (index : ℕ) →
  Nullary.Dec (Equiv.fiber (Cubical.fst embedding) index)

private
  fiberDecisionToMaybe :
      {A : Set ℓ}
    → (embedding : Embedding._↪_ A ℕ)
    → (index : ℕ)
    → Nullary.Dec (Equiv.fiber (Cubical.fst embedding) index)
    → Maybe A
  fiberDecisionToMaybe embedding index
      (Nullary.yes (point , _)) = just point
  fiberDecisionToMaybe embedding index (Nullary.no _) = nothing

  fiberDecisionToMaybe-hits :
      {A : Set ℓ}
    → (embedding : Embedding._↪_ A ℕ)
    → (index : ℕ)
    → (decision :
        Nullary.Dec (Equiv.fiber (Cubical.fst embedding) index))
    → (point : A)
    → Cubical.fst embedding point Cubical.≡ index
    → fiberDecisionToMaybe embedding index decision
        Cubical.≡ just point
  fiberDecisionToMaybe-hits embedding index
      (Nullary.yes (representative , same-index)) point point-index =
    Cubical.cong just
      (Embedding.isEmbedding→Inj
        (Cubical.snd embedding)
        representative point
        (Cubical._∙_ same-index (Cubical.sym point-index)))
  fiberDecisionToMaybe-hits embedding index
      (Nullary.no misses) point point-index =
    CubicalEmpty.rec (misses (point , point-index))

-- An embedding with decidable range gives a partial enumeration: at n it
-- returns the point over n, if there is one.

embedding→enumeration :
    {A : Set ℓ}
  → (embedding : Embedding._↪_ A ℕ)
  → RangeDecidable embedding
  → Countability.PartialEnumeration A
embedding→enumeration embedding decide = record
  { sequence = λ index →
      fiberDecisionToMaybe embedding index (decide index)
  ; covers = λ point →
      Truncation.∣
        Cubical.fst embedding point
        , fiberDecisionToMaybe-hits
            embedding
            (Cubical.fst embedding point)
            (decide (Cubical.fst embedding point))
            point
            Cubical.refl
      ∣₁
  }

excludedMiddle→rangeDecidable :
    {A : Set ℓ}
  → ExcludedMiddle ℓ
  → (embedding : Embedding._↪_ A ℕ)
  → RangeDecidable embedding
excludedMiddle→rangeDecidable excluded-middle embedding index =
  excluded-middle
    (Equiv.fiber (Cubical.fst embedding) index)
    (Embedding.isEmbedding→hasPropFibers
      (Cubical.snd embedding) index)

------------------------------------------------------------------------
-- The comparison under excluded middle

countable→embeds :
    {A : Set ℓ}
  → ExcludedMiddle ℓ
  → Cubical.isSet A
  → Countability.IsCountable A
  → MerelyEmbedsInNat A
countable→embeds excluded-middle setA =
  Truncation.rec
    isPropMerelyEmbedsInNat
    (λ enumeration →
      Truncation.∣
        enumeration→embedding
          (discreteFromExcludedMiddle excluded-middle setA)
          enumeration
      ∣₁)

embeds→countable :
    {A : Set ℓ}
  → ExcludedMiddle ℓ
  → MerelyEmbedsInNat A
  → Countability.IsCountable A
embeds→countable excluded-middle =
  Truncation.rec
    Countability.isPropIsCountable
    (λ embedding →
      Truncation.∣
        embedding→enumeration embedding
          (excludedMiddle→rangeDecidable
            excluded-middle embedding)
      ∣₁)

-- ExcludedMiddle(ℓ) → isSet(A) → (IsCountable(A) ≃ ‖A ↪ ℕ‖).

countable≃embeds :
    {A : Set ℓ}
  → ExcludedMiddle ℓ
  → Cubical.isSet A
  → Countability.IsCountable A Equiv.≃ MerelyEmbedsInNat A
countable≃embeds excluded-middle setA =
  Equiv.propBiimpl→Equiv
    Countability.isPropIsCountable
    isPropMerelyEmbedsInNat
    (countable→embeds excluded-middle setA)
    (embeds→countable excluded-middle)
