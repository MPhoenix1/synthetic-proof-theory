{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Countability where

-- Countability as the mere existence of a partial enumeration, its
-- invariance under equivalence, and countability of every order type
-- ord(P).

open import Agda.Primitive using (Level)
open import Data.Maybe using (Maybe; just)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_)
import Relation.Binary.PropositionalEquality as InductiveEquality

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType as Reflection

import Cubical.Data.Equality.Conversion as EqualityConversion
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.Prelude as Cubical
import Cubical.HITs.PropositionalTruncation as Truncation
import Cubical.HITs.SetQuotients as Quotient

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- Partial enumerations

-- A partial enumeration of A: a sequence ℕ → Maybe A that merely hits
-- every point,
--
--   PartialEnumeration(A) = Σ(e : ℕ → Maybe A). Π a. ‖Σ n. e(n) = just(a)‖.
--
-- Empty and finite types are admitted.

record PartialEnumeration {level : Level} (A : Set level) : Set level where
  field
    sequence : ℕ → Maybe A
    covers :
      (point : A) →
      Truncation.∥
        Σ ℕ (λ index → sequence index Cubical.≡ just point)
      ∥₁

open PartialEnumeration public

-- IsCountable(A) = ‖PartialEnumeration(A)‖.  Its comparison with mere
-- injections into ℕ is in Hartogs.Countability.

IsCountable : ∀ {level} → Set level → Set level
IsCountable A = Truncation.∥ PartialEnumeration A ∥₁

isPropIsCountable :
    {A : Set ℓ}
  → Cubical.isProp (IsCountable A)
isPropIsCountable = Truncation.isPropPropTrunc

------------------------------------------------------------------------
-- Invariance under equivalence

-- (A ≃ B) → PartialEnumeration(A) → PartialEnumeration(B): map the
-- sequence forward, and cover b through its preimage.

partialEnumeration-respects-equivalence :
    ∀ {level-left level-right}
      {A : Set level-left}
      {B : Set level-right}
  → Equiv._≃_ A B
  → PartialEnumeration A
  → PartialEnumeration B
partialEnumeration-respects-equivalence equivalence enumeration = record
  { sequence = λ index →
      Maybe.map
        (Equiv.equivFun equivalence)
        (sequence enumeration index)
  ; covers = λ point →
      Truncation.map
        (λ hit →
          Cubical.fst hit
          , Cubical._∙_
              (Cubical.cong
                (Maybe.map (Equiv.equivFun equivalence))
                (Cubical.snd hit))
              (Cubical.cong just (Equiv.secEq equivalence point)))
        (covers enumeration (Equiv.invEq equivalence point))
  }

-- (A ≃ B) → IsCountable(A) → IsCountable(B).

isCountable-respects-equivalence :
    ∀ {level-left level-right}
      {A : Set level-left}
      {B : Set level-right}
  → Equiv._≃_ A B
  → IsCountable A
  → IsCountable B
isCountable-respects-equivalence equivalence =
  Truncation.map (partialEnumeration-respects-equivalence equivalence)

------------------------------------------------------------------------
-- The enumeration of P descends to classes

classSequence :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
  → ℕ → Maybe (Reflection.Class presentation)
classSequence presentation index =
  Maybe.map
    (λ point → Quotient.[ point ])
    (Presented.CountableOrdinal𝒫.enum presentation index)

private
  classSequence-covers :
      (presentation : Presented.CountableOrdinal𝒫 ℓ)
      (point : Presented.CountableOrdinal𝒫.X presentation)
    → Truncation.∥
        Σ ℕ (λ index →
          classSequence presentation index
            Cubical.≡ just (Quotient.[ point ]))
      ∥₁
  classSequence-covers presentation point
      with Presented.CountableOrdinal𝒫.covers presentation point
  ... | index , representative , selected , representative≈point =
    Truncation.∣
      index
      , Cubical._∙_
          (EqualityConversion.eqToPath
            (InductiveEquality.cong
              (Maybe.map (λ entry → Quotient.[ entry ]))
              selected))
          (Cubical.cong just
            (Quotient.eq/
              {R = Presented.CountableOrdinal𝒫._≈_ presentation}
              representative point representative≈point))
    ∣₁

classEnumeration :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
  → PartialEnumeration (Reflection.Class presentation)
classEnumeration presentation = record
  { sequence = classSequence presentation
  ; covers =
      Quotient.elimProp
        (λ _ → Truncation.isPropPropTrunc)
        (classSequence-covers presentation)
  }

-- Every order type ord(P) has a countable carrier, through the
-- enumeration of P.

orderType-countable :
    (presentation : Presented.CountableOrdinal𝒫 ℓ)
  → IsCountable (Cubical.fst (Reflection.orderType presentation))
orderType-countable presentation =
  Truncation.∣ classEnumeration presentation ∣₁
