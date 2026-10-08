{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Uniqueness where

-- Uniqueness of addition, multiplication and exponentiation with base ω
-- (Kraus, Nordvall Forsberg and Xu, Theorems 28 and 42), for hereditarily
-- classified arguments.
--
-- IsAddition, IsMultiplication and IsExponential are the specifications
-- of Definitions 12–14, read with ≃𝒫: the zero, successor and limit laws
-- for every zero, successor and limit. P + Q, P · Q and ω^P satisfy them.
-- Any operation satisfying one agrees with ours up to ≃𝒫 at every
-- hereditary argument, by classifiability induction: the zero and
-- successor cases by the laws, the limit case because both are suprema of
-- pointwise equivalent families. Multiplication respects ≃𝒫 on the left
-- at hereditary right arguments, which the successor case of ω^ uses at ω.

open import Agda.Primitive using (Level; lsuc)
open import Data.Nat using (ℕ)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
open import SPT.Cubical.OrdinalGeometry.Presentation.Sum using (_+_)
import SPT.Cubical.OrdinalGeometry.Presentation.Limit as Limit
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization using
  (Zero; Successor; Strong; module Successors; Supremum; module Suprema;
   Increasing)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Addition as Addition
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Multiplication using (_·_)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Multiplication as Multiplication
open import SPT.Cubical.OrdinalGeometry.Operation.Exponential using (exp)
import SPT.Cubical.OrdinalGeometry.Operation.Exponential
  as GeneratedExponential
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Exponential using (omega)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Exponential as Exponential
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Successor using (respect)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Classification.Induction
  using
  (Hereditary; induction; omega-hereditary)

private
  variable
    ℓ : Level

  -- A supremum of a family is a supremum of every pointwise equivalent
  -- family.
  family : {F G : ℕ → 𝒫 ℓ} {S : 𝒫 ℓ}
    → ((n : ℕ) → F n Presented.≃𝒫 G n) → Supremum F S → Supremum G S
  family e sup = record
    { member = λ n →
        Maps.compose (Maps.equivalence (Presented.≃𝒫-sym (e n)))
          (Supremum.member sup n)
    ; least = λ X g → Supremum.least sup X λ n →
        Maps.compose (Maps.equivalence (e n)) (g n)
    }

  _∙_ : {P Q R : 𝒫 ℓ}
    → P Presented.≃𝒫 Q → Q Presented.≃𝒫 R → P Presented.≃𝒫 R
  _∙_ = Presented.≃𝒫-trans

  infixr 5 _∙_

------------------------------------------------------------------------
-- The specifications

-- Definition 12, with ≃𝒫.
record IsAddition {ℓ : Level} (_⊕_ : 𝒫 ℓ → 𝒫 ℓ → 𝒫 ℓ) : Set (lsuc ℓ) where
  field
    zero-law : (P Z : 𝒫 ℓ) → Zero Z → (P ⊕ Z) Presented.≃𝒫 P
    successor-law : (P : 𝒫 ℓ) {Q R : 𝒫 ℓ} → Successor Q R
      → {D : 𝒫 ℓ} → Successor (P ⊕ Q) D → (P ⊕ R) Presented.≃𝒫 D
    limit-law : (P : 𝒫 ℓ) (s : Increasing ℓ) {A B : 𝒫 ℓ}
      → Supremum (Increasing.stage s) A
      → Supremum (λ n → P ⊕ Increasing.stage s n) B
      → (P ⊕ A) Presented.≃𝒫 B

-- Definition 13, with ≃𝒫.
record IsMultiplication {ℓ : Level} (_⊙_ : 𝒫 ℓ → 𝒫 ℓ → 𝒫 ℓ)
  : Set (lsuc ℓ) where
  field
    zero-law : (P Z : 𝒫 ℓ) → Zero Z → (P ⊙ Z) Presented.≃𝒫 Z
    successor-law : (P : 𝒫 ℓ) {Q S : 𝒫 ℓ} → Successor Q S
      → (P ⊙ S) Presented.≃𝒫 ((P ⊙ Q) + P)
    limit-law : (P : 𝒫 ℓ) (s : Increasing ℓ) {A B : 𝒫 ℓ}
      → Supremum (Increasing.stage s) A
      → Supremum (λ n → P ⊙ Increasing.stage s n) B
      → (P ⊙ A) Presented.≃𝒫 B

-- Definition 14 with base ω, with ≃𝒫.
record IsExponential {ℓ : Level} (e : 𝒫 ℓ → 𝒫 ℓ) : Set (lsuc ℓ) where
  field
    zero-law : (Z : 𝒫 ℓ) → Zero Z → {S : 𝒫 ℓ} → Successor Z S
      → e Z Presented.≃𝒫 S
    successor-law : {P S : 𝒫 ℓ} → Successor P S
      → e S Presented.≃𝒫 (e P · omega)
    limit-law : (s : Increasing ℓ) {A D : 𝒫 ℓ}
      → Supremum (Increasing.stage s) A
      → Supremum (λ n → e (Increasing.stage s n)) D
      → e A Presented.≃𝒫 D

addition : IsAddition {ℓ} _+_
addition = record
  { zero-law = λ P Z z → Addition.zero-law {P = P} Z z
  ; successor-law = λ P s d → Addition.successor-law {P = P} s d
  ; limit-law = λ P s a b → Addition.limit-law {P = P} s a b
  }

multiplication : IsMultiplication {ℓ} _·_
multiplication = record
  { zero-law = Multiplication.zero-law
  ; successor-law = λ P s → Multiplication.successor-law P s
  ; limit-law = Multiplication.limit-law
  }

exponential : IsExponential {ℓ} exp
exponential = record
  { zero-law = λ Z z s → Exponential.zero-law Z z s
  ; successor-law = Exponential.successor-law
  ; limit-law = Exponential.limit-law
  }

------------------------------------------------------------------------
-- Uniqueness

-- Mathematical shape: IsAddition ⊕ → H Q → P ⊕ Q ≃ P + Q.
unique-addition : {_⊕_ : 𝒫 ℓ → 𝒫 ℓ → 𝒫 ℓ} → IsAddition _⊕_
  → (P : 𝒫 ℓ) {Q : 𝒫 ℓ} → Hereditary Q → (P ⊕ Q) Presented.≃𝒫 (P + Q)
unique-addition {_⊕_ = _⊕_} add P =
  induction (λ Q → (P ⊕ Q) Presented.≃𝒫 (P + Q)) record
    { zero-case = λ {Q} z →
        IsAddition.zero-law add P Q z
          ∙ Presented.≃𝒫-sym (Addition.zero-law {P = P} Q z)
    ; successor-case = λ {Q} {R} st e →
        IsAddition.successor-law add P (Strong.successor st)
          (Strong.successor (Successors.next (P ⊕ R)))
          ∙ respect e
          ∙ Presented.≃𝒫-sym (Addition.successor-law {P = P}
              (Strong.successor st)
              (Strong.successor (Successors.next (P + R))))
    ; limit-case = λ s sup e →
        IsAddition.limit-law add P s sup
          (family (λ n → Presented.≃𝒫-sym (e n)) (bound s))
          ∙ Presented.≃𝒫-sym (Addition.limit-law {P = P} s sup (bound s))
    }
  where
  bound : (s : Increasing _)
    → Supremum (λ n → P + Increasing.stage s n)
        (Limit.completion (Addition.chain P (Increasing.chain s)))
  bound s = Suprema.completion (Addition.chain P (Increasing.chain s))

-- Mathematical shape: IsMultiplication ⊙ → H Q → P ⊙ Q ≃ P · Q.
unique-multiplication : {_⊙_ : 𝒫 ℓ → 𝒫 ℓ → 𝒫 ℓ}
  → IsMultiplication _⊙_
  → (P : 𝒫 ℓ) {Q : 𝒫 ℓ} → Hereditary Q → (P ⊙ Q) Presented.≃𝒫 (P · Q)
unique-multiplication {_⊙_ = _⊙_} mul P =
  induction (λ Q → (P ⊙ Q) Presented.≃𝒫 (P · Q)) record
    { zero-case = λ {Q} z →
        IsMultiplication.zero-law mul P Q z
          ∙ Presented.≃𝒫-sym (Multiplication.zero-law P Q z)
    ; successor-case = λ {Q} {R} st e →
        IsMultiplication.successor-law mul P (Strong.successor st)
          ∙ Addition.equivalence e (Presented.≃𝒫-refl P)
          ∙ Presented.≃𝒫-sym
              (Multiplication.successor-law P (Strong.successor st))
    ; limit-case = λ s sup e →
        IsMultiplication.limit-law mul P s sup
          (family (λ n → Presented.≃𝒫-sym (e n)) (bound s))
          ∙ Presented.≃𝒫-sym (Multiplication.limit-law P s sup (bound s))
    }
  where
  bound : (s : Increasing _)
    → Supremum (λ n → P · Increasing.stage s n)
        (Limit.completion (Multiplication.chain P (Increasing.chain s)))
  bound s =
    Suprema.completion (Multiplication.chain P (Increasing.chain s))

-- Mathematical shape: P ≃ P′ → H Q → P · Q ≃ P′ · Q.
left : {P P′ : 𝒫 ℓ} → P Presented.≃𝒫 P′
  → {Q : 𝒫 ℓ} → Hereditary Q → (P · Q) Presented.≃𝒫 (P′ · Q)
left {P = P} {P′} e =
  induction (λ Q → (P · Q) Presented.≃𝒫 (P′ · Q)) record
    { zero-case = λ {Q} z →
        Multiplication.zero-law P Q z
          ∙ Presented.≃𝒫-sym (Multiplication.zero-law P′ Q z)
    ; successor-case = λ {Q} st f →
        Multiplication.successor-law P (Strong.successor st)
          ∙ Addition.equivalence f e
          ∙ Presented.≃𝒫-sym
              (Multiplication.successor-law P′ (Strong.successor st))
    ; limit-case = λ s sup f →
        Multiplication.limit-law P s sup (bound P s)
          ∙ Suprema.unique (family f (bound P s)) (bound P′ s)
          ∙ Presented.≃𝒫-sym (Multiplication.limit-law P′ s sup (bound P′ s))
    }
  where
  bound : (X : 𝒫 _) (s : Increasing _)
    → Supremum (λ n → X · Increasing.stage s n)
        (Limit.completion (Multiplication.chain X (Increasing.chain s)))
  bound X s =
    Suprema.completion (Multiplication.chain X (Increasing.chain s))

-- Mathematical shape: IsExponential e → H P → e P ≃ ω^P.
unique-exponential : {e : 𝒫 ℓ → 𝒫 ℓ} → IsExponential e
  → {P : 𝒫 ℓ} → Hereditary P → e P Presented.≃𝒫 exp P
unique-exponential {e = e} ex =
  induction (λ P → e P Presented.≃𝒫 exp P) record
    { zero-case = λ {Z} z →
        IsExponential.zero-law ex Z z next
          ∙ Presented.≃𝒫-sym (Exponential.zero-law Z z next)
    ; successor-case = λ st f →
        IsExponential.successor-law ex (Strong.successor st)
          ∙ left f omega-hereditary
          ∙ Presented.≃𝒫-sym
              (Exponential.successor-law (Strong.successor st))
    ; limit-case = λ s sup f →
        IsExponential.limit-law ex s sup
          (family (λ n → Presented.≃𝒫-sym (f n)) (bound s))
          ∙ Presented.≃𝒫-sym (Exponential.limit-law s sup (bound s))
    }
  where
  next : {Z : 𝒫 _} → Successor Z (Maps.Successor.next Z)
  next {Z} = Strong.successor (Successors.next Z)

  chain : Increasing _ → Limit.Chain _
  chain s = record
    { stage = λ n → exp (Increasing.stage s n)
    ; edge = λ n →
        GeneratedExponential.initial
          (Maps.inclusion (Increasing.step s n))
    }

  bound : (s : Increasing _)
    → Supremum (λ n → exp (Increasing.stage s n))
        (Limit.completion (chain s))
  bound s = Suprema.completion (chain s)
