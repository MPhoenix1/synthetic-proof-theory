{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Residence.Calibration where

-- Absorption calibrated against Mahlo. The least subclosure makes leastness
-- free once a small closure exists, so absorption asks of a Mahlo family
-- only a name for a small least closure. For a family naming every small
-- type (Inductive.Naming) that name is free: small least closures for every
-- operator give absorption (small-absorbs), Mahlo gives absorption
-- (mahlo-absorbs), and so do small presentations of the generated totals
-- (presented-small, presentations-absorb). For the ambient family of all
-- types of level ℓ, absorption, Mahlo, small least closures for every
-- operator and presentations of every generated total are therefore
-- interderivable (ambient-mahlo-absorbs). None of these derivations uses
-- induction–recursion; it enters only to inhabit them
-- (Inductive.ambient-absorbs).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
import SPT.Mahlo.Ambient as Ambient
open import SPT.Mahlo.Specification using (Operator; Formers; Mahlo)
open import SPT.Mahlo.Residence.Absorption using
  (Small-Least; Absorption; named)
open import SPT.Mahlo.Residence.Inductive using
  (Naming; ambient-naming)
open import SPT.Mahlo.Residence.Presentation using
  (Generated-Presentation; presented-closure)
open import SPT.Mahlo.Residence.Subclosure using
  (subclosure-small; mahlo-small)

------------------------------------------------------------------------
-- Families naming every small type

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  where

  small-absorbs :
      (Q : Formers C D)
      (ν : Level)
    → Naming D
    → ((Ψ : Operator D) → Small-Least Q Ψ ν)
    → Absorption Q ν
  small-absorbs Q ν names small = record
    { absorb = λ Ψ →
        named (small Ψ)
          ( pr₁ (names (Small-Least.carrier (small Ψ))))
          ( pr₂ (names (Small-Least.carrier (small Ψ))))
    }

  mahlo-absorbs :
      (Q : Formers C D)
      (ν : Level)
    → Naming D
    → Mahlo Q
    → Absorption Q ν
  mahlo-absorbs Q ν names mahlo =
    small-absorbs Q ν names (λ Ψ → mahlo-small mahlo Ψ ν)

  -- A presentation carries a closure, and its least subclosure is a small
  -- least closure.
  presented-small :
      (Q : Formers C D)
      (Ψ : Operator D)
      (extensionality : (X : Set ℓ) → FunExt X (λ _ → C))
    → Generated-Presentation Q Ψ
    → (ν : Level)
    → Small-Least Q Ψ ν
  presented-small Q Ψ extensionality p ν =
    subclosure-small (presented-closure Q Ψ extensionality p) ν

  presentations-absorb :
      (Q : Formers C D)
      (ν : Level)
      (extensionality : (X : Set ℓ) → FunExt X (λ _ → C))
    → Naming D
    → ((Ψ : Operator D) → Generated-Presentation Q Ψ)
    → Absorption Q ν
  presentations-absorb Q ν extensionality names presentations =
    small-absorbs Q ν names
      ( λ Ψ → presented-small Q Ψ extensionality (presentations Ψ) ν)

------------------------------------------------------------------------
-- The ambient family

-- Mathematical shape: Mahlo(Set ℓ) ⇒ Absorption(Set ℓ); the converse is
-- Absorption.mahlo.

ambient-mahlo-absorbs :
    (ℓ ν : Level)
  → Mahlo (Ambient.formers ℓ)
  → Absorption (Ambient.formers ℓ) ν
ambient-mahlo-absorbs ℓ ν mahlo =
  mahlo-absorbs (Ambient.formers ℓ) ν (ambient-naming ℓ) mahlo
