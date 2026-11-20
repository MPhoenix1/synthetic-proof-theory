{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Ambient.Initiality where

-- The induction–recursion that the ambient Mahlo rule derives is that of
-- the smallness it gives with no hypothesis (Mahlo.DS.Ambient's
-- `smallness`), so IR's results at smallness hold for it. It is initial
-- among the algebras with their laws (`mahlo-unique`, and its contractible
-- form `mahlo-initial`: IR.Morphism.Initiality's `small-unique` and
-- `small-initial`), and its induction is the only valuation satisfying the
-- computation equations of congruent methods (`mahlo-ind-unique`:
-- IR.Smallness.Initiality's `ind-unique`).

open import SPT.Base
open import SPT.Foundation.Contractible using (is-contractible)
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Induction.Initiality using (Section)
import SPT.Mahlo.Ambient as Ambient
import SPT.Mahlo.Specification as Specification

open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.IR.Description using (Desc)
import SPT.IR.Generated as Generated
import SPT.IR.Generated.Initiality as Initiality
open import SPT.IR.Morphism using (Morphism)
open import SPT.IR.Morphism.Initiality using
  (generated; generated-fold; small-unique; small-initial)
import SPT.IR.Polynomial as Polynomial
open import SPT.IR.Smallness using (Smallness; G; Method; ind)
open import SPT.IR.Smallness.Initiality using (ind-unique)
open import SPT.Mahlo.DS.Ambient using (smallness)

------------------------------------------------------------------------
-- Initiality among the algebras with their laws

mahlo-unique :
  {ℓ κ′ : Level} (reflections : Specification.Mahlo (Ambient.formers ℓ))
  (γ : Desc {s = ℓ} (Set ℓ))
  (extensionality : (A : Set ℓ) → FunExt A (λ _ → Set ℓ))
  (positions : Polynomial.Extensionality ℓ ℓ)
  (motive : (A : Set ℓ) (B : A → Set (κ′ ⊔ lsuc ℓ)) → FunExt A B)
  (N : Algebra κ′ γ) (law′ : Law N)
  ( h :
      Morphism extensionality
        (generated (Smallness.algebra (smallness reflections) γ)) N
        ( Generated.make-β (Smallness.algebra (smallness reflections) γ)
            (Smallness.law (smallness reflections) γ))
        law′)
  (g : Generated.G (Smallness.algebra (smallness reflections) γ))
  → Section.valuation
      ( generated-fold extensionality positions motive
          (Smallness.algebra (smallness reflections) γ)
          (Smallness.law (smallness reflections) γ) N law′)
      g
    ＝ Section.valuation h g
mahlo-unique reflections = small-unique (smallness reflections)

mahlo-initial :
  {ℓ κ′ : Level} (reflections : Specification.Mahlo (Ambient.formers ℓ))
  (γ : Desc {s = ℓ} (Set ℓ))
  (extensionality : (A : Set ℓ) → FunExt A (λ _ → Set ℓ))
  (positions : Polynomial.Extensionality ℓ ℓ)
  (motive : (A : Set ℓ) (B : A → Set (κ′ ⊔ lsuc ℓ)) → FunExt A B)
  (N : Algebra κ′ γ) (law′ : Law N)
  → is-contractible
      (Morphism extensionality
        (generated (Smallness.algebra (smallness reflections) γ)) N
        ( Generated.make-β (Smallness.algebra (smallness reflections) γ)
            (Smallness.law (smallness reflections) γ))
        law′)
mahlo-initial reflections = small-initial (smallness reflections)

------------------------------------------------------------------------
-- Uniqueness of induction

mahlo-ind-unique :
  {ℓ ν : Level} (reflections : Specification.Mahlo (Ambient.formers ℓ))
  (γ : Desc {s = ℓ} (Set ℓ)) (P : G (smallness reflections) γ → Set ν)
  (v : (g : G (smallness reflections) γ) → P g)
  (m : Method (smallness reflections) γ P)
  → Initiality.Congruent (Smallness.algebra (smallness reflections) γ) P m
  → Initiality.Homomorphic
      (Smallness.algebra (smallness reflections) γ) P v m
  → (g : G (smallness reflections) γ)
  → v g ＝ ind (smallness reflections) γ P m g
mahlo-ind-unique reflections γ P = ind-unique (smallness reflections) γ P
