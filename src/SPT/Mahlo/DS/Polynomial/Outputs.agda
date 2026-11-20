{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Polynomial.Outputs where

-- Small algebras of schemes with outputs polynomial in types
-- (IR.Polynomial.Outputs), from smallness and from a Mahlo reflection: a
-- small algebra of the scheme's type-valued rules (`types`), which
-- Polynomial.Smallness or Polynomial.Realization gives, is one of the
-- scheme on structured codes (`small`, `reflected`), under extensionality
-- for families of information over the arities.

open import SPT.Base
import SPT.Mahlo.Ambient as Ambient
import SPT.Mahlo.Specification as Specification

open import SPT.IR.Polynomial using (Extensionality)
open import SPT.IR.Polynomial.Algebra using (Algebra)
open import SPT.IR.Polynomial.Outputs using (Outputs; types; algebra)
open import SPT.IR.Smallness using (Smallness)
import SPT.Mahlo.DS.Polynomial.Realization as Realization
import SPT.Mahlo.DS.Polynomial.Smallness as Derived

------------------------------------------------------------------------
-- From smallness and from a Mahlo reflection

small :
  {ℓ : Level} → Extensionality ℓ (lsuc ℓ) → Smallness ℓ → (o : Outputs ℓ)
  → Algebra (Outputs.underlying o)
small extensionality smallness o =
  algebra (Outputs.underlying o) (Outputs.form o) extensionality
    (Derived.algebra extensionality smallness
      (types (Outputs.underlying o) (Outputs.form o)))

reflected :
  {ℓ : Level} → Extensionality ℓ (lsuc ℓ)
  → Specification.Mahlo (Ambient.formers ℓ) → (o : Outputs ℓ)
  → Algebra (Outputs.underlying o)
reflected extensionality reflections o =
  algebra (Outputs.underlying o) (Outputs.form o) extensionality
    (Realization.reflected extensionality reflections
      (types (Outputs.underlying o) (Outputs.form o)))
