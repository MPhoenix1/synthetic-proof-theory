{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Polynomial.General where

-- Algebras of general codes (IR.Polynomial.General) from smallness and from
-- the ambient Mahlo rule. A general code with values in types has the
-- rules of its polynomial (`rules`), whose small algebra
-- Polynomial.Smallness gives (`small-algebra`, `mahlo-algebra`); with a
-- polynomial code of the output type at each index it is a scheme with
-- outputs polynomial in types (`outputs`), whose small algebra
-- Polynomial.Outputs gives (`small-outputs`, `mahlo-outputs`).

open import SPT.Base
import SPT.Mahlo.Ambient as Ambient
import SPT.Mahlo.Specification as Specification

open import SPT.IR.Description.Indexed using (General; general)
open import SPT.IR.Polynomial using (Poly; Scheme; Rules; Extensionality)
open import SPT.IR.Polynomial.Algebra using (Algebra)
open import SPT.IR.Polynomial.Outputs using (Outputs)
open import SPT.IR.Smallness using (Smallness)
open import SPT.Mahlo.DS.Ambient using (smallness)
open import SPT.Mahlo.DS.Polynomial.Outputs using (small; reflected)
import SPT.Mahlo.DS.Polynomial.Smallness as Derived

------------------------------------------------------------------------
-- Algebras from smallness and the Mahlo rule

module _
  {ℓ : Level} {I : Set ℓ} (γ : General ℓ (lsuc ℓ) I (λ _ → Set ℓ))
  where

  rules : Rules ℓ
  rules = record { Index = I ; rule = Scheme.rule (general γ) }

  small-algebra :
    Extensionality ℓ (lsuc ℓ) → Smallness ℓ → Algebra (general γ)
  small-algebra extensionality s =
    Derived.algebra extensionality s rules

  mahlo-algebra :
    Extensionality ℓ (lsuc ℓ)
    → Specification.Mahlo (Ambient.formers ℓ) → Algebra (general γ)
  mahlo-algebra extensionality reflections =
    small-algebra extensionality (smallness reflections)

-- With a polynomial code of the output type at each index.

module _
  {ℓ : Level} {I : Set ℓ} {D : I → Set (lsuc ℓ)}
  (γ : General ℓ (lsuc ℓ) I D)
  (form : (i : I) → Poly ℓ (lsuc ℓ) (λ (_ : 𝟙) → Set ℓ) (D i))
  where

  outputs : Outputs ℓ
  outputs = record { underlying = general γ ; form = form }

  small-outputs :
    Extensionality ℓ (lsuc ℓ) → Smallness ℓ → Algebra (general γ)
  small-outputs extensionality s = small extensionality s outputs

  mahlo-outputs :
    Extensionality ℓ (lsuc ℓ)
    → Specification.Mahlo (Ambient.formers ℓ) → Algebra (general γ)
  mahlo-outputs extensionality reflections =
    reflected extensionality reflections outputs
