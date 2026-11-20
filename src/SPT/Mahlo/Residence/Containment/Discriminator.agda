{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Residence.Containment.Discriminator where

-- Leastness is necessary for containment. Every closure is also a
-- closure of the identity operator (identity-closure). In the ambient
-- universe, beyond names the least identity closure, and wider is the
-- resulting larger reflection of the identity. The least reflection
-- lies inside wider (contained), but the reverse containment fails
-- (not-inside): wider names the least carrier, which cannot name itself.

open import SPT.Base
open import SPT.Mahlo.Specification using
  (Operator; Formers; Closure; Reflection; Name)
open import SPT.Mahlo.Decoding using (DecodingLaws)
open import SPT.Mahlo.Generation using (Branch-Extensionality; unnamed)
open import SPT.Mahlo.Residence.Absorption using (Absorbed; Absorption)
open import SPT.Mahlo.Residence.Inductive using (ambient-absorbs)
open import SPT.Mahlo.Residence.Containment using (inside)
import SPT.Mahlo.Ambient as Ambient
import SPT.Mahlo.Relative as Relative

------------------------------------------------------------------------
-- Every closure is one for the identity operator

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D}
  {Ψ : Operator D} {A : Set ℓ} where

  identity-closure : Closure Q Ψ A → Closure Q id A
  identity-closure L = record
    { interpret = Closure.interpret L
    ; empty = Closure.empty L
    ; unit = Closure.unit L
    ; two = Closure.two L
    ; natural = Closure.natural L
    ; product = Closure.product L
    ; sum = Closure.sum L
    ; tree = Closure.tree L
    ; identity = Closure.identity L
    ; inner = id
    ; inner-β = λ φ → refl
    }

------------------------------------------------------------------------
-- A reflection beyond the least one

module _ (ℓ : Level) where

  beyond : Ambient.Operator ℓ
  beyond φ = Relative.Generated (Ambient.formers ℓ) id , (λ _ → Lift ℓ 𝟙)

  wider : Reflection (Ambient.formers ℓ) id
  wider = record
    { carrier = Relative.Generated (Ambient.formers ℓ) beyond
    ; closure = identity-closure (Relative.closure (Ambient.formers ℓ) beyond)
    }

  contained : Branch-Extensionality (λ (X : Set ℓ) → X) →
    (x : Relative.Generated (Ambient.formers ℓ) id) →
    Name (Relative.interpret (Ambient.formers ℓ) beyond)
      (Relative.interpret (Ambient.formers ℓ) id x)
  contained ext =
    inside (Absorption.absorb (ambient-absorbs ℓ (lsuc ℓ)) id) wider ext

  not-inside : ¬ ((x : Relative.Generated (Ambient.formers ℓ) beyond) →
    Name (Relative.interpret (Ambient.formers ℓ) id)
      (Relative.interpret (Ambient.formers ℓ) beyond x))
  not-inside within = unnamed (DecodingLaws.tree-β (Ambient.laws ℓ))
    (Absorbed.reflection (Absorption.absorb (ambient-absorbs ℓ (lsuc ℓ)) id))
    (within (Relative.result Relative.unit (λ _ → Relative.unit)))
