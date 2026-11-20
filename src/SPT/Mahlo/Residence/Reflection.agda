{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Residence.Reflection where

-- A reflection retains a resident carrier and its interpretation
-- (`resident`). A reflection of a child's own operator, read in the parent,
-- is a reflection there (`compose`, through Subclosure.through), and the
-- resident family of the composite is Families.compose of the two, by
-- computation (`resident-compose`). The operator square is the existing
-- whole-family identity inner-β expressed through Families.image, without a
-- stronger law (`operator-square`).

open import SPT.Base
open import SPT.Mahlo.Decoding using (child-formers)
open import SPT.Mahlo.Specification using
  (Family; Operator; Formers; Decode; map; Closure; Reflection)
import SPT.Mahlo.Residence.Families as Families
open import SPT.Mahlo.Residence.Families using (Resident; image)
open import SPT.Mahlo.Residence.Subclosure using (through)

------------------------------------------------------------------------
-- The interpreted family and the returned operator

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  {Q : Formers C D} {Ψ : Operator D} {A : Set ℓ}
  where

  map-image : (L : Closure Q Ψ A) (F : Family (Decode D (Closure.interpret L)))
    → map D (Closure.interpret L) F ＝ image D (Closure.interpret L) F
  map-image L (a , b) = refl

  operator-square : (L : Closure Q Ψ A)
    (F : Family (Decode D (Closure.interpret L)))
    → image D (Closure.interpret L) (Closure.inner L F)
      ＝ Ψ (image D (Closure.interpret L) F)
  operator-square L F =
    map-image L (Closure.inner L F) ⁻¹
    ∙ (Closure.inner-β L F ∙ ap Ψ (map-image L F))

------------------------------------------------------------------------
-- Retaining the actual resident return

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  {Q : Formers C D} {Ψ : Operator D}
  where

  resident : Reflection Q Ψ → Resident D
  resident r = record
    { name = Reflection.carrier r
    ; interpret = Closure.interpret (Reflection.closure r)
    }

------------------------------------------------------------------------
-- A reflection of the returned inner operator, read in the original parent

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  {Q : Formers C D} {Ψ : Operator D}
  where

  compose : (r : Reflection Q Ψ)
    → Reflection
        (child-formers (Reflection.closure r))
        (Closure.inner (Reflection.closure r))
    → Reflection Q Ψ
  compose r s = record
    { carrier = Closure.interpret (Reflection.closure r)
        (Reflection.carrier s)
    ; closure = through (Reflection.closure r) (Reflection.closure s)
    }

  resident-compose : (r : Reflection Q Ψ)
    (s : Reflection
      (child-formers (Reflection.closure r))
      (Closure.inner (Reflection.closure r)))
    → resident (compose r s)
      ＝ Families.compose D (resident r) (resident s)
  resident-compose r s = refl
