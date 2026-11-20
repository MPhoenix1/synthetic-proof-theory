{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Degree where

-- Degrees of Mahlo reflection for a reflector with decoding laws. A child the
-- reflector returns, given a reflector of its own, is again a Mahlo reflection,
-- with the decoding laws every reflected child inherits (`child-reflection`).
-- Degree n + 1 asks that every child returned carry a reflector of its own of
-- degree n (`Degree`):
--
--   Degree 0 M = 𝟙,
--   Degree (n + 1) M = Π (Ψ : Operator D). Σ (c : Mahlo (child M Ψ)).
--                        Degree n (child M Ψ reflected by c).
--
-- `mahlo`, `child` and `next` read off the reflector, the reflected child
-- and the degree remaining there; a reflector of degree n + 1 has degree n
-- (`lower-degree`).

open import SPT.Base
open import SPT.Mahlo.Specification using
  (Operator; Formers; Reflection; Mahlo)
open import SPT.Mahlo.Decoding using
  (MahloReflection; reflect; child-formers; reflected-decoding)

------------------------------------------------------------------------
-- Degrees of reflection

-- A returned child, with a reflector of its own, as a Mahlo reflection. Its
-- decoding laws are those every reflected child inherits.
child-reflection : {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  {Q : Formers C D} (M : MahloReflection Q) (Ψ : Operator D) →
  Mahlo (child-formers (Reflection.closure (reflect M Ψ))) →
  MahloReflection (child-formers (Reflection.closure (reflect M Ψ)))
child-reflection M Ψ c = record
  { codeReflection = c
  ; decoding = reflected-decoding M Ψ
  }

Degree : ℕ → {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D} →
  MahloReflection Q → Set (κ ⊔ lsuc ℓ)
Degree zero {κ} {ℓ} M = Lift (κ ⊔ lsuc ℓ) 𝟙
Degree (suc n) {κ} {ℓ} {C} {D} M = (Ψ : Operator D) →
  Σ (Mahlo (child-formers (Reflection.closure (reflect M Ψ))))
    (λ c → Degree n (child-reflection M Ψ c))

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D} where

  -- Each returned child's reflector, its Mahlo reflection, and the degree
  -- remaining at that child.
  mahlo : (M : MahloReflection Q) (n : ℕ) → Degree (suc n) M →
    (Ψ : Operator D) → Mahlo (child-formers (Reflection.closure (reflect M Ψ)))
  mahlo M n R Ψ = pr₁ (R Ψ)

  child : (M : MahloReflection Q) (n : ℕ) → Degree (suc n) M →
    (Ψ : Operator D) →
    MahloReflection (child-formers (Reflection.closure (reflect M Ψ)))
  child M n R Ψ = child-reflection M Ψ (mahlo M n R Ψ)

  next : (M : MahloReflection Q) (n : ℕ) (R : Degree (suc n) M)
    (Ψ : Operator D) → Degree n (child M n R Ψ)
  next M n R Ψ = pr₂ (R Ψ)

-- A reflector of degree n + 1 also has degree n.
lower-degree : {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D}
  (M : MahloReflection Q) (n : ℕ) → Degree (suc n) M → Degree n M
lower-degree M zero R = lift ⋆
lower-degree M (suc n) R Ψ =
  mahlo M (suc n) R Ψ ,
  lower-degree (child M (suc n) R Ψ) n (next M (suc n) R Ψ)
