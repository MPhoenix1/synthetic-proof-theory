{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Child where

-- Small spaces in the child returned by a Mahlo reflection. The parent, its
-- decoding laws and its reflector are fixed before the operator Ψ, and the
-- child's code type is literally the decoding of the returned parent code,
-- D (carrier (reflect M Ψ)). A space of the child is a code with a
-- code-valued map on its decoding (`Mahlo-Space`), the same datum as a
-- family of the child (`to-family`, `from-family`, inverse by refl). The
-- closure's inner family acts on spaces (`action`), and the parent family
-- of the action is Ψ's (`parent-family`, `action-β`). A space decodes to a
-- displayed space (`display`).

open import SPT.Base
open import SPT.Foundation.Spaces using (DΣ)
open import SPT.Mahlo.Decoding using (MahloReflection; reflect)
open import SPT.Mahlo.Specification using
  (Family; Operator; Formers; Decode; map; Closure; Reflection)

------------------------------------------------------------------------
-- Spaces of the reflected child

-- Mathematical shape:
--   Σ (a : D (carrier (reflect M Ψ))).
--     (D (interpret a) → D (carrier (reflect M Ψ))).
-- No independently supplied code-and-decoding package occurs here.

record Mahlo-Space
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D}
  (M : MahloReflection Q) (Ψ : Operator D) : Set ℓ where
  constructor space
  field
    base : D (Reflection.carrier (reflect M Ψ))
    fiber :
      Decode D (Closure.interpret (Reflection.closure (reflect M Ψ))) base
      → D (Reflection.carrier (reflect M Ψ))

open Mahlo-Space public

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D}
  (M : MahloReflection Q) (Ψ : Operator D)
  where

  to-family :
    Mahlo-Space M Ψ
    → Family
        ( Decode D (Closure.interpret (Reflection.closure (reflect M Ψ))))
  to-family X = base X , fiber X

  from-family :
    Family
      ( Decode D (Closure.interpret (Reflection.closure (reflect M Ψ))))
    → Mahlo-Space M Ψ
  from-family (a , b) = space a b

  to-from-family :
    (F : Family
      ( Decode D (Closure.interpret (Reflection.closure (reflect M Ψ)))))
    → to-family (from-family F) ＝ F
  to-from-family (a , b) = refl

  from-to-family :
    (X : Mahlo-Space M Ψ) → from-family (to-family X) ＝ X
  from-to-family (space a b) = refl

  -- The closure's inner family acts on spaces, and the parent's family of
  -- the action is Ψ's.
  action : Mahlo-Space M Ψ → Mahlo-Space M Ψ
  action X =
    from-family
      ( Closure.inner (Reflection.closure (reflect M Ψ)) (to-family X))

  parent-family : Mahlo-Space M Ψ → Family D
  parent-family X =
    map D (Closure.interpret (Reflection.closure (reflect M Ψ)))
      ( to-family X)

  action-β :
    (X : Mahlo-Space M Ψ) → parent-family (action X) ＝ Ψ (parent-family X)
  action-β X =
    ap (map D (Closure.interpret (Reflection.closure (reflect M Ψ))))
      ( to-from-family
          ( Closure.inner (Reflection.closure (reflect M Ψ)) (to-family X)))
    ∙ Closure.inner-β (Reflection.closure (reflect M Ψ)) (to-family X)

  -- The decoded displayed space.
  display : Mahlo-Space M Ψ → DΣ ℓ ℓ
  display X = record
    { Base =
        Decode D (Closure.interpret (Reflection.closure (reflect M Ψ)))
          ( base X)
    ; Fiber = λ x →
        Decode D (Closure.interpret (Reflection.closure (reflect M Ψ)))
          ( fiber X x)
    }
