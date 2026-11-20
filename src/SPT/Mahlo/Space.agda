{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Space where

-- Resident Mahlo closure when small displayed spaces are the type-objects:
-- the parent's codes are displayed spaces, decoded to their totals. The
-- returned space has the generated codes of the induction–recursive closure
-- as its base and a one-point fiber over each (`flat`), so each point of
-- the space carries its generated code literally (`read`, `write`). The
-- closure and its reflection (`closure`, `reflection`) give the Mahlo rule
-- for every choice of formers (`mahlo`).

open import SPT.Base
open import SPT.Foundation.Spaces using (DΣ; Total)
open import SPT.Mahlo.Specification using
  (Operator; Formers; Closure; Reflection; Mahlo)
import SPT.Mahlo.Relative as Relative

------------------------------------------------------------------------
-- A type as a displayed space with one-point fibers

flat : {ℓ : Level} → Set ℓ → DΣ ℓ ℓ
flat {ℓ} X = record
  { Base = X
  ; Fiber = λ _ → Lift ℓ 𝟙
  }

------------------------------------------------------------------------
-- The generated codes as a displayed space

module _
  {ℓ : Level} (Q : Formers (DΣ ℓ ℓ) Total) (Φ : Operator Total)
  where

  read : Total (flat (Relative.Generated Q Φ)) → Relative.Generated Q Φ
  read = pr₁

  write : Relative.Generated Q Φ → Total (flat (Relative.Generated Q Φ))
  write c = c , lift ⋆

  read-write : (c : Relative.Generated Q Φ) → read (write c) ＝ c
  read-write c = refl

  closure : Closure Q Φ (Total (flat (Relative.Generated Q Φ)))
  closure = record
    { interpret = λ c → Relative.interpret Q Φ (read c)
    ; empty = write Relative.empty , refl
    ; unit = write Relative.unit , refl
    ; two = write Relative.two , refl
    ; natural = write Relative.natural , refl
    ; product = λ F →
        write (Relative.product (read (pr₁ F)) (λ x → read (pr₂ F x)))
        , refl
    ; sum = λ F →
        write (Relative.sum (read (pr₁ F)) (λ x → read (pr₂ F x)))
        , refl
    ; tree = λ F →
        write (Relative.tree (read (pr₁ F)) (λ x → read (pr₂ F x)))
        , refl
    ; identity = λ a x y →
        write (Relative.identity (read a) x y) , refl
    ; inner = λ F →
        write (Relative.result (read (pr₁ F)) (λ x → read (pr₂ F x)))
        , (λ y →
            write
              ( Relative.branch (read (pr₁ F)) (λ x → read (pr₂ F x)) y))
    ; inner-β = λ F → refl
    }

  reflection : Reflection Q Φ
  reflection = record
    { carrier = flat (Relative.Generated Q Φ)
    ; closure = closure
    }

------------------------------------------------------------------------
-- The Mahlo rule

mahlo : {ℓ : Level} (Q : Formers (DΣ ℓ ℓ) Total) → Mahlo Q
mahlo Q = record
  { reflect = reflection Q
  }
