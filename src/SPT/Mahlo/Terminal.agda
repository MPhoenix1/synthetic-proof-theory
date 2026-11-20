{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Terminal where

-- The one-code family with one point has Mahlo reflection (reflecting).
-- Every selected former has its unique name, and every operator is
-- reflected by the unique code. Its closure equation holds by unit η.

open import SPT.Base
import SPT.Mahlo.Specification as Reflection

------------------------------------------------------------------------
-- Reflection on the one-code family


-- Reflection over one code with one point: the one code, every name the
-- one point.
reflecting : {α β : Level}
  (Q : Reflection.Formers (Lift α 𝟙) (λ _ → Lift β 𝟙)) → Reflection.Mahlo Q
reflecting Q = record
  { reflect = λ Ψ → record
      { carrier = lift ⋆
      ; closure = record
          { interpret = λ _ → lift ⋆
          ; empty = lift ⋆ , refl
          ; unit = lift ⋆ , refl
          ; two = lift ⋆ , refl
          ; natural = lift ⋆ , refl
          ; product = λ _ → lift ⋆ , refl
          ; sum = λ _ → lift ⋆ , refl
          ; tree = λ _ → lift ⋆ , refl
          ; identity = λ _ _ _ → lift ⋆ , refl
          ; inner = λ _ → lift ⋆ , λ _ → lift ⋆
          ; inner-β = λ _ → refl
          }
      }
  }

