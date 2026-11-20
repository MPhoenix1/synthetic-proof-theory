{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Extensionality.Levels where

-- Function extensionality at one level gives it at every function type below
-- that level, through lifting the domain and the values (`funext-below`):
--
--   ((A : Set (a ⊔ b ⊔ c)) (B : A → Set (a ⊔ b ⊔ c)) → FunExt A B)
--     → (A : Set a) (B : A → Set b) → FunExt A B.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Extensionality using (FunExt)

funext-below : {a b : Level} (c : Level) →
  ((A : Set (a ⊔ b ⊔ c)) (B : A → Set (a ⊔ b ⊔ c)) → FunExt A B) →
  (A : Set a) (B : A → Set b) → FunExt A B
funext-below {a} {b} c funext A B f g h =
  ap (λ k x → lower (k (lift x)))
    ( funext
        (Lift (a ⊔ b ⊔ c) A)
        (λ x → Lift (a ⊔ b ⊔ c) (B (lower x)))
        (λ x → lift (f (lower x)))
        (λ x → lift (g (lower x)))
        (λ x → ap lift (h (lower x))))
