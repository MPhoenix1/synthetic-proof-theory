{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Mahlo.Ambient where

-- The ambient parent of level ℓ: its codes are the types of level ℓ, each
-- decoding to itself.  Operator ℓ is the type of operators on its
-- families, formers selects the ordinary type formers, and laws gives
-- their decoding laws, each by refl.  No reflector is assumed here.

open import SPT.Cubical.Base
import SPT.Cubical.Mahlo.Specification as Mahlo
import SPT.Cubical.Mahlo.Decoding as Decoding

Operator : (ℓ : Level) → Set (lsuc ℓ)
Operator ℓ = Mahlo.Operator (λ (A : Set ℓ) → A)

-- The formers are the types themselves, so every law holds by refl.
formers : (ℓ : Level) → Mahlo.Formers (Set ℓ) (λ A → A)
formers ℓ = record
  { empty = Lift ℓ 𝟘
  ; unit = Lift ℓ 𝟙
  ; two = Lift ℓ 𝟚
  ; natural = Lift ℓ ℕ
  ; product = λ { (A , B) → (x : A) → B x }
  ; sum = λ { (A , B) → Σ A B }
  ; tree = λ { (A , B) → Decoding.W A B }
  ; identity = λ A x y → x ＝ y
  }

laws : (ℓ : Level) → Decoding.DecodingLaws (formers ℓ)
laws ℓ = record
  { empty-β = refl
  ; unit-β = refl
  ; two-β = refl
  ; natural-β = refl
  ; product-β = λ A B → refl
  ; sum-β = λ A B → refl
  ; tree-β = λ A B → refl
  ; identity-β = λ A x y → refl
  }
