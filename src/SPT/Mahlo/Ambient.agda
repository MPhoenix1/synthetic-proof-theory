{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Ambient where

-- The ambient parent of level `ℓ` has as codes the types of level `ℓ`, each
-- decoding to itself. `Operator ℓ` is the type of operators on its families,
-- `formers ℓ` selects the ordinary type formers, and `laws ℓ` gives their
-- decoding laws, each by `refl`, since the formers are the types themselves. No
-- reflector is assumed here.

open import SPT.Base
import SPT.Mahlo.Specification as Mahlo
open import SPT.Foundation.Tree.W using (W)
open import SPT.Mahlo.Decoding using (DecodingLaws)

Operator : (ℓ : Level) → Set (lsuc ℓ)
Operator ℓ = Mahlo.Operator (λ (A : Set ℓ) → A)

formers : (ℓ : Level) → Mahlo.Formers (Set ℓ) (λ A → A)
formers ℓ = record
  { empty = Lift ℓ 𝟘
  ; unit = Lift ℓ 𝟙
  ; two = Lift ℓ 𝟚
  ; natural = Lift ℓ ℕ
  ; product = λ (A , B) → (x : A) → B x
  ; sum = λ (A , B) → Σ A B
  ; tree = λ (A , B) → W A B
  ; identity = λ A x y → x ＝ y
  }

laws : (ℓ : Level) → DecodingLaws (formers ℓ)
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
