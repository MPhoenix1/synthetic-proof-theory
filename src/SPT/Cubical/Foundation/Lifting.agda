{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Lifting where

-- A type is isomorphic to its lift (`lifting-is-isomorphism`), and isomorphic
-- types have isomorphic lifts (`lifts-of-isomorphic-types`). On
-- identifications, lifting and lowering are inverse (`lower-of-lift`,
-- `lift-of-lower`).

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Isomorphisms using
  (_≅_; forward; backward; backward-forward; forward-backward)

------------------------------------------------------------------------
-- Lifts of types

lifting-is-isomorphism : {ℓ : Level} (ℓ′ : Level) (A : Set ℓ) → A ≅ Lift ℓ′ A
lifting-is-isomorphism ℓ′ A = record
  { forward = lift
  ; backward = lower
  ; backward-forward = λ a → refl
  ; forward-backward = λ b → refl
  }

lifts-of-isomorphic-types : {ℓ ℓ′ : Level} (ℓ″ : Level)
  {A : Set ℓ} {B : Set ℓ′} → A ≅ B → Lift ℓ″ A ≅ Lift ℓ″ B
lifts-of-isomorphic-types ℓ″ e = record
  { forward = λ a → lift (forward e (lower a))
  ; backward = λ b → lift (backward e (lower b))
  ; backward-forward = λ a → ap lift (backward-forward e (lower a))
  ; forward-backward = λ b → ap lift (forward-backward e (lower b))
  }

------------------------------------------------------------------------
-- Lifts of identifications

lower-of-lift : {a : Level} (b : Level) {A : Set a} {x y : A} (p : x ＝ y) →
  ap lower (ap (lift {κ = b}) p) ＝ p
lower-of-lift b refl = refl

lift-of-lower : {a b : Level} {A : Set a} {u v : Lift b A} (q : u ＝ v) →
  ap lift (ap lower q) ＝ q
lift-of-lower refl = refl
