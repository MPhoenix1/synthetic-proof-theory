{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Modalities where

-- A propositional modality at one universe level is a monad `○` on the types
-- of that level, valued in propositions, under which the empty type of that
-- level, `Lift ℓ 𝟘`, stays empty (`dense`):
--
--   ○ X is a proposition,          η : X → ○ X,
--   bind : ○ X → (X → ○ Y) → ○ Y,  dense : ○ (Lift ℓ 𝟘) → Lift ℓ 𝟘.
--
-- On propositions it is a dense Lawvere–Tierney topology, so it lies between
-- the identity and double negation: `η`, and `○-implies-¬¬` from density.
-- `○` is functorial (`○-map`). A type is stable when `○` of it returns to it
-- (`is-stable`);
-- `○ X` eliminates into every stable type (`○-rec`) and is itself stable
-- (`○-is-stable`), and stable types are closed under products and dependent
-- functions (`×-is-stable`, `Π-is-stable`). A stable proposition is a type
-- with both properties (`Stable-Proposition`); `○ X` is one
-- (`modal-proposition`).
--
-- Two instances: propositional truncation (`truncation-modality`), for which
-- every proposition is stable (`propositions-are-truncation-stable`), and
-- double negation (`double-negation-modality`), under function
-- extensionality for the function types `¬ X → 𝟘` alone, whose stable
-- propositions are the ¬¬-stable ones.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Propositions using
  (is-proposition; 𝟘-is-proposition)
open import SPT.Cubical.Foundation.Extensionality using (FunExt)
open import SPT.Cubical.Foundation.Truncations using (Truncation; ∥∥-bind)

------------------------------------------------------------------------
-- Modalities

record Modality (ℓ : Level) : Set (lsuc ℓ) where
  infix 25 ○_
  field
    ○_ : Set ℓ → Set ℓ
    ○-is-proposition : (X : Set ℓ) → is-proposition (○ X)
    η : {X : Set ℓ} → X → ○ X
    bind : {X Y : Set ℓ} → ○ X → (X → ○ Y) → ○ Y
    dense : ○ (Lift ℓ 𝟘) → Lift ℓ 𝟘

------------------------------------------------------------------------
-- Functoriality, stability and elimination

module _ {ℓ : Level} (M : Modality ℓ) where

  open Modality M

  -- ○ is functorial.
  ○-map : {X Y : Set ℓ} → (X → Y) → ○ X → ○ Y
  ○-map f x = bind x (λ a → η (f a))

  -- ○ X implies ¬¬ X: a refutation of X, carried under ○, gives ○ of the
  -- empty type, which density refutes.
  ○-implies-¬¬ : {X : Set ℓ} → ○ X → ¬ ¬ X
  ○-implies-¬¬ x k = lower (dense (○-map (λ a → lift (k a)) x))

  -- A type is stable when ○ of it returns to it.
  is-stable : Set ℓ → Set ℓ
  is-stable X = ○ X → X

  -- ○ X eliminates into every stable type.
  ○-rec : {X P : Set ℓ} → is-stable P → (X → P) → ○ X → P
  ○-rec s f x = s (○-map f x)

  -- ○ X is stable.
  ○-is-stable : (X : Set ℓ) → is-stable (○ X)
  ○-is-stable X x = bind x (λ y → y)

  -- Stable types are closed under products and dependent functions.
  ×-is-stable : {A B : Set ℓ} → is-stable A → is-stable B →
    is-stable (A × B)
  ×-is-stable a b x = a (○-map pr₁ x) , b (○-map pr₂ x)

  Π-is-stable : {A : Set ℓ} {B : A → Set ℓ} →
    ((x : A) → is-stable (B x)) → is-stable ((x : A) → B x)
  Π-is-stable s f x = s x (○-map (λ g → g x) f)

  -- A stable proposition: a type that is a proposition and stable.
  record Stable-Proposition : Set (lsuc ℓ) where
    field
      carrier : Set ℓ
      carrier-is-proposition : is-proposition carrier
      carrier-is-stable : is-stable carrier

  -- ○ X as a stable proposition.
  modal-proposition : Set ℓ → Stable-Proposition
  modal-proposition X = record
    { carrier = ○ X
    ; carrier-is-proposition = ○-is-proposition X
    ; carrier-is-stable = ○-is-stable X
    }

------------------------------------------------------------------------
-- Propositional truncation

module _ {ℓ : Level} (t : Truncation ℓ) where

  open Truncation t

  -- Propositional truncation is a modality.
  truncation-modality : Modality ℓ
  truncation-modality = record
    { ○_ = ∥_∥
    ; ○-is-proposition = ∥∥-is-proposition
    ; η = ∣_∣
    ; bind = ∥∥-bind t
    ; dense = ∥∥-rec (λ x y → 𝟘-elim (lower x)) (λ x → x)
    }

  -- Every proposition is stable for the truncation.
  propositions-are-truncation-stable : {P : Set ℓ} → is-proposition P →
    is-stable truncation-modality P
  propositions-are-truncation-stable p = ∥∥-rec p (λ x → x)

------------------------------------------------------------------------
-- Double negation

-- Double negation is a modality, under function extensionality for the
-- function types ¬ X → 𝟘 of its values.
double-negation-modality : {ℓ : Level} →
  ((X : Set ℓ) → FunExt (¬ X) (λ _ → 𝟘)) → Modality ℓ
double-negation-modality extensionality = record
  { ○_ = λ X → ¬ ¬ X
  ; ○-is-proposition = λ X f g →
      extensionality X f g (λ k → 𝟘-is-proposition (f k) (g k))
  ; η = λ x k → k x
  ; bind = λ x f k → x (λ a → f a k)
  ; dense = λ x → 𝟘-elim (x lower)
  }
