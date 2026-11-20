{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Isomorphisms where

-- An isomorphism `A ≅ B` is a pair of maps, forward and backward, with
-- pointwise inverse laws. Isomorphisms have an identity, an inverse and a
-- composite, and an isomorphism of each fiber gives an isomorphism of dependent
-- pair types over the same index (`Σ-cong`), pairs whose first component
-- is a pair reassociate (`Σ-assoc`), and a pair over the one point is its
-- second component (`Σ-over-𝟙`). Identifications of pairs are
-- pairs of identifications, the second over the first (`Σ-＝-≅`):
--
--   (σ ＝ τ) ≅ Σ (p : pr₁ σ ＝ pr₁ τ). transport B p (pr₂ σ) ＝ pr₂ τ.
--
-- Two isomorphisms agree pointwise when their forward maps agree at every point
-- and so do their backward maps; the forward agreement already determines the
-- backward one through the inverse laws.
--
-- The inverse laws are pointwise. Function extensionality, as a hypothesis for
-- the function types concerned, turns them, and pointwise agreements, into
-- identifications of functions.
--
-- Transport along an identification is an isomorphism of the fibers
-- (`transport-is-isomorphism`). Pointwise isomorphisms give an isomorphism of
-- dependent function types under extensionality for both (`Π-cong`, after
-- TypeTopology's UF.EquivalenceExamples):
--
--   ((a : A) → B a ≅ C a) → ((a : A) → B a) ≅ ((a : A) → C a).

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Extensionality using (FunExt)

------------------------------------------------------------------------
-- Isomorphisms

infix 5 _≅_

record _≅_ {ℓ κ : Level} (A : Set ℓ) (B : Set κ) : Set (ℓ ⊔ κ) where
  field
    forward : A → B
    backward : B → A
    backward-forward : (a : A) → backward (forward a) ＝ a
    forward-backward : (b : B) → forward (backward b) ＝ b

open _≅_ public

------------------------------------------------------------------------
-- Pointwise agreement

module _ {ℓ κ : Level} {A : Set ℓ} {B : Set κ} where

  record Pointwise-Agreement (E F : A ≅ B) : Set (ℓ ⊔ κ) where
    field
      forward-agrees : (a : A) → forward E a ＝ forward F a
      backward-agrees : (b : B) → backward E b ＝ backward F b

  open Pointwise-Agreement public

------------------------------------------------------------------------
-- Identity, inverse and composite

module _ {ℓ : Level} {A : Set ℓ} where

  ≅-refl : A ≅ A
  ≅-refl = record
    { forward = id
    ; backward = id
    ; backward-forward = λ a → refl
    ; forward-backward = λ a → refl
    }

module _ {ℓ κ : Level} {A : Set ℓ} {B : Set κ} where

  ≅-sym : A ≅ B → B ≅ A
  ≅-sym E = record
    { forward = backward E
    ; backward = forward E
    ; backward-forward = forward-backward E
    ; forward-backward = backward-forward E
    }

module _ {ℓ κ μ : Level} {A : Set ℓ} {B : Set κ} {C : Set μ} where

  ≅-trans : A ≅ B → B ≅ C → A ≅ C
  ≅-trans E F = record
    { forward = forward F ∘ forward E
    ; backward = backward E ∘ backward F
    ; backward-forward = λ a →
        ap (backward E) (backward-forward F (forward E a))
          ∙ backward-forward E a
    ; forward-backward = λ c →
        ap (forward F) (forward-backward E (backward F c))
          ∙ forward-backward F c
    }

------------------------------------------------------------------------
-- Dependent pairs over one index

-- The index is kept in both directions; only the second component is mapped.

module _ {ℓ κ μ : Level} {I : Set ℓ} {L : I → Set κ} {R : I → Set μ} where

  Σ-cong : ((i : I) → L i ≅ R i) → Σ I L ≅ Σ I R
  Σ-cong fibers = record
    { forward = λ (i , l) → i , forward (fibers i) l
    ; backward = λ (i , r) → i , backward (fibers i) r
    ; backward-forward = λ (i , l) →
        ap (λ m → i , m) (backward-forward (fibers i) l)
    ; forward-backward = λ (i , r) →
        ap (λ m → i , m) (forward-backward (fibers i) r)
    }

------------------------------------------------------------------------
-- Reassociation of dependent pairs

-- A pair whose first component is a pair is a triple; both round trips are
-- refl by η (after TypeTopology's Σ-assoc).

module _ {ℓ κ μ : Level} {A : Set ℓ} {B : A → Set κ} where

  Σ-assoc : (C : (a : A) → B a → Set μ) →
    Σ (Σ A B) (λ p → C (pr₁ p) (pr₂ p)) ≅ Σ A (λ a → Σ (B a) (C a))
  Σ-assoc C = record
    { forward = λ p → pr₁ (pr₁ p) , (pr₂ (pr₁ p) , pr₂ p)
    ; backward = λ t → (pr₁ t , pr₁ (pr₂ t)) , pr₂ (pr₂ t)
    ; backward-forward = λ p → refl
    ; forward-backward = λ t → refl
    }

-- A pair over the one point is its second component, by η.

module _ {ℓ : Level} {B : 𝟙 → Set ℓ} where

  Σ-over-𝟙 : Σ 𝟙 B ≅ B ⋆
  Σ-over-𝟙 = record
    { forward = pr₂
    ; backward = λ b → ⋆ , b
    ; backward-forward = λ p → refl
    ; forward-backward = λ b → refl
    }

------------------------------------------------------------------------
-- Transport

-- Transport along an identification is an isomorphism of the fibers; its
-- backward map transports back.

module _ {ℓ κ : Level} {A : Set ℓ} (P : A → Set κ) where

  transport-is-isomorphism : {x y : A} → x ＝ y → P x ≅ P y
  transport-is-isomorphism e = record
    { forward = transport P e
    ; backward = transport P (e ⁻¹)
    ; backward-forward = forth-and-back-transport P e
    ; forward-backward = back-and-forth-transport P e
    }

------------------------------------------------------------------------
-- Identifications of pairs

-- An identification of pairs gives one of their first components and one
-- of their second components over it (`ap pr₁`, `from-Σ-＝-pr₂`), and these
-- give it back (`to-Σ-＝`). Both inverse laws are path induction. After
-- the HoTT book, Theorem 2.7.2 (TypeTopology's Σ-＝-≃).

module _ {ℓ κ : Level} {A : Set ℓ} {B : A → Set κ} where

  private
    Σ-＝-backward-forward : {σ τ : Σ A B} (e : σ ＝ τ) →
      to-Σ-＝ (ap pr₁ e) (from-Σ-＝-pr₂ e) ＝ e
    Σ-＝-backward-forward refl = refl

    Σ-＝-forward-backward : (a a′ : A) (b : B a) (b′ : B a′)
      (q : Σ (a ＝ a′) (λ p → transport B p b ＝ b′)) →
      ( ap pr₁ (to-Σ-＝ (pr₁ q) (pr₂ q))
      , from-Σ-＝-pr₂ (to-Σ-＝ (pr₁ q) (pr₂ q)))
        ＝ q
    Σ-＝-forward-backward a a′ b b′ (refl , refl) = refl

  Σ-＝-≅ : (σ τ : Σ A B) →
    (σ ＝ τ) ≅ Σ (pr₁ σ ＝ pr₁ τ) (λ p → transport B p (pr₂ σ) ＝ pr₂ τ)
  Σ-＝-≅ σ τ = record
    { forward = λ e → ap pr₁ e , from-Σ-＝-pr₂ e
    ; backward = λ q → to-Σ-＝ (pr₁ q) (pr₂ q)
    ; backward-forward = λ e → Σ-＝-backward-forward e
    ; forward-backward =
        Σ-＝-forward-backward (pr₁ σ) (pr₁ τ) (pr₂ σ) (pr₂ τ)
    }

------------------------------------------------------------------------
-- The forward agreement determines the backward one

module _ {ℓ κ : Level} {A : Set ℓ} {B : Set κ} where

  agreement-from-forward : (E F : A ≅ B) →
    ((a : A) → forward E a ＝ forward F a) → Pointwise-Agreement E F
  agreement-from-forward E F agrees = record
    { forward-agrees = agrees
    ; backward-agrees = λ b →
        ap (backward E) (forward-backward F b) ⁻¹
          ∙ (ap (backward E) (agrees (backward F b) ⁻¹)
            ∙ backward-forward E (backward F b))
    }

------------------------------------------------------------------------
-- Under function extensionality

module _ {ℓ κ : Level} {A : Set ℓ} {B : Set κ} where

  backward-forward-identification : FunExt A (λ _ → A) → (E : A ≅ B) →
    backward E ∘ forward E ＝ id
  backward-forward-identification extensionality E =
    extensionality (backward E ∘ forward E) id (backward-forward E)

  forward-backward-identification : FunExt B (λ _ → B) → (E : A ≅ B) →
    forward E ∘ backward E ＝ id
  forward-backward-identification extensionality E =
    extensionality (forward E ∘ backward E) id (forward-backward E)

module _ {ℓ κ : Level} {A : Set ℓ} {B : Set κ} {E F : A ≅ B} where

  forward-identification : FunExt A (λ _ → B) →
    Pointwise-Agreement E F → forward E ＝ forward F
  forward-identification extensionality agreement =
    extensionality (forward E) (forward F) (forward-agrees agreement)

  backward-identification : FunExt B (λ _ → A) →
    Pointwise-Agreement E F → backward E ＝ backward F
  backward-identification extensionality agreement =
    extensionality (backward E) (backward F) (backward-agrees agreement)

-- Pointwise isomorphisms give an isomorphism of dependent functions; its
-- inverse laws are the pointwise ones, through extensionality for both
-- function types.

module _ {ℓ κ μ : Level} {A : Set ℓ} {B : A → Set κ} {C : A → Set μ} where

  Π-cong : FunExt A B → FunExt A C → ((a : A) → B a ≅ C a) →
    ((a : A) → B a) ≅ ((a : A) → C a)
  Π-cong left right fibers = record
    { forward = λ f a → forward (fibers a) (f a)
    ; backward = λ g a → backward (fibers a) (g a)
    ; backward-forward = λ f →
        left (λ a → backward (fibers a) (forward (fibers a) (f a))) f
          (λ a → backward-forward (fibers a) (f a))
    ; forward-backward = λ g →
        right (λ a → forward (fibers a) (backward (fibers a) (g a))) g
          (λ a → forward-backward (fibers a) (g a))
    }
