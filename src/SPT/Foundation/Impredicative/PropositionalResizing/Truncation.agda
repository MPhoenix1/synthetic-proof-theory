{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Impredicative.PropositionalResizing.Truncation where

-- Propositional truncations from propositional resizing, after Voevodsky. The
-- cover of a type X of level ℓ,
--
--   Covered ℓ X = Π (P : Set ℓ). is-proposition P → (X → P) → P,
--
-- is a proposition of level ℓ + 1 under function extensionality at that level
-- (`covers-are-propositions`). Propositional resizing presents it at level ℓ,
-- and the presentation is a truncation at ℓ (`truncation-from-resizing`):
--
--   ∥ X ∥ = resize (Covered ℓ X).
--
-- One level up, the cover itself is a truncation, with no resizing of the
-- cover: resizing lowers instead the proposition it eliminates into
-- (`truncation-one-level-up`).

open import SPT.Base
open import SPT.Foundation.Covers using
  (Covered; covered-by-point; being-covered-is-proposition)
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Extensionality.Levels using (funext-below)
open import SPT.Foundation.Isomorphisms using
  (_≅_; forward; backward; ≅-sym)
open import SPT.Foundation.Propositions using (is-proposition)
open import SPT.Foundation.Propositions.Closure using
  (isomorphic-to-a-proposition)
open import SPT.Foundation.Impredicative.PropositionalResizing using
  (Propositional-Resizing)
open import SPT.Foundation.Size using (is-small)
open import SPT.Foundation.Truncations using (Truncation)
open import SPT.Foundation.Univalence using (equivalence-to-isomorphism)

------------------------------------------------------------------------
-- Covers are propositions

module _ {ℓ : Level}
  (funext : (A : Set (lsuc ℓ)) (B : A → Set (lsuc ℓ)) → FunExt A B) where

  -- Mathematical shape: X : Set ℓ gives is-proposition (Covered ℓ X).
  covers-are-propositions : (X : Set ℓ) → is-proposition (Covered ℓ X)
  covers-are-propositions X =
    being-covered-is-proposition {ℓ} {ℓ} {X}
      ( funext-below lzero funext (Set ℓ)
          (λ R → is-proposition R → (X → R) → R))
      ( λ R →
          funext-below (lsuc ℓ) funext (is-proposition R)
            (λ _ → (X → R) → R))
      (λ R → funext-below (lsuc ℓ) funext (X → R) (λ _ → R))

  -- Mathematical shape: X : Set (ℓ + 1) gives is-proposition (Covered ℓ X).
  raised-covers-are-propositions : (X : Set (lsuc ℓ)) →
    is-proposition (Covered ℓ X)
  raised-covers-are-propositions X =
    being-covered-is-proposition {lsuc ℓ} {ℓ} {X}
      (funext (Set ℓ) (λ R → is-proposition R → (X → R) → R))
      ( λ R →
          funext-below lzero funext (is-proposition R)
            (λ _ → (X → R) → R))
      (λ R → funext-below lzero funext (X → R) (λ _ → R))

------------------------------------------------------------------------
-- The truncations that resizing gives

module _ {ℓ : Level}
  (funext : (A : Set (lsuc ℓ)) (B : A → Set (lsuc ℓ)) → FunExt A B)
  (resize : Propositional-Resizing ℓ) where

  -- The cover of X, presented at level ℓ.
  resized-cover : (X : Set ℓ) → is-small ℓ (Covered ℓ X)
  resized-cover X = resize (Covered ℓ X) (covers-are-propositions funext X)

  cover-presentation : (X : Set ℓ) → pr₁ (resized-cover X) ≅ Covered ℓ X
  cover-presentation X = equivalence-to-isomorphism (pr₂ (resized-cover X))

  -- Mathematical shape: ∥ X ∥ = resize (Covered ℓ X).
  truncation-from-resizing : Truncation ℓ
  truncation-from-resizing = record
    { ∥_∥ = λ X → pr₁ (resized-cover X)
    ; ∥∥-is-proposition = λ X →
        isomorphic-to-a-proposition (≅-sym (cover-presentation X))
          (covers-are-propositions funext X)
    ; ∣_∣ = λ {X} x →
        backward (cover-presentation X) (covered-by-point {ℓ} {ℓ} {X} x)
    ; ∥∥-rec = λ {X} {P} p f u → forward (cover-presentation X) u P p f
    }

  -- Mathematical shape: for X : Set (ℓ + 1), ∥ X ∥ = Covered ℓ X; the
  -- proposition eliminated into is lowered by resizing.
  truncation-one-level-up : Truncation (lsuc ℓ)
  truncation-one-level-up = record
    { ∥_∥ = Covered ℓ
    ; ∥∥-is-proposition = raised-covers-are-propositions funext
    ; ∣_∣ = λ {X} → covered-by-point {lsuc ℓ} {ℓ} {X}
    ; ∥∥-rec = λ {X} {P} p f u →
        let E = equivalence-to-isomorphism (pr₂ (resize P p))
        in forward E
             ( u (pr₁ (resize P p))
                 (isomorphic-to-a-proposition (≅-sym E) p)
                 (λ x → backward E (f x)))
    }
