{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Impredicative.Classification where

-- Logical classification of one family of types by another. G classifies F
-- when each member of F has maps both ways with a member of G (`Classifies`):
--
--   Classifies F G = Π (x : A). Σ (i : I). (F x → G i) × (G i → F x).
--
-- No inverse laws are asked. Two impredicative principles for a Tarski
-- family (U , T) are classifications. Resizing: every type of the level of
-- U is classified by T (`Resizing`). A classifier: a code `proxies` and a
-- family `proxy` of codes over its decoding, such that T ∘ proxy classifies
-- every decoding of T (`Classifier`); `chosen`, `encode` and `decode` read
-- off the classification of a code. At the family of all types of one
-- level, (Set ℓ , λ X → X), resizing says that every type of the next level
-- has maps both ways with a type of level ℓ, and a classifier classifies
-- all types of level ℓ.

open import SPT.Base

------------------------------------------------------------------------
-- Classification

module _ {α κ ι ν : Level} {A : Set α} {I : Set ι} where

  -- Mathematical shape: Π x. Σ i. (F x → G i) × (G i → F x).
  Classifies : (A → Set κ) → (I → Set ν) → Set (α ⊔ κ ⊔ ι ⊔ ν)
  Classifies F G = (x : A) → Σ I (λ i → (F x → G i) × (G i → F x))

------------------------------------------------------------------------
-- Resizing and classifiers of a Tarski family

module _ {κ ν : Level} {U : Set κ} where

  -- Every type of the level of U has maps both ways with a decoding.
  Resizing : (U → Set ν) → Set (lsuc κ ⊔ ν)
  Resizing T = Classifies (λ (P : Set κ) → P) T

-- One family of codes, indexed by the decoding of the code `proxies`,
-- classifies the decoding of every code.
record Classifier {κ ν : Level} {U : Set κ} (T : U → Set ν) : Set (κ ⊔ ν)
  where
  field
    proxies : U
    proxy : T proxies → U
    classify : Classifies T (λ j → T (proxy j))

module _ {κ ν : Level} {U : Set κ} {T : U → Set ν} (C : Classifier T) where

  open Classifier C using (proxies; proxy; classify)

  chosen : U → T proxies
  chosen a = pr₁ (classify a)

  encode : (a : U) → T a → T (proxy (chosen a))
  encode a = pr₁ (pr₂ (classify a))

  decode : (a : U) → T (proxy (chosen a)) → T a
  decode a = pr₂ (pr₂ (classify a))
