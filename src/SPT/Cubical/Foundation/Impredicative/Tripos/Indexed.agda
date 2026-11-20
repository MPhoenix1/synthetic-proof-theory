{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Impredicative.Tripos.Indexed where

-- Triposes over a base of types with predicates of any form. An indexed
-- tripos gives each type X of level α a preorder of predicates on X
-- (`Predicate`, `entails`) with the operations of a Heyting pre-algebra by
-- their universal properties, reindexing along maps that is monotone,
-- functorial and preserves the operations up to entailment both ways,
-- quantifiers left and right adjoint to reindexing that satisfy
-- Beck–Chevalley along the canonical pullbacks, and a generic predicate of
-- which every predicate is a reindexing (`Indexed-Tripos`):
--
--   Predicate : Set α → Set π,   entails φ ψ : Set ε,
--   exists f ⊣ reindex f ⊣ all f,   proxy : Predicate proxies.
--
-- Predicates and entailments sit at independent levels. A tripos of small
-- predicates is one, with every reindexing law by computation
-- (`tripos-gives-indexed-tripos`); the realizability tripos
-- (Realizability.Tripos) is another.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Impredicative.Tripos using
  ( reindex; top; bottom; _∧_; _∨_; _⇒_; every-predicate-is-below-top
  ; bottom-is-below-every-predicate; meet-is-the-greatest-lower-bound
  ; join-is-the-least-upper-bound; implication-is-right-adjoint-to-meet
  ; pullback-left; pullback-right; Quantifiers; Generic-Predicate; Tripos)
open import SPT.Cubical.Foundation.LogicalEquivalence using (_⇔_)

------------------------------------------------------------------------
-- Indexed triposes

record Indexed-Tripos (α π ε : Level) : Set (lsuc (α ⊔ π ⊔ ε)) where
  field
    Predicate : Set α → Set π
    entails : {X : Set α} → Predicate X → Predicate X → Set ε
    entails-refl : {X : Set α} (φ : Predicate X) → entails φ φ
    entails-trans : {X : Set α} (φ ψ χ : Predicate X) → entails φ ψ →
      entails ψ χ → entails φ χ
    reindex-along : {X Y : Set α} → (X → Y) → Predicate Y → Predicate X
    reindex-monotone : {X Y : Set α} (f : X → Y) (φ ψ : Predicate Y) →
      entails φ ψ → entails (reindex-along f φ) (reindex-along f ψ)
    reindex-identity : {X : Set α} (φ : Predicate X) →
      entails (reindex-along (λ x → x) φ) φ ×
      entails φ (reindex-along (λ x → x) φ)
    reindex-compose : {X Y Z : Set α} (f : X → Y) (g : Y → Z)
      (φ : Predicate Z) →
      entails (reindex-along (λ x → g (f x)) φ)
        (reindex-along f (reindex-along g φ)) ×
      entails (reindex-along f (reindex-along g φ))
        (reindex-along (λ x → g (f x)) φ)
    truth : {X : Set α} → Predicate X
    falsity : {X : Set α} → Predicate X
    meet : {X : Set α} → Predicate X → Predicate X → Predicate X
    join : {X : Set α} → Predicate X → Predicate X → Predicate X
    implication : {X : Set α} → Predicate X → Predicate X → Predicate X
    truth-intro : {X : Set α} (φ : Predicate X) → entails φ truth
    falsity-elim : {X : Set α} (φ : Predicate X) → entails falsity φ
    meet-adjoint : {X : Set α} (χ φ ψ : Predicate X) →
      entails χ (meet φ ψ) ⇔ (entails χ φ × entails χ ψ)
    join-adjoint : {X : Set α} (φ ψ χ : Predicate X) →
      entails (join φ ψ) χ ⇔ (entails φ χ × entails ψ χ)
    implication-adjoint : {X : Set α} (χ φ ψ : Predicate X) →
      entails (meet χ φ) ψ ⇔ entails χ (implication φ ψ)
    reindex-truth : {X Y : Set α} (f : X → Y) →
      entails (reindex-along f truth) truth ×
      entails truth (reindex-along f truth)
    reindex-falsity : {X Y : Set α} (f : X → Y) →
      entails (reindex-along f falsity) falsity ×
      entails falsity (reindex-along f falsity)
    reindex-meet : {X Y : Set α} (f : X → Y) (φ ψ : Predicate Y) →
      entails (reindex-along f (meet φ ψ))
        (meet (reindex-along f φ) (reindex-along f ψ)) ×
      entails (meet (reindex-along f φ) (reindex-along f ψ))
        (reindex-along f (meet φ ψ))
    reindex-join : {X Y : Set α} (f : X → Y) (φ ψ : Predicate Y) →
      entails (reindex-along f (join φ ψ))
        (join (reindex-along f φ) (reindex-along f ψ)) ×
      entails (join (reindex-along f φ) (reindex-along f ψ))
        (reindex-along f (join φ ψ))
    reindex-implication : {X Y : Set α} (f : X → Y) (φ ψ : Predicate Y) →
      entails (reindex-along f (implication φ ψ))
        (implication (reindex-along f φ) (reindex-along f ψ)) ×
      entails (implication (reindex-along f φ) (reindex-along f ψ))
        (reindex-along f (implication φ ψ))
    exists : {X Y : Set α} → (X → Y) → Predicate X → Predicate Y
    all : {X Y : Set α} → (X → Y) → Predicate X → Predicate Y
    exists-adjoint : {X Y : Set α} (f : X → Y) (φ : Predicate X)
      (ψ : Predicate Y) → entails (exists f φ) ψ ⇔ entails φ (reindex-along f ψ)
    all-adjoint : {X Y : Set α} (f : X → Y) (φ : Predicate X)
      (ψ : Predicate Y) → entails (reindex-along f ψ) φ ⇔ entails ψ (all f φ)
    exists-beck-chevalley : {X Y Z : Set α} (f : X → Y) (g : Z → Y)
      (φ : Predicate X) →
      entails (reindex-along g (exists f φ))
        (exists (pullback-right f g) (reindex-along (pullback-left f g) φ)) ×
      entails
        (exists (pullback-right f g) (reindex-along (pullback-left f g) φ))
        (reindex-along g (exists f φ))
    all-beck-chevalley : {X Y Z : Set α} (f : X → Y) (g : Z → Y)
      (φ : Predicate X) →
      entails (reindex-along g (all f φ))
        (all (pullback-right f g) (reindex-along (pullback-left f g) φ)) ×
      entails (all (pullback-right f g) (reindex-along (pullback-left f g) φ))
        (reindex-along g (all f φ))
    proxies : Set α
    proxy : Predicate proxies
    classify : (X : Set α) (φ : Predicate X) →
      Σ (X → proxies)
        (λ χ →
          entails φ (reindex-along χ proxy) × entails (reindex-along χ proxy) φ)

------------------------------------------------------------------------
-- A tripos of small predicates

-- Predicates X → Set ℓ ordered by inclusion. Reindexing commutes with the
-- pointwise operations by computation; the quantifiers and the generic
-- predicate are the tripos's.
tripos-gives-indexed-tripos : {α ℓ : Level} → Tripos α ℓ →
  Indexed-Tripos α (α ⊔ lsuc ℓ) (α ⊔ ℓ)
tripos-gives-indexed-tripos {α} {ℓ} T = record
  { Predicate = λ X → X → Set ℓ
  ; entails = λ φ ψ → φ ⊆ᵖ ψ
  ; entails-refl = λ φ x p → p
  ; entails-trans = λ φ ψ χ f g x p → g x (f x p)
  ; reindex-along = reindex
  ; reindex-monotone = λ f φ ψ h x p → h (f x) p
  ; reindex-identity = λ φ → (λ x p → p) , (λ x p → p)
  ; reindex-compose = λ f g φ → (λ x p → p) , (λ x p → p)
  ; truth = top ℓ
  ; falsity = bottom ℓ
  ; meet = _∧_
  ; join = _∨_
  ; implication = _⇒_
  ; truth-intro = every-predicate-is-below-top
  ; falsity-elim = bottom-is-below-every-predicate
  ; meet-adjoint = meet-is-the-greatest-lower-bound
  ; join-adjoint = join-is-the-least-upper-bound
  ; implication-adjoint = implication-is-right-adjoint-to-meet
  ; reindex-truth = λ f → (λ x p → p) , (λ x p → p)
  ; reindex-falsity = λ f → (λ x p → p) , (λ x p → p)
  ; reindex-meet = λ f φ ψ → (λ x p → p) , (λ x p → p)
  ; reindex-join = λ f φ ψ → (λ x p → p) , (λ x p → p)
  ; reindex-implication = λ f φ ψ → (λ x p → p) , (λ x p → p)
  ; exists = Quantifiers.exists (Tripos.quantifiers T)
  ; all = Quantifiers.all (Tripos.quantifiers T)
  ; exists-adjoint = Quantifiers.exists-adjoint (Tripos.quantifiers T)
  ; all-adjoint = Quantifiers.all-adjoint (Tripos.quantifiers T)
  ; exists-beck-chevalley =
      Quantifiers.exists-beck-chevalley (Tripos.quantifiers T)
  ; all-beck-chevalley = Quantifiers.all-beck-chevalley (Tripos.quantifiers T)
  ; proxies = Generic-Predicate.proxies (Tripos.generic T)
  ; proxy = Generic-Predicate.proxy (Tripos.generic T)
  ; classify = Generic-Predicate.classify (Tripos.generic T)
  }
