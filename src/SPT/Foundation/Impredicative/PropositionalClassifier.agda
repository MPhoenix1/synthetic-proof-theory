{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Impredicative.PropositionalClassifier where

-- Classifiers of propositions. A classifier of propositions is a small
-- family in which every small proposition has a logically equivalent member
-- (`Propositional-Classifier`):
--
--   proxies : Set ℓ,   proxy : proxies → Set ℓ,
--   classify : Π (P : Set ℓ). is-proposition P →
--                Σ (j : proxies). (P → proxy j) × (proxy j → P).
--
-- No inverse law is asked. A classifier has distinct true and false members
-- (`proxies-are-distinct`), and it gives each small type a small type of
-- characteristic maps (`Small-Power`, `member`, `characteristic`,
-- `characteristic-is-complete`). Excluded middle gives a classifier with
-- proxies in 𝟚 (ExcludedMiddle's `classifier-from-excluded-middle`).

open import SPT.Base
open import SPT.Foundation.Propositions using (is-proposition)

------------------------------------------------------------------------
-- Classifiers of propositions

-- Mathematical shape: a small family in which every small proposition is
-- logically equivalent to a member. No inverse law is asked.
record Propositional-Classifier (ℓ : Level) : Set (lsuc ℓ) where
  field
    proxies : Set ℓ
    proxy : proxies → Set ℓ
    classify : (P : Set ℓ) → is-proposition P →
      Σ proxies (λ j → (P → proxy j) × (proxy j → P))

-- Non-degeneracy: the empty and the unit type have members classifying them,
-- so a classifier has a member with no point and one with a point, and those
-- two are distinct.

module _ {ℓ : Level} (C : Propositional-Classifier ℓ) where

  false-proxy true-proxy : Propositional-Classifier.proxies C
  false-proxy =
    pr₁
      ( Propositional-Classifier.classify C (Lift ℓ 𝟘)
          (λ x y → 𝟘-elim (lower x)))
  true-proxy =
    pr₁
      ( Propositional-Classifier.classify C (Lift ℓ 𝟙)
          (λ x y → refl))

  false-proxy-is-empty : Propositional-Classifier.proxy C false-proxy → 𝟘
  false-proxy-is-empty q =
    lower
      ( pr₂
          ( pr₂
              ( Propositional-Classifier.classify C (Lift ℓ 𝟘)
                  (λ x y → 𝟘-elim (lower x))))
          q)

  true-proxy-is-inhabited : Propositional-Classifier.proxy C true-proxy
  true-proxy-is-inhabited =
    pr₁
      ( pr₂
          ( Propositional-Classifier.classify C (Lift ℓ 𝟙)
              (λ x y → refl)))
      (lift ⋆)

  -- Mathematical shape: a classifier does not have a single proxy.
  proxies-are-distinct : false-proxy ≠ true-proxy
  proxies-are-distinct e =
    false-proxy-is-empty
      ( transport (Propositional-Classifier.proxy C) (e ⁻¹)
          true-proxy-is-inhabited)

------------------------------------------------------------------------
-- Small powers

-- A classifier gives each small type X a small type of characteristic maps,
-- X → proxies: every proposition-valued family on X is the family of
-- members of one of them.

module _ {ℓ : Level} (C : Propositional-Classifier ℓ) (X : Set ℓ) where

  Small-Power : Set ℓ
  Small-Power = X → Propositional-Classifier.proxies C

  member : Small-Power → X → Set ℓ
  member S x = Propositional-Classifier.proxy C (S x)

  characteristic : (A : X → Set ℓ) → ((x : X) → is-proposition (A x)) →
    Small-Power
  characteristic A p x = pr₁ (Propositional-Classifier.classify C (A x) (p x))

  -- Mathematical shape: A x ⇔ member (characteristic A) x.
  characteristic-is-complete : (A : X → Set ℓ)
    (p : (x : X) → is-proposition (A x)) (x : X) →
    (A x → member (characteristic A p) x) ×
    (member (characteristic A p) x → A x)
  characteristic-is-complete A p x =
    pr₂ (Propositional-Classifier.classify C (A x) (p x))
