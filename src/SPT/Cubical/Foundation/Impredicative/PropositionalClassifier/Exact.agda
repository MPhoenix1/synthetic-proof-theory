{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Impredicative.PropositionalClassifier.Exact where

-- Exact classifiers of propositions and Rathjen's universe of propositions. An
-- exact classifier is a small family of propositions in which every small
-- proposition is isomorphic to a member (`Exact-Classifier`):
--
--   proxies : Set ℓ,   proxy : proxies → Set ℓ,   each proxy k a proposition,
--   classify : Π (X : Set ℓ). is-proposition X → Σ (k : proxies). X ≅ proxy k.
--
-- A classifier of propositions up to logical equivalence gives one
-- (`exact-classifier`). A member is a proxy with a weakly constant endomap of
-- its points (`Constant-Proxy`), and is the type of fixed points of that
-- endomap (`fixed-member`), so it is a proposition. The endomap chosen for a
-- proposition X goes through X, and its fixed points are X. The exact index
-- retains the proxy literally (`exact-index-retains-the-proxy`), and forgetting
-- the inverse laws gives a classifier up to logical equivalence
-- (`exact-classifier-is-propositional`). With propositional resizing, the
-- propositions of the next universe are classified as well
-- (`raised-propositions-are-classified`).
--
-- Under function extensionality the family is closed under products over
-- every small type, the type of its own proxies included (`exact-product`),
-- so it carries the rules of Rathjen's impredicative universe of
-- propositions P of MLV_P (`Proposition-Universe`,
-- `universe-of-exact-classifier`; Rathjen 2012, §4). MLV_P asks proof
-- irrelevance and T_P(0_P) = N₀ judgmentally; here they are a proof that
-- proofs are propositions and an elimination into the empty type.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Extensionality
  using (FunExt; Π-is-proposition)
open import SPT.Cubical.Foundation.Isomorphisms using
  (_≅_; forward; backward; ≅-sym; ≅-trans)
open import SPT.Cubical.Foundation.Propositions using (is-proposition)
open import SPT.Cubical.Foundation.Propositions.Closure using
  ( isomorphic-to-a-proposition; is-weakly-constant; fixed-points
  ; fixed-points-form-a-proposition)
open import SPT.Cubical.Foundation.Impredicative.PropositionalResizing using
  ( Propositional-Resizing; through-the-proposition
  ; through-the-proposition-is-weakly-constant
  ; fixed-points-are-the-proposition)
open import SPT.Cubical.Foundation.Impredicative.PropositionalClassifier using
  (Propositional-Classifier)
open import SPT.Cubical.Foundation.Univalence using (equivalence-to-isomorphism)

------------------------------------------------------------------------
-- Exact classifiers

-- Unlike a classifier up to logical equivalence, every member is a
-- proposition and recovery has both inverse laws.
record Exact-Classifier (ℓ : Level) : Set (lsuc ℓ) where
  field
    proxies : Set ℓ
    proxy : proxies → Set ℓ
    proxies-are-propositions : (k : proxies) → is-proposition (proxy k)
    classify : (X : Set ℓ) → is-proposition X → Σ proxies (λ k → X ≅ proxy k)

exact-classifier-is-propositional : {ℓ : Level} → Exact-Classifier ℓ →
  Propositional-Classifier ℓ
exact-classifier-is-propositional C = record
  { proxies = Exact-Classifier.proxies C
  ; proxy = Exact-Classifier.proxy C
  ; classify = λ P p →
      pr₁ (Exact-Classifier.classify C P p) ,
      forward (pr₂ (Exact-Classifier.classify C P p)) ,
      backward (pr₂ (Exact-Classifier.classify C P p))
  }

------------------------------------------------------------------------
-- From logical equivalence to isomorphism

module _ {ℓ : Level} (C : Propositional-Classifier ℓ) where

  open Propositional-Classifier C using (proxies; proxy; classify)

  -- A proxy with a weakly constant endomap of its points.
  Constant-Proxy : Set ℓ
  Constant-Proxy =
    Σ proxies (λ j → Σ (proxy j → proxy j) is-weakly-constant)

  fixed-member : Constant-Proxy → Set ℓ
  fixed-member k = fixed-points (pr₁ (pr₂ k))

  fixed-member-is-proposition : (k : Constant-Proxy) →
    is-proposition (fixed-member k)
  fixed-member-is-proposition k =
    fixed-points-form-a-proposition (pr₁ (pr₂ k)) (pr₂ (pr₂ k))

  -- The endomap of the proxy of X through X.
  constant-proxy : (X : Set ℓ) → is-proposition X → Constant-Proxy
  constant-proxy X p =
    pr₁ (classify X p) ,
    through-the-proposition p
      (pr₂ (pr₂ (classify X p)))
      (pr₁ (pr₂ (classify X p))) ,
    through-the-proposition-is-weakly-constant p
      (pr₂ (pr₂ (classify X p)))
      (pr₁ (pr₂ (classify X p)))

  exact-classifier : Exact-Classifier ℓ
  exact-classifier = record
    { proxies = Constant-Proxy
    ; proxy = fixed-member
    ; proxies-are-propositions = fixed-member-is-proposition
    ; classify = λ X p →
        constant-proxy X p ,
        ≅-sym
          ( fixed-points-are-the-proposition p
              (pr₂ (pr₂ (classify X p)))
              (pr₁ (pr₂ (classify X p))))
    }

  -- The exact index of X retains the proxy of X literally.
  exact-index-retains-the-proxy : (X : Set ℓ) (p : is-proposition X) →
    pr₁ (constant-proxy X p) ＝ pr₁ (classify X p)
  exact-index-retains-the-proxy X p = refl

------------------------------------------------------------------------
-- Raised propositions

module _ {ℓ : Level} (resize : Propositional-Resizing ℓ)
  (C : Exact-Classifier ℓ) where

  open Exact-Classifier C using (proxies; proxy; classify)

  -- Mathematical shape: a proposition of the next universe is small, and its
  -- small type is classified.
  raised-propositions-are-classified : (P : Set (lsuc ℓ)) → is-proposition P →
    Σ proxies (λ k → P ≅ proxy k)
  raised-propositions-are-classified P h =
    let E = equivalence-to-isomorphism (pr₂ (resize P h))
        c = classify (pr₁ (resize P h))
              (isomorphic-to-a-proposition (≅-sym E) h)
    in pr₁ c , ≅-trans (≅-sym E) (pr₂ c)

------------------------------------------------------------------------
-- Rathjen's universe of propositions

-- Mathematical shape: the rules for P in MLV_P,
--   propositions : Set ℓ,   proofs : propositions → Set ℓ,
--   every proofs a is a proposition,
--   empty : propositions,   proofs empty → 𝟘,
--   π : Π (A : Set ℓ). (A → propositions) → propositions,
--   proofs (π A B) ⇔ Π (x : A). proofs (B x).
-- π ranges over every small type, propositions included, so the closure is
-- impredicative.
record Proposition-Universe (ℓ : Level) : Set (lsuc ℓ) where
  field
    propositions : Set ℓ
    proofs : propositions → Set ℓ
    proofs-are-propositions : (a : propositions) → is-proposition (proofs a)
    empty : propositions
    empty-elim : proofs empty → Lift ℓ 𝟘
    π : (A : Set ℓ) → (A → propositions) → propositions
    π-holds : (A : Set ℓ) (B : A → propositions) →
      (proofs (π A B) → (x : A) → proofs (B x)) ×
      (((x : A) → proofs (B x)) → proofs (π A B))

module _ {ℓ : Level} (C : Exact-Classifier ℓ) where

  open Exact-Classifier C using (proxies; proxy; classify)

  -- The empty proposition is classified with no extensionality.
  exact-empty : Σ proxies (λ k → Lift ℓ 𝟘 ≅ proxy k)
  exact-empty = classify (Lift ℓ 𝟘) (λ x y → 𝟘-elim (lower x))

-- Function extensionality makes a product of propositions a proposition, which
-- is then classified. It is used for no other step.

module _ {ℓ : Level} (funext : (A : Set ℓ) (B : A → Set ℓ) → FunExt A B)
  (C : Exact-Classifier ℓ) where

  open Exact-Classifier C using
    (proxies; proxy; proxies-are-propositions; classify)

  exact-product : (A : Set ℓ) (B : A → proxies) →
    Σ proxies (λ k → ((x : A) → proxy (B x)) ≅ proxy k)
  exact-product A B =
    classify ((x : A) → proxy (B x))
      ( Π-is-proposition (funext A (λ x → proxy (B x)))
          (λ x → proxies-are-propositions (B x)))

  universe-of-exact-classifier : Proposition-Universe ℓ
  universe-of-exact-classifier = record
    { propositions = proxies
    ; proofs = proxy
    ; proofs-are-propositions = proxies-are-propositions
    ; empty = pr₁ (exact-empty C)
    ; empty-elim = backward (pr₂ (exact-empty C))
    ; π = λ A B → pr₁ (exact-product A B)
    ; π-holds = λ A B →
        backward (pr₂ (exact-product A B)) ,
        forward (pr₂ (exact-product A B))
    }
