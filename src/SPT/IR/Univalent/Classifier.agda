{-# OPTIONS --safe --without-K #-}

module SPT.IR.Univalent.Classifier where

-- An exact classifier of propositions at the level of an algebra's carrier
-- gives a least generation at that level, with no resizing. A point is
-- generated when every closed family of the classifier's proxies holds
-- there (`generated`):
--
--   generated k = Π (Q : K → proxies). Closed M (proxy ∘ Q) → proxy (Q k).
--
-- It quantifies over maps into the small type of proxies, so it lies at
-- the carrier's level. It is closed (`generated-is-closed`), and under
-- function extensionality at that level it is a proposition
-- (`generated-is-proposition`), so it is a generation (`generation`).
-- Every closed family of propositions at that level is classified by a
-- closed family of proxies (`classified`, `classification`,
-- `classified-is-closed`), so the generation lies below it (`below`) and
-- is least at the carrier's level (`least`). Univalent.Resizing's
-- intersection ranges over all closed families, a type one level up, and
-- so needs resizing between levels; an exact classifier is a hypothesis
-- at one level, and excluded middle at that level gives one
-- (ExcludedMiddle's `classifier-from-excluded-middle`, then
-- Impredicative.PropositionalClassifier.Exact's `exact-classifier`).
-- Nonclaim: the generation is least at the carrier's level only, so
-- elimination into a higher level still needs a generation least there.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt; Π-is-proposition)
open import SPT.Foundation.Isomorphisms using (_≅_; forward; backward)
open import SPT.Foundation.Propositions using (is-proposition)
open import SPT.Foundation.Impredicative.PropositionalClassifier.Exact using
  (Exact-Classifier)

open import SPT.IR.Algebra using (Algebra)
open import SPT.IR.Description using (Desc; indexed)
open import SPT.IR.Restriction using (input)
open import SPT.IR.Univalent.Generation using
  (Closed; Closed-Family; Least)

------------------------------------------------------------------------
-- The generated points

-- At an operation every closed family of proxies holds, since it holds at
-- the inputs. A closed family of propositions at κ, read through the
-- classifier, is a closed family of proxies, and the generated points lie
-- in it.

module _
  {κ j : Level} {E : Set j} {γ : Desc {s = κ} E} (M : Algebra κ γ)
  (C : Exact-Classifier κ)
  where

  open Algebra M using (K; value; operation)
  open Exact-Classifier C using (proxies; proxy; classify)

  generated : K → Set κ
  generated k =
    (Q : K → proxies) → Closed M (λ k′ → proxy (Q k′)) → proxy (Q k)

  generated-is-closed : Closed M generated
  generated-is-closed a hs Q c = c a (λ p → hs p Q c)

  ----------------------------------------------------------------------
  -- Classified closed families

  classified : Closed-Family M κ → K → proxies
  classified D k =
    pr₁
      (classify (Closed-Family.family D k) (Closed-Family.proposition D k))

  classification :
    (D : Closed-Family M κ) (k : K)
    → Closed-Family.family D k ≅ proxy (classified D k)
  classification D k =
    pr₂
      (classify (Closed-Family.family D k) (Closed-Family.proposition D k))

  classified-is-closed :
    (D : Closed-Family M κ) → Closed M (λ k → proxy (classified D k))
  classified-is-closed D a hs =
    forward (classification D (operation a))
      (Closed-Family.closed D a
        (λ p →
          backward (classification D (input γ (indexed K value) a p))
            (hs p)))

  below :
    (D : Closed-Family M κ) (k : K) → generated k
    → Closed-Family.family D k
  below D k g =
    backward (classification D k) (g (classified D) (classified-is-closed D))

------------------------------------------------------------------------
-- The least generation

-- Function extensionality at κ makes the generated points a family of
-- propositions; it is used for no other step.

module _
  {κ j : Level} {E : Set j} {γ : Desc {s = κ} E} (M : Algebra κ γ)
  (C : Exact-Classifier κ)
  (funext : (A : Set κ) (B : A → Set κ) → FunExt A B)
  where

  open Algebra M using (K)
  open Exact-Classifier C using (proxies; proxy; proxies-are-propositions)

  generated-is-proposition : (k : K) → is-proposition (generated M C k)
  generated-is-proposition k =
    Π-is-proposition
      (funext (K → proxies)
        (λ Q → Closed M (λ k′ → proxy (Q k′)) → proxy (Q k)))
      (λ Q →
        Π-is-proposition
          (funext (Closed M (λ k′ → proxy (Q k′))) (λ c → proxy (Q k)))
          (λ c → proxies-are-propositions (Q k)))

  generation : Closed-Family M κ
  generation = record
    { family = generated M C
    ; proposition = generated-is-proposition
    ; closed = generated-is-closed M C
    }

  least : Least M generation κ
  least = below M C
