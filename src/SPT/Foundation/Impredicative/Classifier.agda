{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Impredicative.Classifier where

-- The classifier of a level and power presentations. A classifier of the
-- types of level ℓ is the classifier of Impredicative.Classification for
-- the family of all of them, Classifier (λ (X : Set ℓ) → X): a small family
-- of proxies with maps both ways between every small type and one proxy,
--
--   proxies : Set ℓ,   proxy : proxies → Set ℓ,
--   classify : Π (X : Set ℓ). Σ (j : proxies). (X → proxy j) × (proxy j → X),
--
-- and SPT writes it as that instance, never as a definition of its own. The
-- recovery is logical only: with an identification for recovery no small
-- family classifies every small type (Diagonal). Restricted to propositions
-- it is a classifier of propositions
-- (`classifier-gives-propositional-classifier`).
--
-- A power presentation of a small type A is a small type of subsets that
-- retains every small predicate on A up to pointwise logical equivalence
-- (`Power-Presentation`):
--
--   Subsets : Set ℓ,   member : Subsets → A → Set ℓ,
--   retain : (A → Set ℓ) → Subsets,
--   recover : Π X a. (X a → member (retain X) a) × (member (retain X) a → X a).
--
-- The power type always has lawless small presentations
-- (Classifier.Discriminator), so recover is the content. A classifier gives
-- every small type a power presentation, the choices of a proxy at each
-- point (`classifier-gives-power-presentations`), and the power
-- presentation of the unit type is a classifier, each small type retained
-- as the constant predicate
-- (`power-presentation-of-the-unit-gives-classifier`): powers are exactly a
-- classifier. With weak resizing the proxies classify the types of the next
-- level too (`raised-types-are-classified`).

open import SPT.Base
open import SPT.Foundation.Impredicative.Classification using
  (Classifies; Resizing; Classifier; chosen; encode; decode)
open import SPT.Foundation.Impredicative.PropositionalClassifier using
  (Propositional-Classifier)

------------------------------------------------------------------------
-- The classifier of a level at propositions

classifier-gives-propositional-classifier : {ℓ : Level} →
  Classifier (λ (X : Set ℓ) → X) → Propositional-Classifier ℓ
classifier-gives-propositional-classifier C = record
  { proxies = Classifier.proxies C
  ; proxy = Classifier.proxy C
  ; classify = λ P h → Classifier.classify C P
  }

------------------------------------------------------------------------
-- Power presentations

record Power-Presentation {ℓ : Level} (A : Set ℓ) : Set (lsuc ℓ) where
  field
    Subsets : Set ℓ
    member : Subsets → A → Set ℓ
    retain : (A → Set ℓ) → Subsets
    recover : (X : A → Set ℓ) (a : A) →
      (X a → member (retain X) a) × (member (retain X) a → X a)

module _ {ℓ : Level} (C : Classifier (λ (X : Set ℓ) → X)) where

  -- The subsets of A are the choices of a proxy at each point of A.
  classifier-gives-power-presentations : (A : Set ℓ) → Power-Presentation A
  classifier-gives-power-presentations A = record
    { Subsets = A → Classifier.proxies C
    ; member = λ s a → Classifier.proxy C (s a)
    ; retain = λ X a → chosen C (X a)
    ; recover = λ X a → encode C (X a) , decode C (X a)
    }

  -- With weak resizing, a type of the next level is presented by a small
  -- type, which is classified.
  raised-types-are-classified : Resizing (λ (X : Set ℓ) → X) →
    Classifies (λ (P : Set (lsuc ℓ)) → P) (Classifier.proxy C)
  raised-types-are-classified r P =
    chosen C (pr₁ (r P)) ,
    (λ p → encode C (pr₁ (r P)) (pr₁ (pr₂ (r P)) p)) ,
    (λ q → pr₂ (pr₂ (r P)) (decode C (pr₁ (r P)) q))

-- The subsets of the unit type classify: a small type is retained as the
-- constant predicate, and its proxy is membership of the one point.
power-presentation-of-the-unit-gives-classifier : {ℓ : Level} →
  Power-Presentation (Lift ℓ 𝟙) → Classifier (λ (X : Set ℓ) → X)
power-presentation-of-the-unit-gives-classifier {ℓ} P = record
  { proxies = Power-Presentation.Subsets P
  ; proxy = λ s → Power-Presentation.member P s (lift ⋆)
  ; classify = λ X →
      Power-Presentation.retain P (λ (u : Lift ℓ 𝟙) → X) ,
      Power-Presentation.recover P (λ (u : Lift ℓ 𝟙) → X) (lift ⋆)
  }
