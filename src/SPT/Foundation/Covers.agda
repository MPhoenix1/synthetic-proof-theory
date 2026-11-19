{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Covers where

-- A type `A` is covered at the universe level `κ` when it proves every
-- `κ`-small proposition that a point of `A` would prove:
--
--   Covered κ A = Π (P : Set κ). is-proposition P → (A → P) → P.
--
-- This is existence with nothing but propositions to observe it, stated
-- predicatively, with no truncation. A point covers its type, covers move along
-- maps and compose, a covered proposition has a point, and a covered type is
-- not refuted. Being covered is a proposition under function extensionality for
-- the three function types in its definition.
--
-- A map is a cover when each of its fibers is covered. A cover does not say
-- which point of a fiber covers a given point. It is used by descent: a family
-- of propositions over the target that holds at the image of every source point
-- holds everywhere. A split cover chooses a point in every fiber; it is a
-- cover, and a cover whose fibers are propositions splits. Identities,
-- composites, pullbacks and maps pointwise equal to covers are covers.

open import SPT.Base
open import SPT.Foundation.Propositions using (is-proposition)
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Fibers using (fiber)

------------------------------------------------------------------------
-- Covered types

Covered : {ℓ : Level} (κ : Level) → Set ℓ → Set (ℓ ⊔ lsuc κ)
Covered κ A = (P : Set κ) → is-proposition P → (A → P) → P

------------------------------------------------------------------------
-- Covers and split covers

module _ {ℓ μ : Level} {C : Set ℓ} {X : Set μ} where

  Cover : (κ : Level) → (C → X) → Set (ℓ ⊔ μ ⊔ lsuc κ)
  Cover κ q = (x : X) → Covered κ (fiber q x)

  Split-Cover : (C → X) → Set (ℓ ⊔ μ)
  Split-Cover q = (x : X) → fiber q x

------------------------------------------------------------------------
-- Pullbacks

module _ {ℓ κ μ : Level} {A : Set ℓ} {B : Set κ} {C : Set μ} where

  Pullback : (A → C) → (B → C) → Set (ℓ ⊔ κ ⊔ μ)
  Pullback q f = Σ B (λ b → fiber q (f b))

  pullback-base : (q : A → C) (f : B → C) → Pullback q f → B
  pullback-base q f (b , _) = b

------------------------------------------------------------------------
-- Covered types

module _ {ℓ κ : Level} {A : Set ℓ} where

  covered-by-point : A → Covered κ A
  covered-by-point a P proposition consequence = consequence a

  covered-agrees : (covered : Covered κ A) (a : A) (P : Set κ)
    (proposition : is-proposition P) (consequence : A → P) →
    covered P proposition consequence ＝ consequence a
  covered-agrees covered a P proposition consequence =
    proposition (covered P proposition consequence) (consequence a)

  covered-is-not-refuted : Covered κ A → ¬ ¬ A
  covered-is-not-refuted covered refutation =
    lower (covered (Lift κ 𝟘) lifted-𝟘-is-proposition
      (λ a → lift (refutation a)))
    where
    lifted-𝟘-is-proposition : is-proposition (Lift κ 𝟘)
    lifted-𝟘-is-proposition (lift ()) y

module _ {ℓ μ κ : Level} {A : Set ℓ} {B : Set μ} where

  map-covered : (A → B) → Covered κ A → Covered κ B
  map-covered f covered P proposition consequence =
    covered P proposition (consequence ∘ f)

  bind-covered : Covered κ A → (A → Covered κ B) → Covered κ B
  bind-covered covered next P proposition consequence =
    covered P proposition (λ a → next a P proposition consequence)

module _ {κ : Level} {P : Set κ} where

  extract-proposition : Covered κ P → is-proposition P → P
  extract-proposition covered proposition = covered P proposition id

------------------------------------------------------------------------
-- Being covered is a proposition

module _ {ℓ κ : Level} {A : Set ℓ} where

  being-covered-is-proposition :
    FunExt (Set κ) (λ R → is-proposition R → (A → R) → R) →
    ((R : Set κ) → FunExt (is-proposition R) (λ _ → (A → R) → R)) →
    ((R : Set κ) → FunExt (A → R) (λ _ → R)) →
    is-proposition (Covered κ A)
  being-covered-is-proposition types proofs maps c d =
    types c d (λ R →
      proofs R (c R) (d R) (λ proposition →
        maps R (c R proposition) (d R proposition) (λ consequence →
          proposition (c R proposition consequence)
            (d R proposition consequence))))

------------------------------------------------------------------------
-- Split covers and descent

--   Cover κ q    Π x. is-proposition (P x)    Π (c : C). P (q c)
--   ------------------------------------------------------------
--                          Π (x : X). P x

-- Each point of a fiber transports its value along its identification to `x`.
-- At an image point, and for a family that already holds everywhere, descent
-- returns the given value, since the values form a proposition.

module _ {ℓ μ κ : Level} {C : Set ℓ} {X : Set μ} {q : C → X} where

  split-covers-are-covers : Split-Cover q → Cover κ q
  split-covers-are-covers split x P proposition consequence =
    consequence (split x)

  fibers-of-covers-are-not-refuted : Cover κ q → (x : X) →
    ¬ ¬ fiber q x
  fibers-of-covers-are-not-refuted cover x =
    covered-is-not-refuted (cover x)

  descend : Cover κ q → (P : X → Set κ) →
    ((x : X) → is-proposition (P x)) →
    ((c : C) → P (q c)) → (x : X) → P x
  descend cover P proposition section x =
    cover x (P x) (proposition x)
      (λ (c , e) → transport P e (section c))

  descend-at-image : (cover : Cover κ q) (P : X → Set κ)
    (proposition : (x : X) → is-proposition (P x))
    (section : (c : C) → P (q c)) (c : C) →
    descend cover P proposition section (q c) ＝ section c
  descend-at-image cover P proposition section c =
    proposition (q c) (descend cover P proposition section (q c))
      (section c)

  descend-precomposed : (cover : Cover κ q) (P : X → Set κ)
    (proposition : (x : X) → is-proposition (P x))
    (everywhere : (x : X) → P x) (x : X) →
    descend cover P proposition (λ c → everywhere (q c)) x
      ＝ everywhere x
  descend-precomposed cover P proposition everywhere x =
    proposition x
      (descend cover P proposition (λ c → everywhere (q c)) x)
      (everywhere x)

module _ {ℓ μ : Level} {C : Set ℓ} {X : Set μ} {q : C → X} where

  cover-with-propositional-fibers-splits : Cover (ℓ ⊔ μ) q →
    ((x : X) → is-proposition (fiber q x)) → Split-Cover q
  cover-with-propositional-fibers-splits cover fibers x =
    extract-proposition (cover x) (fibers x)

------------------------------------------------------------------------
-- Identities, composites, pullbacks, homotopies

module _ {μ κ : Level} {X : Set μ} where

  identity-is-cover : Cover κ (id {A = X})
  identity-is-cover x P proposition consequence = consequence (x , refl)

module _ {ℓ ν μ κ : Level} {A : Set ℓ} {B : Set ν} {C : Set μ}
  {f : A → B} {g : B → C} where

  composite-of-covers-is-cover : Cover κ f → Cover κ g → Cover κ (g ∘ f)
  composite-of-covers-is-cover first second z P proposition consequence =
    second z P proposition (λ (b , e) →
      first b P proposition (λ (a , e′) →
        consequence (a , ap g e′ ∙ e)))

module _ {ℓ ν μ κ : Level} {A : Set ℓ} {B : Set ν} {C : Set μ}
  {q : A → C} where

  pullback-of-cover-is-cover : Cover κ q → (f : B → C) →
    Cover κ (pullback-base q f)
  pullback-of-cover-is-cover cover f b P proposition consequence =
    cover (f b) P proposition (λ (a , e) →
      consequence ((b , (a , e)) , refl))

module _ {ℓ ν κ : Level} {A : Set ℓ} {B : Set ν} {f g : A → B} where

  cover-respects-homotopy : ((a : A) → f a ＝ g a) →
    Cover κ f → Cover κ g
  cover-respects-homotopy homotopy cover b P proposition consequence =
    cover b P proposition (λ (a , e) →
      consequence (a , homotopy a ⁻¹ ∙ e))
