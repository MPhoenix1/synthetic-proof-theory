{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Covers.WeaklyInitial where

-- Weakly initial covers, in their section form. Weakly initial covers of a
-- type A are a small family of small types, each covering A, along one of
-- which every family of covered types over A has a section, as a covered
-- statement (`Weakly-Initial-Covers`):
--
--   index : Set ℓ,   domain : index → Set ℓ,
--   projection i : domain i → A,   each a cover,
--   Π (Y : A → Set ℓ). (Π x. Covered ℓ (Y x)) →
--     Covered ℓ (Σ (i : index). Π (z : domain i). Y (projection i z)).
--
-- A cover is refined by one of the projections, through the family of its
-- fibers (`refinements`). For a set A, a set of covers by sets
-- (`Weakly-Initial-Set-Covers`) is the weakly initial set of covers (WISC)
-- that Fiore, Pitts and Steenkamp use (LMCS 2022, §4); a choice of them for
-- every small set is global (`Global-Weakly-Initial-Set-Covers`), the form
-- they separate from mere existence for each set. A choice of weakly
-- initial covers for every small type is `Global-Weakly-Initial-Covers`.
-- Choice at a type, a covered section of every family of covered types
-- over it (`Projective`), gives the identity cover alone
-- (`projective-types-have-weakly-initial-covers`), by sets at a set
-- (`projective-sets-have-weakly-initial-set-covers`), so choice for the
-- small sets gives global weakly initial covers by sets
-- (`choice-gives-weakly-initial-set-covers`). The forward map of an
-- isomorphism is a cover (`isomorphisms-are-covers`), and so is the first
-- projection of a family of covered types (`first-projections-cover`).

open import SPT.Base
open import SPT.Foundation.Covers using
  ( Covered; Cover; map-covered; split-covers-are-covers
  ; identity-is-cover )
open import SPT.Foundation.Fibers using (fiber)
open import SPT.Foundation.Isomorphisms using
  (_≅_; forward; backward; forward-backward)
open import SPT.Foundation.Propositions using
  (is-set; propositions-are-sets)

------------------------------------------------------------------------
-- Isomorphisms and first projections cover

module _ {ℓ μ κ : Level} {A : Set ℓ} {B : Set μ} where

  isomorphisms-are-covers : (e : A ≅ B) → Cover κ (forward e)
  isomorphisms-are-covers e =
    split-covers-are-covers {q = forward e}
      (λ y → backward e y , forward-backward e y)

module _ {ℓ κ : Level} {A : Set ℓ} (Y : A → Set ℓ) where

  first-projections-cover : ((x : A) → Covered κ (Y x)) →
    Cover κ (pr₁ {A = A} {B = Y})
  first-projections-cover covered x =
    map-covered (λ y → (x , y) , refl) (covered x)

------------------------------------------------------------------------
-- Weakly initial covers

record Weakly-Initial-Covers {ℓ : Level} (A : Set ℓ) : Set (lsuc ℓ) where
  field
    index : Set ℓ
    domain : index → Set ℓ
    projection : (i : index) → domain i → A
    projections-cover : (i : index) → Cover ℓ (projection i)
    sections : (Y : A → Set ℓ) → ((x : A) → Covered ℓ (Y x)) →
      Covered ℓ (Σ index (λ i → (z : domain i) → Y (projection i z)))

-- A set of covers by sets.
record Weakly-Initial-Set-Covers {ℓ : Level} (A : Set ℓ) :
  Set (lsuc ℓ) where
  field
    covers : Weakly-Initial-Covers A
    index-is-set : is-set (Weakly-Initial-Covers.index covers)
    domains-are-sets : (i : Weakly-Initial-Covers.index covers) →
      is-set (Weakly-Initial-Covers.domain covers i)

-- A choice of weakly initial covers for every small type.
Global-Weakly-Initial-Covers : (ℓ : Level) → Set (lsuc ℓ)
Global-Weakly-Initial-Covers ℓ = (A : Set ℓ) → Weakly-Initial-Covers A

-- A choice of weakly initial covers by sets for every small set.
Global-Weakly-Initial-Set-Covers : (ℓ : Level) → Set (lsuc ℓ)
Global-Weakly-Initial-Set-Covers ℓ =
  (A : Set ℓ) → is-set A → Weakly-Initial-Set-Covers A

-- Every cover is refined by a projection: a map over A from its domain.
module _ {ℓ : Level} {A : Set ℓ} (W : Weakly-Initial-Covers A) where

  open Weakly-Initial-Covers W

  refinements : (E : Set ℓ) (q : E → A) → Cover ℓ q →
    Covered ℓ
      (Σ index (λ i →
        Σ (domain i → E) (λ r → (z : domain i) → q (r z) ＝ projection i z)))
  refinements E q cover =
    map-covered
      (λ w → pr₁ w , (λ z → pr₁ (pr₂ w z)) , (λ z → pr₂ (pr₂ w z)))
      (sections (fiber q) cover)

------------------------------------------------------------------------
-- From choice

-- Mathematical shape: Π (Y : A → Set ℓ). (Π x. Covered ℓ (Y x)) →
-- Covered ℓ (Π x. Y x).
Projective : {ℓ : Level} → Set ℓ → Set (lsuc ℓ)
Projective {ℓ} A =
  (Y : A → Set ℓ) → ((x : A) → Covered ℓ (Y x)) → Covered ℓ ((x : A) → Y x)

module _ {ℓ : Level} {A : Set ℓ} where

  projective-types-have-weakly-initial-covers : Projective A →
    Weakly-Initial-Covers A
  projective-types-have-weakly-initial-covers choice = record
    { index = Lift ℓ 𝟙
    ; domain = λ i → A
    ; projection = λ i → id
    ; projections-cover = λ i → identity-is-cover
    ; sections = λ Y covered →
        map-covered (λ f → lift ⋆ , f) (choice Y covered)
    }

  projective-sets-have-weakly-initial-set-covers : is-set A → Projective A →
    Weakly-Initial-Set-Covers A
  projective-sets-have-weakly-initial-set-covers s choice = record
    { covers = projective-types-have-weakly-initial-covers choice
    ; index-is-set = propositions-are-sets (λ x y → refl)
    ; domains-are-sets = λ i → s
    }

choice-gives-weakly-initial-set-covers : {ℓ : Level} →
  ((A : Set ℓ) → is-set A → Projective A) →
  Global-Weakly-Initial-Set-Covers ℓ
choice-gives-weakly-initial-set-covers choice A s =
  projective-sets-have-weakly-initial-set-covers s (choice A s)
