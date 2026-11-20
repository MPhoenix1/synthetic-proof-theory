{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Heights.Presentation where

-- Every presented ordinal lies below the closure height. A presentation P
-- of level ℓ (Ordinal Geometry's Countable-Ordinal𝒫, with its ranks from
-- Height.Presentation) is simulated by derivations. The name of a point x
-- is the product over the natural-numbers code whose member at n is the
-- name of the n-th enumerated point if that point lies below x, and the
-- empty code otherwise; its derivation is built alongside (`name`,
-- `derivation`), read along the decoding law of the natural code
-- (`index-of`, `position`). The rank of each point lies below its
-- derivation's height (`dominates`), and the rank of P below the height of
-- the derivation over the whole enumeration (`dominates-whole`). So, under
-- the ambient rule and extensionality, every presentation's rank lies
-- strictly below the closure height of every operator (`presented-below`):
-- the derivable names close beyond every presented ordinal of their level.

open import SPT.Base
open import SPT.Foundation.Accessibility using (is-accessible; acc)
open import SPT.Foundation.Extensionality using (FunExt)
import SPT.Mahlo.Ambient as Ambient
open import SPT.Mahlo.Decoding using (DecodingLaws)
import SPT.Mahlo.Specification as Specification
open import SPT.Mahlo.DS.Cedents using
  (∅ᶜ; Derivable; empty; natural; product)
open import SPT.Mahlo.DS.Naming using (recast)
open import SPT.Mahlo.DS.Naming.Trees using (requests)
open import SPT.Mahlo.DS.Realization.Family using (cast)
open import SPT.Mahlo.Heights using
  (leaf; either; height; closing; below-closing)
open import SPT.OrdinalGeometry.Height.Ordinals using
  (Height; rank-at; rank; whole)
import SPT.OrdinalGeometry.Height.Presentation as Ranks
open import SPT.OrdinalGeometry.Height.Simulation using
  (_⊑_; _⊏_; below; under; ⊑-trans; ⊑-⊏-trans)
import SPT.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using (Countable-Ordinal𝒫)

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Specification.Formers C D) (Φ : Specification.Operator D)
  (laws : DecodingLaws Q) (P : Countable-Ordinal𝒫 ℓ)
  where

  open Countable-Ordinal𝒫 P using
    (X; _≈_; _<_; ≈-sym; <-respˡ-≈; <-wf; compare; enum; covers)

  ----------------------------------------------------------------------
  -- Positions of the natural code

  index-of : D (Specification.Formers.natural Q) → ℕ
  index-of m = lower (cast (DecodingLaws.natural-β laws) m)

  position : ℕ → D (Specification.Formers.natural Q)
  position n = cast (DecodingLaws.natural-β laws ⁻¹) (lift n)

  index-position : (n : ℕ) → index-of (position n) ＝ n
  index-position n =
    ap lower (recast (DecodingLaws.natural-β laws) (lift n))

  ----------------------------------------------------------------------
  -- Names and derivations of the points

  choose-name :
    (x r : X) → ((y : X) → y < x → C) → Trichotomy _≈_ _<_ r x → C
  choose-name x r k (inl r<x) = k r r<x
  choose-name x r k (inr _) = Specification.Formers.empty Q

  pick-name : (x : X) → ((y : X) → y < x → C) → Maybe X → C
  pick-name x k nothing = Specification.Formers.empty Q
  pick-name x k (just r) = choose-name x r k (compare r x)

  name : (x : X) → is-accessible _<_ x → C
  name x (acc smaller) =
    Specification.Formers.product Q
      ( Specification.Formers.natural Q
      , (λ m →
          pick-name x (λ y y<x → name y (smaller y y<x)) (enum (index-of m))))

  choose-derivation :
    (x r : X) (k : (y : X) → y < x → C)
    → ((y : X) (y<x : y < x) → Derivable Q Φ ∅ᶜ (k y y<x))
    → (o : Trichotomy _≈_ _<_ r x)
    → Derivable Q Φ ∅ᶜ (choose-name x r k o)
  choose-derivation x r k kd (inl r<x) = kd r r<x
  choose-derivation x r k kd (inr _) = empty

  pick-derivation :
    (x : X) (k : (y : X) → y < x → C)
    → ((y : X) (y<x : y < x) → Derivable Q Φ ∅ᶜ (k y y<x))
    → (o : Maybe X) → Derivable Q Φ ∅ᶜ (pick-name x k o)
  pick-derivation x k kd nothing = empty
  pick-derivation x k kd (just r) =
    choose-derivation x r k kd (compare r x)

  derivation : (x : X) (a : is-accessible _<_ x) → Derivable Q Φ ∅ᶜ (name x a)
  derivation x (acc smaller) =
    product (Specification.Formers.natural Q)
      (λ m →
        pick-name x (λ y y<x → name y (smaller y y<x)) (enum (index-of m)))
      natural
      (λ m →
        pick-derivation x (λ y y<x → name y (smaller y y<x))
          (λ y y<x → derivation y (smaller y y<x)) (enum (index-of m)))

  ----------------------------------------------------------------------
  -- Domination

  -- A point y below x is enumerated at some n by a point r ≈ y; the
  -- comparison then selects r < x, and the other outcomes contradict
  -- y < x.

  mutual
    dominates :
      (x : X) (a b : is-accessible _<_ x)
      → rank-at _<_ x a ⊑ height (derivation x b)
    dominates x (acc smaller) (acc smaller') =
      below
        (λ p →
          enumerated x smaller smaller' (pr₁ p) (pr₂ p)
            (pr₁ (covers (pr₁ p)))
            (pr₁ (pr₂ (covers (pr₁ p))))
            (pr₁ (pr₂ (pr₂ (covers (pr₁ p)))))
            (pr₂ (pr₂ (pr₂ (covers (pr₁ p))))))

    enumerated :
      (x : X) (smaller smaller' : (y : X) → y < x → is-accessible _<_ y)
      (y : X) (y<x : y < x) (n : ℕ) (r : X) (e : enum n ＝ just r)
      (r≈y : r ≈ y)
      → rank-at _<_ y (smaller y y<x) ⊏ height (derivation x (acc smaller'))
    enumerated x smaller smaller' y y<x n r e r≈y =
      under (inr (position n))
        (transport
          (λ o →
            rank-at _<_ y (smaller y y<x)
              ⊑ height
                  (pick-derivation x (λ z z<x → name z (smaller' z z<x))
                    (λ z z<x → derivation z (smaller' z z<x)) o))
          ((ap enum (index-position n) ∙ e) ⁻¹)
          (chosen x smaller smaller' y r y<x r≈y (compare r x)))

    chosen :
      (x : X) (smaller smaller' : (y : X) → y < x → is-accessible _<_ y)
      (y r : X) (y<x : y < x) (r≈y : r ≈ y)
      (o : Trichotomy _≈_ _<_ r x)
      → rank-at _<_ y (smaller y y<x)
        ⊑ height
            (choose-derivation x r (λ z z<x → name z (smaller' z z<x))
              (λ z z<x → derivation z (smaller' z z<x)) o)
    chosen x smaller smaller' y r y<x r≈y (inl r<x) =
      ⊑-trans
        (Ranks.rank-at-equivalent P y r (≈-sym r≈y) (smaller y y<x)
          (smaller r (<-respˡ-≈ (≈-sym r≈y) y<x)))
        (dominates r (smaller r (<-respˡ-≈ (≈-sym r≈y) y<x))
          (smaller' r r<x))
    chosen x smaller smaller' y r y<x r≈y (inr (inl r≈x)) =
      𝟘-elim
        (Presented.Presentation.≈↛< P r≈x (<-respˡ-≈ (≈-sym r≈y) y<x))
    chosen x smaller smaller' y r y<x r≈y (inr (inr x<r)) =
      𝟘-elim
        (Presented.Presentation.<-asym P (<-respˡ-≈ (≈-sym r≈y) y<x) x<r)

  ----------------------------------------------------------------------
  -- The whole presentation

  pick-all-name : Maybe X → C
  pick-all-name nothing = Specification.Formers.empty Q
  pick-all-name (just r) = name r (<-wf r)

  pick-all-derivation :
    (o : Maybe X) → Derivable Q Φ ∅ᶜ (pick-all-name o)
  pick-all-derivation nothing = empty
  pick-all-derivation (just r) = derivation r (<-wf r)

  whole-name : C
  whole-name =
    Specification.Formers.product Q
      ( Specification.Formers.natural Q
      , (λ m → pick-all-name (enum (index-of m))))

  whole-derivation : Derivable Q Φ ∅ᶜ whole-name
  whole-derivation =
    product (Specification.Formers.natural Q)
      (λ m → pick-all-name (enum (index-of m))) natural
      (λ m → pick-all-derivation (enum (index-of m)))

  covered :
    (x : X) (n : ℕ) (r : X) (e : enum n ＝ just r) (r≈x : r ≈ x)
    → rank _<_ <-wf x ⊏ height whole-derivation
  covered x n r e r≈x =
    under (inr (position n))
      (transport (λ o → rank _<_ <-wf x ⊑ height (pick-all-derivation o))
        ((ap enum (index-position n) ∙ e) ⁻¹)
        (⊑-trans
          (Ranks.rank-at-equivalent P x r (≈-sym r≈x) (<-wf x) (<-wf r))
          (dominates r (<-wf r) (<-wf r))))

  dominates-whole : whole _<_ <-wf ⊑ height whole-derivation
  dominates-whole =
    below
      (λ x →
        covered x (pr₁ (covers x)) (pr₁ (pr₂ (covers x)))
          (pr₁ (pr₂ (pr₂ (covers x))))
          (pr₂ (pr₂ (pr₂ (covers x)))))

  ----------------------------------------------------------------------
  -- Below the closure height

  presented-below :
    (extensionality : (X : Set ℓ) → FunExt X (λ _ → C))
    {K : Set ℓ}
    (L : Specification.Closure (Ambient.formers ℓ) (requests Q Φ) K)
    → whole _<_ <-wf ⊏ closing Q Φ L
  presented-below extensionality L =
    ⊑-⊏-trans dominates-whole
      (below-closing Q Φ L extensionality whole-derivation)
