{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.WellFounded.Stable where

-- Orders well-founded for ¬¬-stable propositions. A relation is stably
-- well-founded when induction along it proves every ¬¬-stable proposition
-- (`is-stably-well-founded`); a well-founded relation is
-- (`well-founded-relations-are-stably-well-founded`). A stably well-founded
-- order is a transitive relation valued in propositions and stably
-- well-founded (`Stably-Well-Founded-Order`). The points below a point form
-- one (`segment`); an order isomorphism (`Order-Isomorphism`) restricts to
-- segments (`restricted-isomorphism`), and a segment of a segment is a
-- segment (`segment-of-segment`).

open import SPT.Base
open import SPT.Foundation.Accessibility using
  (is-accessible; acc; is-well-founded)
open import SPT.Foundation.Extensionality using (FunExt; Π-is-proposition)
open import SPT.Foundation.Isomorphisms using
  ( _≅_; forward; backward; backward-forward; forward-backward
  ; ≅-refl; ≅-sym; ≅-trans)
open import SPT.Foundation.Propositions using (is-proposition)

------------------------------------------------------------------------
-- Stable well-foundedness

-- Induction is asked only for ¬¬-stable propositions; at an accessible
-- point it holds for every predicate.

module _ {ℓ : Level} {A : Set ℓ} where

  is-stably-well-founded : (A → A → Set ℓ) → Set (lsuc ℓ)
  is-stably-well-founded _<_ =
    (P : A → Set ℓ) → ((x : A) → is-proposition (P x)) →
    ((x : A) → ¬ ¬ P x → P x) →
    ((x : A) → ((y : A) → y < x → P y) → P x) → (x : A) → P x

module _ {ℓ : Level} {A : Set ℓ} (_<_ : A → A → Set ℓ) where

  induction-at-accessible-points : (P : A → Set ℓ) →
    ((x : A) → ((y : A) → y < x → P y) → P x) →
    (x : A) → is-accessible _<_ x → P x
  induction-at-accessible-points P step x (acc h) =
    step x (λ y r → induction-at-accessible-points P step y (h y r))

  well-founded-relations-are-stably-well-founded :
    is-well-founded _<_ → is-stably-well-founded _<_
  well-founded-relations-are-stably-well-founded wf P propositions stable
    step x =
    induction-at-accessible-points P step x (wf x)

------------------------------------------------------------------------
-- Stably well-founded orders

record Stably-Well-Founded-Order (ℓ : Level) : Set (lsuc ℓ) where
  field
    carrier : Set ℓ
    relation : carrier → carrier → Set ℓ
    relation-is-a-proposition : (x y : carrier) →
      is-proposition (relation x y)
    relation-is-transitive : (x y z : carrier) →
      relation x y → relation y z → relation x z
    relation-is-stably-well-founded : is-stably-well-founded relation

module _ {ℓ : Level} (O : Stably-Well-Founded-Order ℓ) where

  Points : Set ℓ
  Points = Stably-Well-Founded-Order.carrier O

precedes : {ℓ : Level} (O : Stably-Well-Founded-Order ℓ) →
  Points O → Points O → Set ℓ
precedes O = Stably-Well-Founded-Order.relation O

infix 30 precedes
syntax precedes O x y = x ≺⟨ O ⟩ y

module _ {ℓ : Level} (O : Stably-Well-Founded-Order ℓ) where

  precedence-is-a-proposition : (x y : Points O) →
    is-proposition (x ≺⟨ O ⟩ y)
  precedence-is-a-proposition =
    Stably-Well-Founded-Order.relation-is-a-proposition O

  precedence-is-transitive : (x y z : Points O) →
    x ≺⟨ O ⟩ y → y ≺⟨ O ⟩ z → x ≺⟨ O ⟩ z
  precedence-is-transitive =
    Stably-Well-Founded-Order.relation-is-transitive O

  stable-induction : is-stably-well-founded (precedes O)
  stable-induction =
    Stably-Well-Founded-Order.relation-is-stably-well-founded O

  precedence-along : {x x′ y y′ : Points O} → x ＝ x′ → y ＝ y′ →
    x ≺⟨ O ⟩ y → x′ ≺⟨ O ⟩ y′
  precedence-along refl refl r = r

------------------------------------------------------------------------
-- Segments

-- The points below a. A predicate on them is read on the order as
-- Π (p : x ≺ a). P (x , p), so induction passes to the segment.

module _ {ℓ : Level} (O : Stably-Well-Founded-Order ℓ) (a : Points O) where

  points-below-are-identified :
    {u v : Σ (Points O) (λ x → x ≺⟨ O ⟩ a)} → pr₁ u ＝ pr₁ v → u ＝ v
  points-below-are-identified {u} {v} e =
    to-Σ-＝ e
      (precedence-is-a-proposition O (pr₁ v) a
        (transport (λ x → x ≺⟨ O ⟩ a) e (pr₂ u)) (pr₂ v))

module _ {ℓ : Level}
  (extensionality : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y)
  (O : Stably-Well-Founded-Order ℓ) where

  segments-are-stably-well-founded : (a : Points O) →
    is-stably-well-founded
      (λ (u v : Σ (Points O) (λ x → x ≺⟨ O ⟩ a)) → pr₁ u ≺⟨ O ⟩ pr₁ v)
  segments-are-stably-well-founded a P propositions stable step u =
    stable-induction O
      (λ x → (p : x ≺⟨ O ⟩ a) → P (x , p))
      (λ x → Π-is-proposition
        (extensionality (x ≺⟨ O ⟩ a) (λ p → P (x , p)))
        (λ p → propositions (x , p)))
      (λ x k p → stable (x , p) (λ n → k (λ f → n (f p))))
      (λ x h p → step (x , p) (λ v r → h (pr₁ v) r (pr₂ v)))
      (pr₁ u) (pr₂ u)

  -- Mathematical shape: O↓a = Σ (x : O). x ≺ a, ordered as in O.
  segment : Points O → Stably-Well-Founded-Order ℓ
  segment a = record
    { carrier = Σ (Points O) (λ x → x ≺⟨ O ⟩ a)
    ; relation = λ u v → pr₁ u ≺⟨ O ⟩ pr₁ v
    ; relation-is-a-proposition = λ u v →
        precedence-is-a-proposition O (pr₁ u) (pr₁ v)
    ; relation-is-transitive = λ u v w →
        precedence-is-transitive O (pr₁ u) (pr₁ v) (pr₁ w)
    ; relation-is-stably-well-founded = segments-are-stably-well-founded a
    }

------------------------------------------------------------------------
-- Order isomorphisms

-- An isomorphism of points that preserves and reflects precedence. They
-- have identities, inverses and composites.

module _ {ℓ : Level} (O O′ : Stably-Well-Founded-Order ℓ) where

  record Order-Isomorphism : Set ℓ where
    field
      points-isomorphism : Points O ≅ Points O′
      preserves : (x y : Points O) → x ≺⟨ O ⟩ y →
        forward points-isomorphism x ≺⟨ O′ ⟩ forward points-isomorphism y
      reflects : (x y : Points O) →
        forward points-isomorphism x ≺⟨ O′ ⟩ forward points-isomorphism y →
        x ≺⟨ O ⟩ y

open Order-Isomorphism public

module _ {ℓ : Level} (O : Stably-Well-Founded-Order ℓ) where

  identity-isomorphism : Order-Isomorphism O O
  identity-isomorphism = record
    { points-isomorphism = ≅-refl
    ; preserves = λ x y r → r
    ; reflects = λ x y r → r
    }

module _ {ℓ : Level} {O O′ : Stably-Well-Founded-Order ℓ} where

  inverse-isomorphism : Order-Isomorphism O O′ → Order-Isomorphism O′ O
  inverse-isomorphism φ = record
    { points-isomorphism = ≅-sym (points-isomorphism φ)
    ; preserves = λ x y r →
        reflects φ (backward (points-isomorphism φ) x)
          (backward (points-isomorphism φ) y)
          (precedence-along O′
            (forward-backward (points-isomorphism φ) x ⁻¹)
            (forward-backward (points-isomorphism φ) y ⁻¹) r)
    ; reflects = λ x y r →
        precedence-along O′ (forward-backward (points-isomorphism φ) x)
          (forward-backward (points-isomorphism φ) y)
          (preserves φ (backward (points-isomorphism φ) x)
            (backward (points-isomorphism φ) y) r)
    }

module _ {ℓ : Level} {O O′ O″ : Stably-Well-Founded-Order ℓ} where

  composite-isomorphism : Order-Isomorphism O O′ →
    Order-Isomorphism O′ O″ → Order-Isomorphism O O″
  composite-isomorphism φ ψ = record
    { points-isomorphism =
        ≅-trans (points-isomorphism φ) (points-isomorphism ψ)
    ; preserves = λ x y r →
        preserves ψ (forward (points-isomorphism φ) x)
          (forward (points-isomorphism φ) y) (preserves φ x y r)
    ; reflects = λ x y r →
        reflects φ x y
          (reflects ψ (forward (points-isomorphism φ) x)
            (forward (points-isomorphism φ) y) r)
    }

------------------------------------------------------------------------
-- Isomorphisms of segments

-- An isomorphism maps the points below a onto the points below its image
-- of a. The points below b in O↓a are the points below b in O, since b is
-- below a.

module _ {ℓ : Level}
  (extensionality : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y)
  {O O′ : Stably-Well-Founded-Order ℓ} (φ : Order-Isomorphism O O′) where

  -- Mathematical shape: O↓a ≅ O′↓(φ a).
  restricted-isomorphism : (a : Points O) →
    Order-Isomorphism (segment extensionality O a)
      (segment extensionality O′ (forward (points-isomorphism φ) a))
  restricted-isomorphism a = record
    { points-isomorphism = record
        { forward = λ u →
            forward (points-isomorphism φ) (pr₁ u) ,
            preserves φ (pr₁ u) a (pr₂ u)
        ; backward = λ v →
            backward (points-isomorphism φ) (pr₁ v) ,
            reflects φ (backward (points-isomorphism φ) (pr₁ v)) a
              (precedence-along O′
                (forward-backward (points-isomorphism φ) (pr₁ v) ⁻¹) refl
                (pr₂ v))
        ; backward-forward = λ u →
            points-below-are-identified O a
              (backward-forward (points-isomorphism φ) (pr₁ u))
        ; forward-backward = λ v →
            points-below-are-identified O′ (forward (points-isomorphism φ) a)
              (forward-backward (points-isomorphism φ) (pr₁ v))
        }
    ; preserves = λ u v r → preserves φ (pr₁ u) (pr₁ v) r
    ; reflects = λ u v r → reflects φ (pr₁ u) (pr₁ v) r
    }

module _ {ℓ : Level}
  (extensionality : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y)
  (O : Stably-Well-Founded-Order ℓ) (a : Points O) where

  -- Mathematical shape: (O↓a)↓b ≅ O↓b.
  segment-of-segment : (b : Points (segment extensionality O a)) →
    Order-Isomorphism
      (segment extensionality (segment extensionality O a) b)
      (segment extensionality O (pr₁ b))
  segment-of-segment b = record
    { points-isomorphism = record
        { forward = λ w → pr₁ (pr₁ w) , pr₂ w
        ; backward = λ v →
            ( pr₁ v
            , precedence-is-transitive O (pr₁ v) (pr₁ b) a (pr₂ v) (pr₂ b))
            , pr₂ v
        ; backward-forward = λ w →
            ap (λ p → (pr₁ (pr₁ w) , p) , pr₂ w)
              (precedence-is-a-proposition O (pr₁ (pr₁ w)) a
                (precedence-is-transitive O (pr₁ (pr₁ w)) (pr₁ b) a
                  (pr₂ w) (pr₂ b))
                (pr₂ (pr₁ w)))
        ; forward-backward = λ v → refl
        }
    ; preserves = λ w w′ r → r
    ; reflects = λ w w′ r → r
    }
