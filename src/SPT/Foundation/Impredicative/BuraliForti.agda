{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Impredicative.BuraliForti where

-- Burali-Forti for stably well-founded orders, read through double
-- negation. An order type is a ¬¬-stable predicate on the orders of level ℓ
-- that is doubly not the class of an order under ¬¬-isomorphism
-- (`Order-Types`); the order types form a ¬¬-separated set. Ordered by
-- being, doubly not, isomorphic to segments of one another, they are stably
-- well-founded (`order-types-are-stably-well-founded`). Under function
-- extensionality at ℓ and ℓ + 1, propositional extensionality at ℓ and
-- propositional resizing (`Hypotheses`) they are not small
-- (`order-types-are-not-small`): a small presentation of them is an order,
-- whose segments have types increasing strictly and below its own. So under
-- propositional extensionality at ℓ and univalence at ℓ + 1, small
-- identifications give a large separated set (`separated-largeness`) and
-- are contradictory (`small-identifications-are-contradictory`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt; Π-is-proposition)
open import SPT.Foundation.Extensionality.Levels using (funext-below)
open import SPT.Foundation.Impredicative.PropositionalResizing using
  (Propositional-Resizing)
open import SPT.Foundation.Impredicative.SmallIdentifications using
  ( Small-Identifications; Large-Separated-Set; Separated-Largeness
  ; small-identifications-give-resizing
  ; separated-largeness-refutes-small-identifications)
open import SPT.Foundation.Isomorphisms using
  (_≅_; forward; backward; backward-forward; forward-backward; ≅-sym)
open import SPT.Foundation.Modalities using
  (Stable-Proposition; double-negation-modality; modal-proposition)
open import SPT.Foundation.Modalities.Biconditional using
  (stable-propositions-are-identified; stable-propositions-form-a-set)
open import SPT.Foundation.Propositions using
  (is-proposition; is-set; 𝟘-is-proposition; propositions-are-sets)
open import SPT.Foundation.Propositions.Closure using
  (isomorphic-to-a-proposition)
open import SPT.Foundation.Propositions.Extensionality using
  (Propositional-Extensionality)
open import SPT.Foundation.Sets using
  (products-of-sets-are-sets; sums-of-sets-are-sets)
open import SPT.Foundation.Size using (is-small)
open import SPT.Foundation.Univalence using
  (is-univalent; equivalence-to-isomorphism; funext-from-univalence)
open import SPT.Foundation.WellFounded.Stable using
  ( is-stably-well-founded; Stably-Well-Founded-Order; Points; precedes
  ; stable-induction; segment; Order-Isomorphism; points-isomorphism
  ; identity-isomorphism; inverse-isomorphism; composite-isomorphism
  ; restricted-isomorphism; segment-of-segment)

------------------------------------------------------------------------
-- Hypotheses

-- Function extensionality at ℓ and ℓ + 1, propositional extensionality at ℓ
-- and propositional resizing. Univalence at ℓ + 1 gives the function
-- extensionality at both levels (`hypotheses`).

record Hypotheses (ℓ : Level) : Set (lsuc (lsuc ℓ)) where
  field
    dn : (X : Set ℓ) → FunExt (¬ X) (λ _ → 𝟘)
    extensionality₀ : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y
    extensionality₁ : (X : Set (lsuc ℓ)) (Y : X → Set (lsuc ℓ)) → FunExt X Y
    negation₁ : (X : Set (lsuc ℓ)) → FunExt X (λ _ → 𝟘)
    pe₀ : Propositional-Extensionality ℓ
    resize : Propositional-Resizing ℓ

hypotheses : {ℓ : Level} → Propositional-Extensionality ℓ →
  is-univalent (lsuc ℓ) → Propositional-Resizing ℓ → Hypotheses ℓ
hypotheses {ℓ} pe u₁ r = record
  { dn = λ X →
      funext-below (lsuc ℓ) (λ A B → funext-from-univalence A B u₁ u₁)
        (¬ X) (λ _ → 𝟘)
  ; extensionality₀ = λ X Y →
      funext-below (lsuc ℓ) (λ A B → funext-from-univalence A B u₁ u₁) X Y
  ; extensionality₁ = λ X Y → funext-from-univalence X Y u₁ u₁
  ; negation₁ = λ X → funext-from-univalence X (λ _ → 𝟘) u₁ u₁
  ; pe₀ = pe
  ; resize = r
  }

------------------------------------------------------------------------
-- Isomorphism classes

-- The class of α holds at β when β is doubly not isomorphic to α.
-- Isomorphic orders have one class, and equal classes make their orders
-- doubly not isomorphic.

module _ {ℓ : Level} (H : Hypotheses ℓ) where

  open Hypotheses H

  isomorphism-class : Stably-Well-Founded-Order ℓ →
    Stably-Well-Founded-Order ℓ →
    Stable-Proposition (double-negation-modality dn)
  isomorphism-class α β =
    modal-proposition (double-negation-modality dn) (Order-Isomorphism β α)

  classes-of-isomorphic-orders-agree : (α β : Stably-Well-Founded-Order ℓ) →
    Order-Isomorphism α β → isomorphism-class α ＝ isomorphism-class β
  classes-of-isomorphic-orders-agree α β φ =
    extensionality₁ (Stably-Well-Founded-Order ℓ)
      (λ _ → Stable-Proposition (double-negation-modality dn))
      (isomorphism-class α) (isomorphism-class β)
      (λ γ → stable-propositions-are-identified dn extensionality₀ pe₀
        (isomorphism-class α γ) (isomorphism-class β γ)
        (λ k n → k (λ χ → n (composite-isomorphism χ φ)))
        (λ k n → k (λ χ → n (composite-isomorphism χ (inverse-isomorphism φ)))))

  isomorphic-by-classes : (γ δ : Stably-Well-Founded-Order ℓ) →
    isomorphism-class δ ＝ isomorphism-class γ → ¬ ¬ Order-Isomorphism γ δ
  isomorphic-by-classes γ δ e =
    transport (λ P → Stable-Proposition.carrier (P γ)) (e ⁻¹)
      (λ n → n (identity-isomorphism γ))

------------------------------------------------------------------------
-- Order types

-- An order type is a stable predicate on orders that is doubly not the class
-- of an order. The order types form a set, and a ¬¬-separated one: two of
-- them agree at each order when they doubly do, their values being stable.

module _ {ℓ : Level} (H : Hypotheses ℓ) where

  open Hypotheses H

  is-an-order-type :
    (Stably-Well-Founded-Order ℓ →
      Stable-Proposition (double-negation-modality dn)) → Set (lsuc ℓ)
  is-an-order-type P =
    ¬ ¬ Σ (Stably-Well-Founded-Order ℓ) (λ α → P ＝ isomorphism-class H α)

  -- Mathematical shape: Σ (P : Orders → Ω¬¬). ¬¬ Σ α. P ＝ [α].
  Order-Types : Set (lsuc ℓ)
  Order-Types =
    Σ (Stably-Well-Founded-Order ℓ →
        Stable-Proposition (double-negation-modality dn))
      is-an-order-type

  order-type : Stably-Well-Founded-Order ℓ → Order-Types
  order-type α = isomorphism-class H α , (λ n → n (α , refl))

  being-an-order-type-is-a-proposition :
    (P : Stably-Well-Founded-Order ℓ →
      Stable-Proposition (double-negation-modality dn)) →
    is-proposition (is-an-order-type P)
  being-an-order-type-is-a-proposition P =
    Π-is-proposition
      (negation₁
        (¬ Σ (Stably-Well-Founded-Order ℓ)
          (λ α → P ＝ isomorphism-class H α)))
      (λ _ → 𝟘-is-proposition)

  order-types-are-identified : (q r : Order-Types) → pr₁ q ＝ pr₁ r → q ＝ r
  order-types-are-identified q r e =
    to-Σ-＝ e
      (being-an-order-type-is-a-proposition (pr₁ r)
        (transport is-an-order-type e (pr₂ q)) (pr₂ r))

  -- An order type at the class of β is the type of each order isomorphic
  -- to β.
  order-type-of-an-isomorphic-order : (q : Order-Types)
    (β δ : Stably-Well-Founded-Order ℓ) →
    pr₁ q ＝ isomorphism-class H β → Order-Isomorphism β δ →
    q ＝ order-type δ
  order-type-of-an-isomorphic-order q β δ e φ =
    order-types-are-identified q (order-type δ)
      (e ∙ classes-of-isomorphic-orders-agree H β δ φ)

  order-types-form-a-set : is-set Order-Types
  order-types-form-a-set =
    sums-of-sets-are-sets
      (products-of-sets-are-sets extensionality₁
        (Stably-Well-Founded-Order ℓ)
        (λ _ → Stable-Proposition (double-negation-modality dn))
        (λ _ → stable-propositions-form-a-set dn extensionality₀ pe₀))
      (λ P → propositions-are-sets (being-an-order-type-is-a-proposition P))

  order-types-are-separated : (q r : Order-Types) → ¬ ¬ (q ＝ r) → q ＝ r
  order-types-are-separated q r k =
    order-types-are-identified q r
      (extensionality₁ (Stably-Well-Founded-Order ℓ)
        (λ _ → Stable-Proposition (double-negation-modality dn))
        (pr₁ q) (pr₁ r)
        (λ γ → stable-propositions-are-identified dn extensionality₀
          pe₀ (pr₁ q γ) (pr₁ r γ)
          (λ x → Stable-Proposition.carrier-is-stable (pr₁ r γ)
            (λ n → k (λ e → n
              (transport (λ s → Stable-Proposition.carrier (pr₁ s γ)) e x))))
          (λ y → Stable-Proposition.carrier-is-stable (pr₁ q γ)
            (λ n → k (λ e → n
              (transport (λ s → Stable-Proposition.carrier (pr₁ s γ))
                (e ⁻¹) y))))))

------------------------------------------------------------------------
-- The order of order types

-- One order type is below another when, doubly not, an order of the first
-- is isomorphic to a segment of an order of the second. It is transitive:
-- isomorphisms restrict to segments, and a segment of a segment is a
-- segment.

-- α is isomorphic to the segment of β below a point.
Segment-Of : {ℓ : Level} (H : Hypotheses ℓ) →
  Stably-Well-Founded-Order ℓ → Stably-Well-Founded-Order ℓ → Set ℓ
Segment-Of H α β =
  Σ (Points β)
    (λ b → Order-Isomorphism α (segment (Hypotheses.extensionality₀ H) β b))

infix 30 Segment-Of
syntax Segment-Of H α β = α ◁⟨ H ⟩ β

-- Orders of the two types, the first a segment of the second.
Below-Witness : {ℓ : Level} (H : Hypotheses ℓ) →
  Order-Types H → Order-Types H → Set (lsuc ℓ)
Below-Witness {ℓ} H q r =
  Σ (Stably-Well-Founded-Order ℓ) (λ α →
    Σ (Stably-Well-Founded-Order ℓ) (λ β →
      (pr₁ q ＝ isomorphism-class H α) ×
      (pr₁ r ＝ isomorphism-class H β) × α ◁⟨ H ⟩ β))

infix 30 Below-Witness
syntax Below-Witness H q r = q ◃⟨ H ⟩ r

-- Mathematical shape: q ⊲ r = ¬¬ Σ α β. q = [α] × r = [β] × α ≅ β↓b.
type-below : {ℓ : Level} (H : Hypotheses ℓ) →
  Order-Types H → Order-Types H → Set (lsuc ℓ)
type-below H q r = ¬ ¬ (q ◃⟨ H ⟩ r)

infix 30 type-below
syntax type-below H q r = q ⊲⟨ H ⟩ r

module _ {ℓ : Level} (H : Hypotheses ℓ) where

  open Hypotheses H

  ⊲-is-a-proposition : (q r : Order-Types H) →
    is-proposition (q ⊲⟨ H ⟩ r)
  ⊲-is-a-proposition q r =
    Π-is-proposition (negation₁ (¬ (q ◃⟨ H ⟩ r)))
      (λ _ → 𝟘-is-proposition)

  segments-compose : (α β β′ γ : Stably-Well-Founded-Order ℓ) →
    α ◁⟨ H ⟩ β → Order-Isomorphism β β′ → β′ ◁⟨ H ⟩ γ → α ◁⟨ H ⟩ γ
  segments-compose α β β′ γ (b , ψ) φ (c , χ) =
    pr₁ (forward (points-isomorphism χ) (forward (points-isomorphism φ) b)) ,
    composite-isomorphism ψ
      (composite-isomorphism (restricted-isomorphism extensionality₀ φ b)
        (composite-isomorphism
          (restricted-isomorphism extensionality₀ χ
            (forward (points-isomorphism φ) b))
          (segment-of-segment extensionality₀ γ c
            (forward (points-isomorphism χ)
              (forward (points-isomorphism φ) b)))))

  below-witnesses-compose : (q r s : Order-Types H) →
    q ◃⟨ H ⟩ r → r ◃⟨ H ⟩ s → q ⊲⟨ H ⟩ s
  below-witnesses-compose q r s (α , β , e₁ , e₂ , m)
    (β′ , γ , e₃ , e₄ , m′) n =
    isomorphic-by-classes H β β′ (e₃ ⁻¹ ∙ e₂)
      (λ φ → n (α , γ , e₁ , e₄ , segments-compose α β β′ γ m φ m′))

  ⊲-is-transitive : (q r s : Order-Types H) →
    q ⊲⟨ H ⟩ r → r ⊲⟨ H ⟩ s → q ⊲⟨ H ⟩ s
  ⊲-is-transitive q r s k l n =
    k (λ w → l (λ w′ → below-witnesses-compose q r s w w′ n))

------------------------------------------------------------------------
-- Stable well-foundedness

-- A stable progressive predicate Φ holds at the types of the segments of an
-- order, by stable induction along the order with Φ resized to level ℓ: an
-- order type below the type of α↓a is, doubly not, the type of α↓c for a
-- point c below a. So Φ holds at the type of every order and, being stable,
-- at every order type.

module _ {ℓ : Level} (H : Hypotheses ℓ) where

  open Hypotheses H

  module _ (Φ : Order-Types H → Set (lsuc ℓ))
    (propositions : (q : Order-Types H) → is-proposition (Φ q))
    (stable : (q : Order-Types H) → ¬ ¬ Φ q → Φ q)
    (step : (q : Order-Types H) →
      ((r : Order-Types H) → r ⊲⟨ H ⟩ q → Φ r) → Φ q)
    where

    doubly-holds-at-witnesses-below-a-segment :
      (α : Stably-Well-Founded-Order ℓ) (a : Points α) →
      ((c : Points α) → c ≺⟨ α ⟩ a →
        Φ (order-type H (segment extensionality₀ α c))) →
      (r : Order-Types H) →
      r ◃⟨ H ⟩ order-type H (segment extensionality₀ α a) → ¬ ¬ Φ r
    doubly-holds-at-witnesses-below-a-segment α a below r
      (β , γ , e₁ , e₂ , c′ , ψ) n =
      isomorphic-by-classes H γ (segment extensionality₀ α a) e₂
        (λ φ → n
          (transport Φ
            (order-type-of-an-isomorphic-order H r β
              (segment extensionality₀ α
                (pr₁ (forward (points-isomorphism φ) c′)))
              e₁
              (composite-isomorphism ψ
                (composite-isomorphism
                  (restricted-isomorphism extensionality₀ φ c′)
                  (segment-of-segment extensionality₀ α a
                    (forward (points-isomorphism φ) c′)))) ⁻¹)
            (below (pr₁ (forward (points-isomorphism φ) c′))
              (pr₂ (forward (points-isomorphism φ) c′)))))

    holds-below-the-type-of-a-segment :
      (α : Stably-Well-Founded-Order ℓ) (a : Points α) →
      ((c : Points α) → c ≺⟨ α ⟩ a →
        Φ (order-type H (segment extensionality₀ α c))) →
      (r : Order-Types H) →
      r ⊲⟨ H ⟩ order-type H (segment extensionality₀ α a) → Φ r
    holds-below-the-type-of-a-segment α a below r k =
      stable r
        (λ n → k (λ w →
          doubly-holds-at-witnesses-below-a-segment α a below r w n))

    resized-at-segment : (α : Stably-Well-Founded-Order ℓ) (a : Points α) →
      is-small ℓ (Φ (order-type H (segment extensionality₀ α a)))
    resized-at-segment α a =
      resize (Φ (order-type H (segment extensionality₀ α a)))
        (propositions (order-type H (segment extensionality₀ α a)))

    resized-at-segment-isomorphism : (α : Stably-Well-Founded-Order ℓ)
      (a : Points α) →
      pr₁ (resized-at-segment α a) ≅
        Φ (order-type H (segment extensionality₀ α a))
    resized-at-segment-isomorphism α a =
      equivalence-to-isomorphism (pr₂ (resized-at-segment α a))

    holds-at-types-of-segments : (α : Stably-Well-Founded-Order ℓ)
      (a : Points α) → Φ (order-type H (segment extensionality₀ α a))
    holds-at-types-of-segments α a =
      forward (resized-at-segment-isomorphism α a)
        (stable-induction α (λ c → pr₁ (resized-at-segment α c))
          (λ c → isomorphic-to-a-proposition
            (≅-sym (resized-at-segment-isomorphism α c))
            (propositions (order-type H (segment extensionality₀ α c))))
          (λ c k → backward (resized-at-segment-isomorphism α c)
            (stable (order-type H (segment extensionality₀ α c))
              (λ n → k (λ x → n
                (forward (resized-at-segment-isomorphism α c) x)))))
          (λ c h → backward (resized-at-segment-isomorphism α c)
            (step (order-type H (segment extensionality₀ α c))
              (holds-below-the-type-of-a-segment α c
                (λ d r → forward (resized-at-segment-isomorphism α d)
                  (h d r)))))
          a)

    doubly-holds-at-witnesses-below-an-order :
      (α : Stably-Well-Founded-Order ℓ) (r : Order-Types H) →
      r ◃⟨ H ⟩ order-type H α → ¬ ¬ Φ r
    doubly-holds-at-witnesses-below-an-order α r (β , γ , e₁ , e₂ , c′ , ψ)
      n =
      isomorphic-by-classes H γ α e₂
        (λ φ → n
          (transport Φ
            (order-type-of-an-isomorphic-order H r β
              (segment extensionality₀ α (forward (points-isomorphism φ) c′))
              e₁
              (composite-isomorphism ψ
                (restricted-isomorphism extensionality₀ φ c′)) ⁻¹)
            (holds-at-types-of-segments α
              (forward (points-isomorphism φ) c′))))

    holds-at-types-of-orders : (α : Stably-Well-Founded-Order ℓ) →
      Φ (order-type H α)
    holds-at-types-of-orders α =
      step (order-type H α)
        (λ r k → stable r
          (λ n → k (λ w →
            doubly-holds-at-witnesses-below-an-order α r w n)))

    holds-at-order-types : (q : Order-Types H) → Φ q
    holds-at-order-types q =
      stable q
        (λ n → pr₂ q (λ w → n
          (transport Φ
            (order-types-are-identified H (order-type H (pr₁ w)) q
              (pr₂ w ⁻¹))
            (holds-at-types-of-orders (pr₁ w)))))

  order-types-are-stably-well-founded :
    is-stably-well-founded (type-below H)
  order-types-are-stably-well-founded Φ propositions stable step =
    holds-at-order-types Φ propositions stable step

------------------------------------------------------------------------
-- Burali-Forti

-- A small presentation of the order types, ordered by their order resized,
-- is a stably well-founded order. The type of its segment at the
-- presentation of q increases strictly in q and lies below the type of the
-- presentation itself; by stable induction it lies below q for no q, which
-- fails at the type of the presentation.

module _ {ℓ : Level} (H : Hypotheses ℓ) where

  open Hypotheses H

  module _ (small : is-small ℓ (Order-Types H)) where

    presentation : pr₁ small ≅ Order-Types H
    presentation = equivalence-to-isomorphism (pr₂ small)

    presented-precedence-is-small : (l l′ : pr₁ small) →
      is-small ℓ (forward presentation l ⊲⟨ H ⟩ forward presentation l′)
    presented-precedence-is-small l l′ =
      resize (forward presentation l ⊲⟨ H ⟩ forward presentation l′)
        (⊲-is-a-proposition H (forward presentation l)
          (forward presentation l′))

    -- l precedes l′ when their order types do, at level ℓ.
    presented-precedence : pr₁ small → pr₁ small → Set ℓ
    presented-precedence l l′ = pr₁ (presented-precedence-is-small l l′)

    presented-precedence-isomorphism : (l l′ : pr₁ small) →
      presented-precedence l l′ ≅
        (forward presentation l ⊲⟨ H ⟩ forward presentation l′)
    presented-precedence-isomorphism l l′ =
      equivalence-to-isomorphism (pr₂ (presented-precedence-is-small l l′))

    presented-precedence-is-stably-well-founded :
      is-stably-well-founded presented-precedence
    presented-precedence-is-stably-well-founded P propositions stable step l =
      transport P (backward-forward presentation l)
        (lower
          (order-types-are-stably-well-founded H
            (λ q → Lift (lsuc ℓ) (P (backward presentation q)))
            (λ q x y → ap lift
              (propositions (backward presentation q) (lower x) (lower y)))
            (λ q k → lift
              (stable (backward presentation q)
                (λ n → k (λ x → n (lower x)))))
            (λ q h → lift
              (step (backward presentation q)
                (λ l′ r → transport P (backward-forward presentation l′)
                  (lower
                    (h (forward presentation l′)
                      (transport (λ s → forward presentation l′ ⊲⟨ H ⟩ s)
                        (forward-backward presentation q)
                        (forward
                          (presented-precedence-isomorphism l′
                            (backward presentation q))
                          r)))))))
            (forward presentation l)))

    presented-order : Stably-Well-Founded-Order ℓ
    presented-order = record
      { carrier = pr₁ small
      ; relation = presented-precedence
      ; relation-is-a-proposition = λ l l′ →
          isomorphic-to-a-proposition
            (≅-sym (presented-precedence-isomorphism l l′))
            (⊲-is-a-proposition H (forward presentation l)
              (forward presentation l′))
      ; relation-is-transitive = λ l l′ l″ r r′ →
          backward (presented-precedence-isomorphism l l″)
            (⊲-is-transitive H (forward presentation l)
              (forward presentation l′) (forward presentation l″)
              (forward (presented-precedence-isomorphism l l′) r)
              (forward (presented-precedence-isomorphism l′ l″) r′))
      ; relation-is-stably-well-founded =
          presented-precedence-is-stably-well-founded
      }

    presented-precedence-of-types : (q r : Order-Types H) → q ⊲⟨ H ⟩ r →
      backward presentation q ≺⟨ presented-order ⟩ backward presentation r
    presented-precedence-of-types q r k =
      backward
        (presented-precedence-isomorphism (backward presentation q)
          (backward presentation r))
        (transport
          (λ s → s ⊲⟨ H ⟩ forward presentation (backward presentation r))
          (forward-backward presentation q ⁻¹)
          (transport (λ s → q ⊲⟨ H ⟩ s) (forward-backward presentation r ⁻¹)
            k))

    -- The type of the segment of the presentation at q.
    segment-type : Order-Types H → Order-Types H
    segment-type q =
      order-type H
        (segment extensionality₀ presented-order (backward presentation q))

    segment-types-are-below : (q : Order-Types H) →
      segment-type q ⊲⟨ H ⟩ order-type H presented-order
    segment-types-are-below q n =
      n ( segment extensionality₀ presented-order (backward presentation q)
        , presented-order , refl , refl , backward presentation q
        , identity-isomorphism
            (segment extensionality₀ presented-order
              (backward presentation q)))

    segment-types-increase : (q r : Order-Types H) → q ⊲⟨ H ⟩ r →
      segment-type q ⊲⟨ H ⟩ segment-type r
    segment-types-increase q r k n =
      n ( segment extensionality₀ presented-order (backward presentation q)
        , segment extensionality₀ presented-order (backward presentation r)
        , refl , refl
        , (backward presentation q , presented-precedence-of-types q r k)
        , inverse-isomorphism
            (segment-of-segment extensionality₀ presented-order
              (backward presentation r)
              (backward presentation q , presented-precedence-of-types q r k)))

    no-segment-type-is-below-its-order-type : (q : Order-Types H) →
      ¬ (segment-type q ⊲⟨ H ⟩ q)
    no-segment-type-is-below-its-order-type =
      order-types-are-stably-well-founded H
        (λ q → ¬ (segment-type q ⊲⟨ H ⟩ q))
        (λ q → Π-is-proposition (negation₁ (segment-type q ⊲⟨ H ⟩ q))
          (λ _ → 𝟘-is-proposition))
        (λ q k m → k (λ n → n m))
        (λ q below m → below (segment-type q) m
          (segment-types-increase (segment-type q) q m))

    order-types-are-not-small : 𝟘
    order-types-are-not-small =
      no-segment-type-is-below-its-order-type (order-type H presented-order)
        (segment-types-are-below (order-type H presented-order))

------------------------------------------------------------------------
-- Small identifications

-- Under resizing the order types are a large separated set. Small
-- identifications give resizing, so they give one, which refutes them.

module _ {ℓ : Level} (H : Hypotheses ℓ) where

  order-types-form-a-large-separated-set : Large-Separated-Set ℓ
  order-types-form-a-large-separated-set = record
    { separated-set = record
        { points = Order-Types H
        ; points-form-a-set = order-types-form-a-set H
        ; points-are-separated = order-types-are-separated H
        }
    ; not-small = order-types-are-not-small H
    }

-- The specification of SmallIdentifications, inhabited.
separated-largeness : {ℓ : Level} → Separated-Largeness ℓ
separated-largeness pe u₁ s =
  order-types-form-a-large-separated-set
    (hypotheses pe u₁ (small-identifications-give-resizing u₁ s))

-- Mathematical shape: propositional extensionality at ℓ and univalence at
-- ℓ + 1 refute small identifications; univalence at ℓ gives the first
-- (`univalence-gives-propositional-extensionality`).
small-identifications-are-contradictory : {ℓ : Level} →
  Propositional-Extensionality ℓ → is-univalent (lsuc ℓ) →
  Small-Identifications ℓ → 𝟘
small-identifications-are-contradictory {ℓ} pe u₁ =
  separated-largeness-refutes-small-identifications
    (λ X → funext-below (lsuc ℓ) (λ A B → funext-from-univalence A B u₁ u₁)
      (¬ X) (λ _ → 𝟘))
    (λ X Y →
      funext-below (lsuc ℓ) (λ A B → funext-from-univalence A B u₁ u₁) X Y)
    (λ X Y → funext-from-univalence X Y u₁ u₁) pe u₁ separated-largeness
