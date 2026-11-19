{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Propositions.Closure where

-- Two closure properties of propositions. A type isomorphic to a proposition
-- is a proposition (`isomorphic-to-a-proposition`). The fixed points of a
-- weakly constant endomap form a proposition
-- (`fixed-points-form-a-proposition`): they retract from the type of points
-- identified with the value of the map at any one point. After TypeTopology
-- (UF.KrausLemma: fix-is-prop).

open import SPT.Base
open import SPT.Foundation.Isomorphisms using
  (_≅_; forward; backward; forward-backward)
open import SPT.Foundation.Propositions using (is-proposition)

------------------------------------------------------------------------
-- Isomorphisms

module _ {ℓ κ : Level} {A : Set ℓ} {B : Set κ} where

  isomorphic-to-a-proposition : A ≅ B → is-proposition A → is-proposition B
  isomorphic-to-a-proposition E p x y =
    forward-backward E x ⁻¹
    ∙ ( ap (forward E) (p (backward E x) (backward E y))
      ∙ forward-backward E y)

------------------------------------------------------------------------
-- Weakly constant maps

module _ {ℓ : Level} {X : Set ℓ} where

  is-weakly-constant : (X → X) → Set ℓ
  is-weakly-constant f = (x y : X) → f x ＝ f y

  fixed-points : (X → X) → Set ℓ
  fixed-points f = Σ X (λ x → x ＝ f x)

  -- The points identified with a given point form a proposition.
  points-identified-with-a-point-form-a-proposition : (c : X) →
    is-proposition (Σ X (λ x → x ＝ c))
  points-identified-with-a-point-form-a-proposition c (.c , refl) (.c , refl) =
    refl

  private
    cancel : {x y z : X} (p : x ＝ y) (q : y ＝ z) → (p ∙ q) ∙ q ⁻¹ ＝ p
    cancel refl refl = refl

  -- A fixed point is a point identified with the value at x₀, and back.
  module _ (f : X → X) (c : is-weakly-constant f) (x₀ : X) where

    to-identified : fixed-points f → Σ X (λ x → x ＝ f x₀)
    to-identified (x , p) = x , (p ∙ c x x₀)

    from-identified : Σ X (λ x → x ＝ f x₀) → fixed-points f
    from-identified (x , p) = x , (p ∙ c x x₀ ⁻¹)

    from-to-identified : (w : fixed-points f) →
      from-identified (to-identified w) ＝ w
    from-to-identified (x , p) = ap (λ q → x , q) (cancel p (c x x₀))

  -- Mathematical shape: fix f is a proposition when f is weakly constant.
  fixed-points-form-a-proposition : (f : X → X) → is-weakly-constant f →
    is-proposition (fixed-points f)
  fixed-points-form-a-proposition f c (x , p) (y , q) =
    from-to-identified f c x (x , p) ⁻¹
    ∙ ( ap (from-identified f c x)
          ( points-identified-with-a-point-form-a-proposition (f x)
              (to-identified f c x (x , p))
              (to-identified f c x (y , q)))
      ∙ from-to-identified f c x (y , q))
