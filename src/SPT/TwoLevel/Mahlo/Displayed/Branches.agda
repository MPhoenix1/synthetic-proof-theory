{-# OPTIONS --safe --without-K --two-level #-}

module SPT.TwoLevel.Mahlo.Displayed.Branches where

-- Strictly identified split families carry base points back (back) and
-- fiber points over those same points (carry). The theorem branches-along
-- identifies the entire dependent pair of branch sets and branch fibers
-- after this transport. All three computing clauses match same.

open import SPT.Base
open import SPT.TwoLevel.Coherence using (_≐_; same)
open import SPT.TwoLevel.Mahlo.Displayed using (Split-Family)

------------------------------------------------------------------------
-- Base points, fiber points and branches along strict identification

module _ {ι ι′ ℓ : Level} {X : Set ι} {Y : X → Set ι′} where

  -- A point of the second's family, carried back to the first's.
  back : {f g : Split-Family ℓ X Y} → f ≐ g → (x : X) →
    pr₁ (pr₁ g x) → pr₁ (pr₁ f x)
  back same x a = a

  -- A fiber point over it, carried back with it.
  carry : {f g : Split-Family ℓ X Y} (e : f ≐ g) (x : X) (y : Y x)
    (a : pr₁ (pr₁ g x)) → pr₁ (pr₂ g x y) a → pr₁ (pr₂ f x y) (back e x a)
  carry same x y a a₁ = a₁

  -- The branches of the first at points carried back are the second's,
  -- the sets and the fiber families over them.
  branches-along : {f g : Split-Family ℓ X Y} (e : f ≐ g) →
    _≐_ {A = Σ ((x : X) → pr₁ (pr₁ g x) → Set ℓ)
        (λ h → (x : X) (y : Y x) (a : pr₁ (pr₁ g x)) →
          pr₁ (pr₂ g x y) a → h x a → Set ℓ)}
      ((λ x a → pr₂ (pr₁ f x) (back e x a)) ,
        (λ x y a a₁ → pr₂ (pr₂ f x y) (back e x a) (carry e x y a a₁)))
      ((λ x a → pr₂ (pr₁ g x) a) , (λ x y a a₁ → pr₂ (pr₂ g x y) a a₁))
  branches-along same = same

