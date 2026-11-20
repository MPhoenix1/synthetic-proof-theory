{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Stationary.Ambient where

-- Stationary reflection at the ambient family of level ℓ. Stationarity at
-- the unit predicate is the Mahlo rule there, so it is the smallness
-- principle of induction–recursion: smallness gives it under extensionality
-- (`small`), and stationarity at any predicate gives smallness
-- (`smallness`), through Ambient. Smallness and the rule at
-- the unit predicate give degree one (`degree-one`): every operator has a
-- reflection whose universe, a small type with its interpretation, is
-- itself Mahlo (`mahlo-universes`). The rule at each degree gives every
-- finite degree (`every-degree`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
import SPT.Mahlo.Ambient as Ambient
open import SPT.Mahlo.Decoding using (child-formers)
import SPT.Mahlo.Specification as Specification

import SPT.Mahlo.DS.Ambient as Types
open import SPT.IR.Smallness using (Smallness)
import SPT.Mahlo.DS.Stationary as Stationarity

------------------------------------------------------------------------
-- Degree zero is smallness

module _ {ℓ : Level} where

  small :
    ((X : Set ℓ) → FunExt X (λ _ → Set ℓ)) → Smallness ℓ
    → Stationarity.Stationary (Ambient.formers ℓ)
        (Stationarity.Mahlo-Of (Ambient.formers ℓ) zero)
  small extensionality s =
    Stationarity.stationary (Ambient.formers ℓ)
      ( Types.mahlo extensionality s)

  smallness :
    {ν : Level} (S : Stationarity.Universe (Ambient.formers ℓ) → Set ν)
    → Stationarity.Stationary (Ambient.formers ℓ) S → Smallness ℓ
  smallness S s =
    Types.smallness (Stationarity.reflector (Ambient.formers ℓ) S s)

------------------------------------------------------------------------
-- The degrees above smallness

-- Each degree past zero is the rule at the degree below it, on top of
-- smallness. At degree one the universes are small Mahlo universes: a small
-- type with an interpretation into the types of level ℓ, closed under the
-- operator, which reflects all of its own operators.

module _ {ℓ : Level} where

  degree-one :
    ((X : Set ℓ) → FunExt X (λ _ → Set ℓ)) → Smallness ℓ
    → Stationarity.Stationary-Reflection (Ambient.formers ℓ)
        (Stationarity.Mahlo-Of (Ambient.formers ℓ) zero)
    → Stationarity.Stationary (Ambient.formers ℓ)
        (Stationarity.Mahlo-Of (Ambient.formers ℓ) (suc zero))
  degree-one extensionality s =
    Stationarity.degree-one (Ambient.formers ℓ)
      ( Types.mahlo extensionality s)

  every-degree :
    ((X : Set ℓ) → FunExt X (λ _ → Set ℓ)) → Smallness ℓ
    → ( (n : ℕ)
      → Stationarity.Stationary-Reflection (Ambient.formers ℓ)
          (Stationarity.Mahlo-Of (Ambient.formers ℓ) n))
    → (n : ℕ)
    → Stationarity.Stationary (Ambient.formers ℓ)
        (Stationarity.Mahlo-Of (Ambient.formers ℓ) n)
  every-degree extensionality s =
    Stationarity.every-degree (Ambient.formers ℓ)
      ( Types.mahlo extensionality s)

  mahlo-universes :
    Stationarity.Stationary (Ambient.formers ℓ)
      (Stationarity.Mahlo-Of (Ambient.formers ℓ) (suc zero))
    → (Ψ : Ambient.Operator ℓ)
    → Σ (Specification.Reflection (Ambient.formers ℓ) Ψ) (λ r →
        Specification.Mahlo
          (child-formers (Specification.Reflection.closure r)))
  mahlo-universes s Ψ =
    pr₁ (s Ψ) ,
    Stationarity.child-mahlo (Ambient.formers ℓ)
      ( Stationarity.universe (Ambient.formers ℓ) (pr₁ (s Ψ)))
      ( pr₂ (s Ψ))
