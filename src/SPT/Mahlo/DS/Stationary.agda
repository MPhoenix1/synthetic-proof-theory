{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Stationary where

-- Stationary reflection for SPT's specification. A universe of a parent is
-- a reflection of the identity (`Universe`, `universe`); a universe of its
-- child is one of the parent by Residence's composition (`included`). S is
-- stationary when every operator has a reflection whose universe satisfies
-- S (`Stationary`); the rule at S gives every operator one in whose child S
-- is stationary (`Stationary-Reflection`). From the Mahlo rule, the rule
-- gives every finite degree (`Mahlo-Of`, `every-degree`), and at the unit
-- predicate it is degree one (`degree-one`, `rule-one`, `child-mahlo`).
-- With the reflections fixed this is a reflector's degree (`exact`).

open import SPT.Base
open import SPT.Foundation.Isomorphisms using (_≅_)
open import SPT.Mahlo.Decoding using (child-formers)
open import SPT.Mahlo.Residence.Reflection using (compose)
import SPT.Mahlo.Specification as Specification

------------------------------------------------------------------------
-- Universes

-- A universe of the parent is a code whose decoding names the formers: a
-- reflection of the identity operator, as Setzer's `ordinary` and
-- Residence's Unreflected read one. Every reflection gives a universe
-- with the same names and the identity as its inner operator (`universe`).

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} (Q : Specification.Formers C D)
  where

  Universe : Set (κ ⊔ ℓ)
  Universe = Specification.Reflection Q (λ F → F)

  universe :
    {Ψ : Specification.Operator D} → Specification.Reflection Q Ψ → Universe
  universe r =
    let L = Specification.Reflection.closure r
    in record
      { carrier = Specification.Reflection.carrier r
      ; closure = record
          { interpret = Specification.Closure.interpret L
          ; empty = Specification.Closure.empty L
          ; unit = Specification.Closure.unit L
          ; two = Specification.Closure.two L
          ; natural = Specification.Closure.natural L
          ; product = Specification.Closure.product L
          ; sum = Specification.Closure.sum L
          ; tree = Specification.Closure.tree L
          ; identity = Specification.Closure.identity L
          ; inner = λ F → F
          ; inner-β = λ F → refl
          }
      }

------------------------------------------------------------------------
-- Universes of a child, in the parent

-- A universe of a universe's child is a universe of the parent: it is read
-- through the universe's interpretation by Residence.Reflection's
-- composition, at the identity operator. Its resident family is the
-- composite of Residence.Families (Stationary.Discriminator).

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} (Q : Specification.Formers C D)
  where

  included :
    (u : Universe Q)
    → Universe (child-formers (Specification.Reflection.closure u))
    → Universe Q
  included u v = compose (universe Q u) v

------------------------------------------------------------------------
-- Stationary predicates and their reflection

-- A predicate on the parent's universes holds of a child of an operator
-- when some reflection of it has a universe satisfying it (`Child-In`); it
-- is stationary when every operator has such a child. At a universe,
-- `Stationary-In S` asks the same of every operator on the universe's own
-- families, with its children read in the parent (`included`). The rule at
-- S: stationarity of S gives every operator a child in which S is
-- stationary.

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} (Q : Specification.Formers C D)
  where

  -- Mathematical shape: Σ (r : Reflection Q Ψ). S (universe r).
  Child-In :
    {ν : Level} → (Universe Q → Set ν) → Specification.Operator D
    → Set (κ ⊔ ℓ ⊔ ν)
  Child-In S Ψ = Σ (Specification.Reflection Q Ψ) (λ r → S (universe Q r))

  Stationary : {ν : Level} → (Universe Q → Set ν) → Set (κ ⊔ ℓ ⊔ ν)
  Stationary S = (Ψ : Specification.Operator D) → Child-In S Ψ

  -- Mathematical shape, at a universe u with closure L:
  --
  --   Π (Φ : Operator (Decode D (interpret L))).
  --     Σ (r : Reflection (child-formers L) Φ). S (included u (universe r)).
  Stationary-In :
    {ν : Level} → (Universe Q → Set ν) → Universe Q → Set (ℓ ⊔ ν)
  Stationary-In S u =
    let L = Specification.Reflection.closure u
    in (Φ : Specification.Operator
          (Specification.Decode D (Specification.Closure.interpret L)))
       → Σ (Specification.Reflection (child-formers L) Φ) (λ r →
           S (included Q u (universe (child-formers L) r)))

  Stationary-Reflection :
    {ν : Level} → (Universe Q → Set ν) → Set (κ ⊔ ℓ ⊔ ν)
  Stationary-Reflection S =
    Stationary S
    → (Ψ : Specification.Operator D) → Child-In (Stationary-In S) Ψ

------------------------------------------------------------------------
-- Mahlo of every finite degree

-- Mahlo-Of 0 asks nothing and Mahlo-Of (n + 1) is Stationary-In of Mahlo-Of n.
-- Stationarity at Mahlo-Of 0 is the Mahlo rule (`stationary`,
-- `reflector`), and stationarity at Mahlo-Of (n + 1) is the conclusion of
-- the rule at Mahlo-Of n. At a universe, Mahlo-Of 1 is the Mahlo rule of its
-- child (`child-mahlo`, `mahlo-child`), and each degree gives the one
-- below it (`lowered`).

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} (Q : Specification.Formers C D)
  where

  Mahlo-Of : ℕ → Universe Q → Set ℓ
  Mahlo-Of zero u = Lift ℓ 𝟙
  Mahlo-Of (suc n) u = Stationary-In Q (Mahlo-Of n) u

  stationary : Specification.Mahlo Q → Stationary Q (Mahlo-Of zero)
  stationary M Ψ = Specification.Mahlo.reflect M Ψ , lift ⋆

  reflector :
    {ν : Level} (S : Universe Q → Set ν) → Stationary Q S
    → Specification.Mahlo Q
  reflector S s = record { reflect = λ Ψ → pr₁ (s Ψ) }

  child-mahlo :
    (u : Universe Q) → Mahlo-Of (suc zero) u
    → Specification.Mahlo (child-formers (Specification.Reflection.closure u))
  child-mahlo u m = record { reflect = λ Φ → pr₁ (m Φ) }

  mahlo-child :
    (u : Universe Q)
    → Specification.Mahlo (child-formers (Specification.Reflection.closure u))
    → Mahlo-Of (suc zero) u
  mahlo-child u c Φ = Specification.Mahlo.reflect c Φ , lift ⋆

  lowered : (n : ℕ) (u : Universe Q) → Mahlo-Of (suc n) u → Mahlo-Of n u
  lowered zero u m = lift ⋆
  lowered (suc n) u m Φ =
    pr₁ (m Φ) ,
    lowered n
      ( included Q u
        ( universe (child-formers (Specification.Reflection.closure u))
          ( pr₁ (m Φ))))
      ( pr₂ (m Φ))

------------------------------------------------------------------------
-- The rule gives every finite degree

-- From the Mahlo rule and the rule at each degree, stationarity at every
-- degree, by induction on the degree. At the unit predicate the rule is
-- exactly degree one: it gives it from the Mahlo rule (`degree-one`), and
-- its conclusion holds outright once degree one does (`rule-one`).

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} (Q : Specification.Formers C D)
  where

  every-degree :
    Specification.Mahlo Q
    → ((n : ℕ) → Stationary-Reflection Q (Mahlo-Of Q n))
    → (n : ℕ) → Stationary Q (Mahlo-Of Q n)
  every-degree M rule zero = stationary Q M
  every-degree M rule (suc n) = rule n (every-degree M rule n)

  degree-one :
    Specification.Mahlo Q → Stationary-Reflection Q (Mahlo-Of Q zero)
    → Stationary Q (Mahlo-Of Q (suc zero))
  degree-one M rule = rule (stationary Q M)

  rule-one :
    Stationary Q (Mahlo-Of Q (suc zero))
    → Stationary-Reflection Q (Mahlo-Of Q zero)
  rule-one s _ = s

------------------------------------------------------------------------
-- Degrees of a reflector

-- A reflector has degree n when the universe of each of its reflections is
-- Mahlo of degree n. A reflector with its degree is stationarity at that
-- degree with the reflections fixed, both round trips by refl.

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} (Q : Specification.Formers C D)
  where

  Degree : ℕ → Specification.Mahlo Q → Set (κ ⊔ ℓ)
  Degree n M =
    (Ψ : Specification.Operator D)
    → Mahlo-Of Q n (universe Q (Specification.Mahlo.reflect M Ψ))

  exact :
    (n : ℕ)
    → (Σ (Specification.Mahlo Q) (λ M → Degree n M))
      ≅ Stationary Q (Mahlo-Of Q n)
  exact n = record
    { forward = λ p Ψ → Specification.Mahlo.reflect (pr₁ p) Ψ , pr₂ p Ψ
    ; backward = λ s → reflector Q (Mahlo-Of Q n) s , (λ Ψ → pr₂ (s Ψ))
    ; backward-forward = λ p → refl
    ; forward-backward = λ s → refl
    }
