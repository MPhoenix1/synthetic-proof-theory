{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Described.Discriminator where

-- The reflections of Mahlo.Described have content. Formers commute with the
-- embedding as codes (`product-code`). A reflected action's head is the
-- operator's actual output code (`output-code`, `output-β`); a sum after a
-- selection returns V's sigma code over the selection's output
-- (`composed-code`), and a tree description V's tree code (`tree-code`). A
-- description returning one reflected child is reflected again, with that
-- child as its output (`contained`). V's reflections meet
-- DS.Stationary.Derivable: no carrier is derivable by V's formers and its
-- own operator (`carrier-underivable`); each carrier is derivable by the
-- constant operator at it, which V describes (`carrier-derivable`); and V's
-- reflection of the constant operator at a code does not have that code as
-- carrier (`constant-carrier`). V's codes are small, so V does not admit
-- every small type (`unadmitting`): it reflects what it describes, but
-- cannot absorb its level. Combined through V's two-element code, two
-- described operators derive each one's outputs and one applied to the
-- other's (`selected-derived`, `composed-derived`), and no carrier is
-- derivable by its own operator and the identity together
-- (`carrier-underivable-together`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
import SPT.Mahlo.Relative as Relative
open import SPT.Mahlo.Retraction using (retracts-from-laws)
import SPT.Mahlo.Specification as Specification
open import SPT.Mahlo.DS.Cedents using
  (Ced; Closed; Derivable; ∅ᶜ; derivable-closed; named-closed)
import SPT.Mahlo.DS.Naming as Naming
open import SPT.Mahlo.DS.Stationary.Derivable using
  ( not-derivable; constant; constant-derivable; constant-unreflected
  ; admission-not-small; combined; combined-derivable
  ; not-derivable-together)
open import SPT.Mahlo.Described

------------------------------------------------------------------------
-- Descriptions

-- A resident family at true, the identity at false.
choose : Dec two → Desc
choose (lift ₁) = residentᵈ two (λ _ → unit)
choose (lift ₀) = identityᵈ

selected : Desc
selected = selectᵈ two choose

-- The selection, then the sum of its output.
composed : Desc
composed = composeᵈ selected (sumᵈ identityᵈ)

-- Trees of the family of units over the two-element code.
branching : Desc
branching = treeᵈ (residentᵈ two (λ _ → unit))

-- The constant operator at a code, as V describes it.
constantᵈ : V → Desc
constantᵈ c = residentᵈ c (λ _ → c)

output-β :
  pr₁ (operator selected (two , (λ _ → two))) ＝
    sigma two (λ x → pr₁ (operator (choose x) (two , (λ _ → two))))
output-β = refl

------------------------------------------------------------------------
-- The reflections compute

module _ (ext : Extensionality) where

  carrier-β :
    Specification.Reflection.carrier (reflect ext selected)
      ＝ reflected selected
  carrier-β = refl

  product-code :
    embed ext selected (Relative.product Relative.two (λ _ → Relative.unit))
      ＝ pi two (λ _ → unit)
  product-code = refl

  output-code :
    embed ext selected
      (pr₁ (action ext selected (Relative.two , (λ _ → Relative.two))))
      ＝ pr₁ (operator selected (two , (λ _ → two)))
  output-code = refl

  composed-code :
    embed ext composed
      ( pr₂ (action ext composed (Relative.two , (λ _ → Relative.two)))
          (lift ⋆))
      ＝ sigma (pr₁ (operator selected (two , (λ _ → two))))
          (pr₂ (operator selected (two , (λ _ → two))))
  composed-code = refl

  tree-code :
    embed ext branching
      ( pr₂ (action ext branching (Relative.unit , (λ _ → Relative.unit)))
          (lift ⋆))
      ＝ tree two (λ _ → unit)
  tree-code = refl

  -- A description returning the first reflected child, carrier and map.
  nested : Desc
  nested = residentᵈ (reflected selected) (embed ext selected)

  contained :
    embed ext nested
      (pr₁ (action ext nested (Relative.unit , (λ _ → Relative.unit))))
      ＝ reflected selected
  contained = refl

------------------------------------------------------------------------
-- V's reflections and DS.Stationary.Derivable

-- V describes the constant operator at every code.
described-constant : (c : V) → operator (constantᵈ c) ＝ constant Dec c
described-constant c = refl

-- Each carrier is derivable by the constant operator at it.
carrier-derivable :
  (d : Desc)
  → Derivable formers (operator (constantᵈ (reflected d))) ∅ᶜ (reflected d)
carrier-derivable d =
  transport (λ Ψ → Derivable formers Ψ ∅ᶜ (reflected d))
    (described-constant (reflected d) ⁻¹)
    (constant-derivable formers (reflected d))

-- V's codes are small, so V does not admit every small type.
unadmitting : ¬ Naming.Admission Dec
unadmitting = admission-not-small formers (retracts-from-laws laws)

------------------------------------------------------------------------
-- Several described operators together

-- The selection and the composition, as one operator through V's
-- two-element code.
together : Dec two → Specification.Operator Dec
together (lift ₁) = operator selected
together (lift ₀) = operator composed

unit-derivable :
  Derivable formers
    (combined formers (retracts-from-laws laws) two together) ∅ᶜ unit
unit-derivable =
  Closed.on-unit
    (derivable-closed formers
      (combined formers (retracts-from-laws laws) two together) ∅ᶜ)

-- The selection's index at the unit family.
selected-derived :
  Derivable formers
    (combined formers (retracts-from-laws laws) two together) ∅ᶜ
    (pr₁ (operator selected (unit , (λ _ → unit))))
selected-derived =
  Closed.on-result
    (combined-derivable formers (retracts-from-laws laws) ∅ᶜ two together
      (lift ₁))
    unit (λ _ → unit) unit-derivable (λ _ → unit-derivable)

-- The composition's member over the selection's output: a step of each.
composed-derived :
  Derivable formers
    (combined formers (retracts-from-laws laws) two together) ∅ᶜ
    (pr₂ (operator composed (operator selected (unit , (λ _ → unit))))
      (lift ⋆))
composed-derived =
  Closed.on-branch
    (combined-derivable formers (retracts-from-laws laws) ∅ᶜ two together
      (lift ₀))
    (pr₁ (operator selected (unit , (λ _ → unit))))
    (pr₂ (operator selected (unit , (λ _ → unit))))
    selected-derived
    (Closed.on-branch
      (combined-derivable formers (retracts-from-laws laws) ∅ᶜ two together
        (lift ₁))
      unit (λ _ → unit) unit-derivable (λ _ → unit-derivable))
    (lift ⋆)

-- A described operator with the identity beside it.
with-identity : Desc → Dec two → Specification.Operator Dec
with-identity d (lift ₁) = operator d
with-identity d (lift ₀) = λ F → F

-- Names closed under an operator are closed under it with the identity.
beside :
  {μ : Level} {Δ : Ced μ V} (d : Desc)
  → Closed formers (operator d) Δ
  → (x : Dec two)
  → Closed formers (with-identity d x) Δ
beside d names (lift ₁) = names
beside d names (lift ₀) = record
  { on-empty = Closed.on-empty names
  ; on-unit = Closed.on-unit names
  ; on-two = Closed.on-two names
  ; on-natural = Closed.on-natural names
  ; on-product = Closed.on-product names
  ; on-sum = Closed.on-sum names
  ; on-tree = Closed.on-tree names
  ; on-identity = Closed.on-identity names
  ; on-result = λ a b n m → n
  ; on-branch = λ a b n m y → m y
  }

module _
  (ext : Extensionality)
  (extensionality : (X : Set) → FunExt X (λ _ → V))
  where

  -- No carrier is derivable by V's formers and its own operator.
  carrier-underivable :
    (d : Desc) → ¬ Derivable formers (operator d) ∅ᶜ (reflected d)
  carrier-underivable d =
    not-derivable formers (retracts-from-laws laws) extensionality
      (operator d) (reflect ext d)

  -- V's reflection of the constant operator at c has another carrier.
  constant-carrier : (c : V) → ¬ (reflected (constantᵈ c) ＝ c)
  constant-carrier c =
    constant-unreflected formers (retracts-from-laws laws) extensionality c
      ( transport (λ Ψ → Specification.Reflection formers Ψ)
          (described-constant c)
          (reflect ext (constantᵈ c)))

  -- No carrier is derivable by its own operator and the identity together.
  carrier-underivable-together :
    (d : Desc)
    → ¬ Derivable formers
          (combined formers (retracts-from-laws laws) two (with-identity d))
          ∅ᶜ (reflected d)
  carrier-underivable-together d =
    let r = reflect ext d
    in not-derivable-together formers (retracts-from-laws laws)
         extensionality (operator d) r two (with-identity d)
         (Specification.Closure.two (Specification.Reflection.closure r))
         (beside d
           (named-closed extensionality (Specification.Reflection.closure r)))
         ∅ᶜ (λ p → 𝟘-elim p)
