{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Polynomial.Generation.Formation where

-- Higher-order formation over the generated codes of
-- Polynomial.Generation. A tree stage over a code g has one index, a leaf
-- and a node, the node with g as its positions (`stage-diagram`, `stage`,
-- `leaf`, `fork`); higher-order functions on complete trees become later
-- branching types (`functional`, `again`, `higher-node`), and the root
-- operation of a tree determines the domain of its child family (`root`).
--
-- Over the code of 𝟚, with h the higher type (𝟚 → stage) → stage, a later
-- dependent product requires an empty type at every child of the root of
-- the tree returned at a sample function (`next`). Reading the sample at
-- its first and its second point (`left`, `right`) agrees at the constant
-- leaf family (`same`), yet the two products differ: the first is
-- inhabited, the second empty (`live`, `dead`, `no-loss`). So no family of
-- types on the stage reads the product off the value at the constant
-- family (`no-factor`): its domain depends on the complete function. An
-- arbitrary complete higher-order function is an actual position in the
-- next polynomial (`second`, `second-β`), more than a displayed
-- function-type law.

open import SPT.Base
open import SPT.Foundation.Tree using (hole; node)
import SPT.Mahlo.Universe as Universe
open import SPT.Mahlo.Polynomial.Generation using
  (Diagram; Generated; given; product; trees; Value; arrow; higher)

------------------------------------------------------------------------
-- Tree stages

stage-position : {ℓ : Level} → Generated ℓ → Lift ℓ 𝟚 → Generated ℓ
stage-position g (lift ₀) = given Universe.empty
stage-position g (lift ₁) = g

stage-diagram : {ℓ : Level} → Generated ℓ → Diagram (Generated ℓ) Value
stage-diagram g = record
  { index = given Universe.unit
  ; operation = λ i → given Universe.two
  ; position = λ i → stage-position g
  ; input = λ i o p → lift ⋆
  }

stage : {ℓ : Level} → Generated ℓ → Generated ℓ
stage g = trees (stage-diagram g) (lift ⋆)

leaf : {ℓ : Level} (g : Generated ℓ) → Value (stage g)
leaf g = node (lift ₀) (λ p → 𝟘-elim (lower p))

-- Here the codomain is the very tree type being generated. This is the
-- ordinary polynomial node, and its full child function is unrestricted.

fork : {ℓ : Level} (g : Generated ℓ) →
  (Value g → Value (stage g)) → Value (stage g)
fork g f = node (lift ₁) f

functional : {ℓ : Level} (g : Generated ℓ) → Value (higher g (stage g))
functional g = fork g

again : {ℓ : Level} → Generated ℓ → Generated ℓ
again g = stage (higher g (stage g))

higher-node : {ℓ : Level} (g : Generated ℓ) →
  (((Value g → Value (stage g)) → Value (stage g)) → Value (again g)) →
  Value (again g)
higher-node g f = fork (higher g (stage g)) f

-- The actual root operation determines the domain of its child family.

root : {ℓ : Level} (g : Generated ℓ) → Value (stage g) → Generated ℓ
root g (hole ())
root g (node (lift ₀) k) = given Universe.empty
root g (node (lift ₁) k) = g

------------------------------------------------------------------------
-- The product at the returned root depends on the complete function

two-code : Generated lzero
two-code = given Universe.two

two-stage : Generated lzero
two-stage = stage two-code

two-higher : Generated lzero
two-higher = higher two-code two-stage

left : Value two-higher
left f = f (lift ₀)

right : Value two-higher
right f = f (lift ₁)

sample : Value (arrow two-code two-stage)
sample (lift ₀) = leaf two-code
sample (lift ₁) = fork two-code (λ x → leaf two-code)

same : left (λ x → leaf two-code) ＝ right (λ x → leaf two-code)
same = refl

-- A later dependent product requires an empty type at every child of
-- the returned tree's root. That domain depends on the complete function.

next : Value two-higher → Generated lzero
next H = product (root two-code (H sample)) (λ x → given Universe.empty)

live : Value (next left)
live (lift ())

dead : ¬ Value (next right)
dead f = lower (f (lift ₀))

no-loss : Value (next left) ≠ Value (next right)
no-loss e = dead (transport (λ X → X) e live)

no-factor : (K : Value two-stage → Set) →
  ¬ ((H : Value two-higher) →
    Value (next H) ＝ K (H (λ x → leaf two-code)))
no-factor K e = no-loss (e left ∙ e right ⁻¹)

-- An arbitrary complete higher-order function is an actual position in
-- the next polynomial. This is more than a displayed function-type law.

second : Value (again two-code)
second = higher-node two-code (λ H → leaf two-higher)

second-β : second ＝ fork two-higher (λ H → leaf two-higher)
second-β = refl
