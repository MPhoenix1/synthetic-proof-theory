{-# OPTIONS --safe --without-K #-}

module SPT.OrdinalGeometry.Regularity where

-- The ω₁ pattern for any class of ordinals. A class O with a strict
-- relation and a weak relation, the strict one irreflexive and a strict
-- step followed by a weak one strict, bounds its families when every family
-- indexed by a type of an index class has a strict upper bound in O
-- (Bounded-Families). Then no such family covers O in the weak relation
-- (no-family-is-cofinal): the bound of the family would lie strictly below
-- one of its members.
--
--   F : Index i → O,  Π a. F a ≺ q   ⊢   ¬ (Π x. Σ a. x ≼ F a).
--
-- The classes it is stated for: the heights of a universe with the families
-- indexed by its types (Height.Ordinals, heights-bound-families; Ord(ℓ) is
-- their boundary), the child trees of a reflection with the families
-- indexed by the points of its codes (Height.Reflection,
-- child-trees-bound-families; the boundary Ω), and the countable
-- presentations with ℕ-indexed families, the presented ω₁
-- (Presentation.CountableOrdinal, presentations-bound-families; its
-- Cofinality.no-family is the theorem there). The instances stay three:
-- presentations keep decidable orders and their equivalence ≈, heights
-- have only ∼ and least upper bounds of small families. They are compared
-- by rank (Height.Presentation, Height.Calibration).

open import SPT.Base

------------------------------------------------------------------------
-- Classes that bound their families

record Bounded-Families {ℓo ℓs ℓw ℓi ℓa : Level} (O : Set ℓo)
  (strict : O → O → Set ℓs) (weak : O → O → Set ℓw)
  (I : Set ℓi) (Index : I → Set ℓa)
  : Set (ℓo ⊔ ℓs ⊔ ℓw ⊔ ℓi ⊔ ℓa) where
  field
    strict-is-irreflexive : (x : O) → ¬ (strict x x)
    strict-then-weak : {x y z : O} → strict x y → weak y z → strict x z
    upper-bound : (i : I) (F : Index i → O) →
      Σ O (λ q → (a : Index i) → strict (F a) q)

------------------------------------------------------------------------
-- No family is cofinal

module _ {ℓo ℓs ℓw ℓi ℓa : Level} {O : Set ℓo}
  {strict : O → O → Set ℓs} {weak : O → O → Set ℓw}
  {I : Set ℓi} {Index : I → Set ℓa} where

  -- Mathematical shape: the bound q of F lies weakly below some F a, and
  -- F a strictly below q.
  no-family-is-cofinal : Bounded-Families O strict weak I Index →
    (i : I) (F : Index i → O) →
    ¬ ((x : O) → Σ (Index i) (λ a → weak x (F a)))
  no-family-is-cofinal G i F covers =
    let q = pr₁ (Bounded-Families.upper-bound G i F)
        a = pr₁ (covers q)
    in Bounded-Families.strict-is-irreflexive G (F a)
         (Bounded-Families.strict-then-weak G
           (pr₂ (Bounded-Families.upper-bound G i F) a) (pr₂ (covers q)))
