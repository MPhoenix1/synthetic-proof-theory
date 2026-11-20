{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Polynomial.Parent.Formation where

-- Complete higher-order functions return actual Mahlo polynomial trees, in
-- the parent of Polynomial.Parent at level zero. Its reflection of the
-- identity operator is a code (`reflected-identity`), with the higher type
-- (T → T) → T of its decoding T (`carrier-higher`, `higher-β`). One
-- literal polynomial block with two successive operations, a sum and a
-- product over the unit, holds a whole closure code in its holes
-- (`assemble`, `assemble-β`). Reading a function at the empty and the unit
-- code (`left`, `right`) agrees at the constant unit family (`same`).
--
-- The interpreted return at the identity determines the next operator: its
-- first branch the higher-order return, its second the sum of the complete
-- input family (`selected`, `operator`), with resident reflection
-- (`second`, `resident`, `resident-β`), whose closure satisfies the inner
-- law by refl (`whole`). The inner family at a unit anchor chooses, at its
-- first branch, the selected return (`anchor`, `output`, `chosen`,
-- `chosen-β`), and a later dependent sum over it (`later`) is inhabited at
-- `right` and empty at `left` (`live`, `dead`, `no-loss`); so no family of
-- types on T reads it off the value at the constant family (`no-factor`).
-- Neither branch is replaced by a shape summary. The complete second
-- carrier is again a materialization domain (`powers`, `higher-powers`,
-- `twice-β`).

open import SPT.Base
open import SPT.Foundation.Tree using (hole; node)
open import SPT.Mahlo.Specification using
  (Family; Decode; map; Operator; Formers; Closure; Reflection)
import SPT.Mahlo.Universe as Universe
import SPT.Mahlo.Polynomial.Basis as Basis
import SPT.Mahlo.Polynomial.Closure as Block
open import SPT.Mahlo.Polynomial.Parent using
  ( Generated; Value; given; sum; product; materialize; power; formers
  ; reflect; reflected; higher
  )

------------------------------------------------------------------------
-- One block holding a closure code

reflected-identity : Generated lzero
reflected-identity = reflected (λ F → F)

carrier-higher : Generated lzero
carrier-higher = higher reflected-identity reflected-identity

higher-β :
  Value carrier-higher
    ＝ ((Value reflected-identity → Value reflected-identity) →
      Value reflected-identity)
higher-β = refl

-- This is one literal polynomial block with two successive operations.
-- The entire returned closure code occupies its open holes.

assemble : Value reflected-identity → Value reflected-identity
assemble t =
  Block.block Block.unit
    (node Block.sigma (λ x → node Block.pi (λ y → hole t)))

assemble-β : (t : Value reflected-identity) →
  Block.interpret (formers lzero) (λ F → F) (assemble t)
    ＝ sum (Formers.unit (formers lzero))
      (λ x → product (Formers.unit (formers lzero))
        (λ y → Block.interpret (formers lzero) (λ F → F) t))
assemble-β t = refl

left : Value carrier-higher
left f = assemble (f Block.empty)

right : Value carrier-higher
right f = assemble (f Block.unit)

same : left (λ t → Block.unit) ＝ right (λ t → Block.unit)
same = refl

------------------------------------------------------------------------
-- The next operator and its resident reflection

selected : Value carrier-higher → Generated lzero
selected H = Block.interpret (formers lzero) (λ F → F) (H (λ t → t))

-- The first branch uses the higher-order return; the second retains the
-- complete input family.

operator-branch : Value carrier-higher → Family (Value {lzero}) →
  Lift lzero 𝟚 → Generated lzero
operator-branch H F (lift ₀) = selected H
operator-branch H F (lift ₁) = Formers.sum (formers lzero) F

operator : Value carrier-higher → Operator (Value {lzero})
operator H F = Formers.two (formers lzero) , operator-branch H F

second : Value carrier-higher → Generated lzero
second H = reflected (operator H)

resident : (H : Value carrier-higher) →
  Reflection (formers lzero) (operator H)
resident H = reflect (operator H)

resident-β : (H : Value carrier-higher) →
  Value (second H) ＝ Block.Code (formers lzero) (operator H)
resident-β H = refl

whole : (H : Value carrier-higher)
  (F : Family
    (Decode Value (Closure.interpret (Reflection.closure (resident H))))) →
  map Value (Closure.interpret (Reflection.closure (resident H)))
    (Closure.inner (Reflection.closure (resident H)) F)
    ＝ operator H
      (map Value (Closure.interpret (Reflection.closure (resident H))) F)
whole H F = refl

anchor : (H : Value carrier-higher) →
  Family (Decode Value (Closure.interpret (Reflection.closure (resident H))))
anchor H = Block.unit , (λ x → Block.unit)

output : (H : Value carrier-higher) →
  Family (Decode Value (Closure.interpret (Reflection.closure (resident H))))
output H = Closure.inner (Reflection.closure (resident H)) (anchor H)

chosen : Value carrier-higher → Generated lzero
chosen H =
  Closure.interpret (Reflection.closure (resident H))
    (pr₂ (output H) (lift ₀))

chosen-β : (H : Value carrier-higher) → chosen H ＝ selected H
chosen-β H = refl

------------------------------------------------------------------------
-- A later dependent sum over the chosen return

later : Value carrier-higher → Generated lzero
later H = sum (chosen H) (λ x → given Universe.unit)

live : Value (later right)
live = (lift ⋆ , (λ y → lift ⋆)) , lift ⋆

dead : ¬ Value (later left)
dead ((x , f) , y) = lower (f (lift ⋆))

no-loss : Value (later right) ≠ Value (later left)
no-loss e = dead (transport (λ X → X) e live)

no-factor : (K : Value reflected-identity → Set) →
  ¬ ((H : Value carrier-higher) →
    Value (later H) ＝ K (H (λ t → Block.unit)))
no-factor K e = no-loss (e right ∙ e left ⁻¹)

------------------------------------------------------------------------
-- The complete second Mahlo carrier is again a materialization domain

powers : Value carrier-higher → Generated lzero
powers H = materialize (second H) power

higher-powers : Value carrier-higher → Generated lzero
higher-powers H = materialize (powers H) power

twice-β : (H : Value carrier-higher) →
  Value (higher-powers H)
    ＝ ((Value (second H) → Basis.Small lzero) → Basis.Small lzero)
twice-β H = refl
