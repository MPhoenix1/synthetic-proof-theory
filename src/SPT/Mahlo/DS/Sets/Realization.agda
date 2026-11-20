{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Sets.Realization where

-- Small algebras of set-valued descriptions with set arities, from
-- closures of the parent of small sets, through the type-valued
-- realization. An ambient operator that keeps families of sets lifts to
-- the parent of sets (`points-family`, `lift-operator`), and a closure of
-- the parent of sets under the lift is an ambient closure on the same
-- carrier, decoding by points (`ambient-closure`): the parent's formers
-- decode to the ambient ones by refl. The frontier operator of a
-- description's reading keeps families of sets (`frontier-keeps-sets`),
-- so a closure under its lift (`frontier-operator`) is, through
-- DS.Realization, a small algebra of the reading, and read back a small
-- algebra of the description on the closure's own carrier, decoding by
-- its interpretation (`ambient`, `algebra`, `law`). Closures of every
-- operator give one at every description (`algebra-of-closures`,
-- `law-of-closures`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Propositions using (is-set)
import SPT.Mahlo.Ambient as Ambient
import SPT.Mahlo.Specification as Specification
open import SPT.Mahlo.Sets using
  ( Small-Set; small-set; points; points-form-a-set; Operator; set-formers
  ; small-set-identification )

open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.IR.Description using (Desc; indexed; Mark)
import SPT.Mahlo.DS.Realization as Realization
import SPT.Mahlo.DS.Realization.Frontier as Frontier
open import SPT.Mahlo.DS.Sets.Description using
  ( Set-Arities; translate; translate-shape; translate-mark
  ; translated-is-set-valued; frontier-is-set-valued; shapes-are-sets
  ; marks-are-sets )

------------------------------------------------------------------------
-- Lifting an ambient operator

-- The family of points of a family of small sets.
points-family : {ℓ : Level} →
  Specification.Family {C = Small-Set ℓ} points →
  Specification.Family (λ (X : Set ℓ) → X)
points-family (a , b) = points a , (λ x → points (b x))

-- An ambient operator returning a family of sets at every family of sets
-- is an operator of the parent of sets with the same points.

module _ {ℓ : Level} (Ψ : Ambient.Operator ℓ)
  (keeps : (F : Specification.Family {C = Small-Set ℓ} points) →
    is-set (pr₁ (Ψ (points-family F))) ×
    ((z : pr₁ (Ψ (points-family F))) →
      is-set (pr₂ (Ψ (points-family F)) z)))
  where

  lift-operator : Operator ℓ
  lift-operator F =
    small-set (pr₁ (Ψ (points-family F))) (pr₁ (keeps F)) ,
    (λ z → small-set (pr₂ (Ψ (points-family F)) z) (pr₂ (keeps F) z))

------------------------------------------------------------------------
-- Closures of the lift are ambient closures

-- Each former's name is the parent's, its identification read by points;
-- the operator's family is the parent's, its identification read by the
-- family of points.

module _ {ℓ : Level}
  (functions : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y)
  (Ψ : Ambient.Operator ℓ)
  (keeps : (F : Specification.Family {C = Small-Set ℓ} points) →
    is-set (pr₁ (Ψ (points-family F))) ×
    ((z : pr₁ (Ψ (points-family F))) →
      is-set (pr₂ (Ψ (points-family F)) z)))
  {K : Set ℓ}
  (L : Specification.Closure (set-formers functions) (lift-operator Ψ keeps)
    K)
  where

  open Specification.Closure L using (interpret)

  ambient-closure : Specification.Closure (Ambient.formers ℓ) Ψ K
  ambient-closure = record
    { interpret = λ k → points (interpret k)
    ; empty =
        pr₁ (Specification.Closure.empty L) ,
        ap points (pr₂ (Specification.Closure.empty L))
    ; unit =
        pr₁ (Specification.Closure.unit L) ,
        ap points (pr₂ (Specification.Closure.unit L))
    ; two =
        pr₁ (Specification.Closure.two L) ,
        ap points (pr₂ (Specification.Closure.two L))
    ; natural =
        pr₁ (Specification.Closure.natural L) ,
        ap points (pr₂ (Specification.Closure.natural L))
    ; product = λ F →
        pr₁ (Specification.Closure.product L F) ,
        ap points (pr₂ (Specification.Closure.product L F))
    ; sum = λ F →
        pr₁ (Specification.Closure.sum L F) ,
        ap points (pr₂ (Specification.Closure.sum L F))
    ; tree = λ F →
        pr₁ (Specification.Closure.tree L F) ,
        ap points (pr₂ (Specification.Closure.tree L F))
    ; identity = λ a x y →
        pr₁ (Specification.Closure.identity L a x y) ,
        ap points (pr₂ (Specification.Closure.identity L a x y))
    ; inner = Specification.Closure.inner L
    ; inner-β = λ F → ap points-family (Specification.Closure.inner-β L F)
    }

------------------------------------------------------------------------
-- The frontier operator of the reading

-- Its shapes over a family of sets and their outputs are sets, since the
-- reading of a description with set arities is set-valued.

module _ {ℓ : Level}
  (functions : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y)
  (γ : Desc {s = ℓ} (Small-Set ℓ)) (arities : Set-Arities γ)
  where

  frontier-keeps-sets : (F : Specification.Family {C = Small-Set ℓ} points) →
    is-set (pr₁ (Realization.operator (translate γ) (points-family F))) ×
    ((z : pr₁ (Realization.operator (translate γ) (points-family F))) →
      is-set (pr₂ (Realization.operator (translate γ) (points-family F)) z))
  frontier-keeps-sets F =
    shapes-are-sets functions (Frontier.description (translate γ))
      (frontier-is-set-valued (translate γ)
        (translated-is-set-valued functions γ arities))
      (indexed (points (pr₁ F)) (λ x → points (pr₂ F x)))
      (points-form-a-set (pr₁ F)) ,
    marks-are-sets (Frontier.description (translate γ))
      (frontier-is-set-valued (translate γ)
        (translated-is-set-valued functions γ arities))
      (indexed (points (pr₁ F)) (λ x → points (pr₂ F x)))

  frontier-operator : Operator ℓ
  frontier-operator =
    lift-operator (Realization.operator (translate γ)) frontier-keeps-sets

------------------------------------------------------------------------
-- Small algebras

-- The realization of the reading at the ambient closure, its operation
-- read at the reading of each shape, and its law read back to small sets.

module _ {ℓ : Level}
  (functions : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y)
  (γ : Desc {s = ℓ} (Small-Set ℓ)) (arities : Set-Arities γ) {K : Set ℓ}
  (L : Specification.Closure (set-formers functions)
    (frontier-operator functions γ arities) K)
  where

  open Specification.Closure L using (interpret)

  ambient :
    Specification.Closure (Ambient.formers ℓ)
      (Realization.operator (translate γ)) K
  ambient =
    ambient-closure functions (Realization.operator (translate γ))
      (frontier-keeps-sets functions γ arities) L

  algebra : Algebra ℓ γ
  algebra = record
    { K = K
    ; value = interpret
    ; operation = λ z →
        Algebra.operation (Realization.algebra (translate γ) ambient)
          (translate-shape interpret γ z)
    }

  law : Law algebra
  law z =
    small-set-identification functions
      (interpret
        (Algebra.operation (Realization.algebra (translate γ) ambient)
          (translate-shape interpret γ z)))
      (Mark γ (indexed K interpret) z)
      ( Realization.law (translate γ) ambient (translate-shape interpret γ z)
      ∙ translate-mark interpret γ z)

-- Closures of every operator give a small algebra of every description
-- with set arities.

module _ {ℓ : Level}
  (functions : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y)
  (R : (Ψ : Operator ℓ) →
    Σ (Set ℓ) (λ K → Specification.Closure (set-formers functions) Ψ K))
  where

  algebra-of-closures : (γ : Desc {s = ℓ} (Small-Set ℓ)) →
    Set-Arities γ → Algebra ℓ γ
  algebra-of-closures γ arities =
    algebra functions γ arities
      (pr₂ (R (frontier-operator functions γ arities)))

  law-of-closures : (γ : Desc {s = ℓ} (Small-Set ℓ))
    (arities : Set-Arities γ) → Law (algebra-of-closures γ arities)
  law-of-closures γ arities =
    law functions γ arities (pr₂ (R (frontier-operator functions γ arities)))
