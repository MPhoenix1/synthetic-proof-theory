{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Univalent.Reflector where

-- The ambient Mahlo rule with unique names (`Reflector`): a reflector of
-- the ambient family whose closures name each type at most once, every Name
-- interpret X a proposition, so that interpretation is an embedding. In the
-- simplicial model (the paper proof Simplicial.md) the closure of an
-- operator ψ is a smaller universe U_λ, interpreted by its inclusion, an
-- embedding. Realization's small algebra of a description lives on the
-- closure of its frontier operator and decodes by the interpretation, so it
-- has unique names. With a generation of it, every type-valued description
-- has Shulman's univalent universe with small codes (`universe`); with
-- leastness, its elimination (`elimination`). Under propositional resizing
-- and extensionality the generation is the resized intersection
-- (`resized-universe`), with elimination into every level ν that resizes to
-- ℓ (`resized-elimination`). With an exact classifier of propositions at ℓ
-- and extensionality at ℓ it is the intersection of the closed families of
-- proxies, with no resizing (`classified-universe`), and elimination
-- reaches level ℓ (`classified-elimination`). Excluded middle at ℓ gives
-- the classifier (`decided-universe`, `decided-elimination`); the resizing
-- from ℓ + 1 to ℓ of `resized-universe` is what ExcludedMiddle derives from
-- excluded middle at ℓ + 1 (`excluded-middle-gives-resizing`).

open import SPT.Base
open import SPT.Foundation.ExcludedMiddle using
  (Excluded-Middle; classifier-from-excluded-middle)
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Propositions using (is-proposition)
open import SPT.Foundation.Impredicative.PropositionalResizing using
  (Propositional-Resizing-Between)
open import SPT.Foundation.Impredicative.PropositionalClassifier.Exact using
  (Exact-Classifier; exact-classifier)
import SPT.Mahlo.Ambient as Ambient
import SPT.Mahlo.Specification as Specification

open import SPT.IR.Algebra using (Algebra)
open import SPT.IR.Description using (Desc)
import SPT.Mahlo.DS.Realization as Realization
import SPT.IR.Univalent.Classifier as Classifier
import SPT.Mahlo.DS.Univalent.Construction as Construction
open import SPT.IR.Univalent.Generation using
  (Closed-Family; Least)
import SPT.IR.Univalent.Resizing as Resizing
open import SPT.IR.Univalent.Universe using
  (Universe; Elimination)

------------------------------------------------------------------------
-- The rule

-- Mathematical shape: Mahlo (Ambient.formers ℓ), with
--
--   is-proposition (Σ a ꞉ D carrier , interpret a ＝ X)
--
-- for the closure of every operator and every type X of level ℓ.

record Reflector (ℓ : Level) : Set (lsuc ℓ) where
  field
    mahlo : Specification.Mahlo (Ambient.formers ℓ)
    unique :
      (Ψ : Ambient.Operator ℓ) (X : Set ℓ)
      → is-proposition
          (Specification.Name
            (Specification.Closure.interpret
              (Specification.Reflection.closure
                (Specification.Mahlo.reflect mahlo Ψ)))
            X)

------------------------------------------------------------------------
-- Univalent universes of every description

-- Realization's algebra, at the reflection of γ's frontier operator, with
-- its law and the unique names of that closure.

module _
  {ℓ : Level} (R : Reflector ℓ) (γ : Desc {s = ℓ} (Set ℓ))
  where

  universe :
    Closed-Family (Realization.reflected-algebra (Reflector.mahlo R) γ) ℓ
    → Universe ℓ γ
  universe G =
    Construction.universe
      (Realization.reflected-algebra (Reflector.mahlo R) γ)
      (Realization.reflected-law (Reflector.mahlo R) γ)
      (Reflector.unique R (Realization.operator γ))
      G

  elimination :
    {ν : Level}
    (G :
      Closed-Family (Realization.reflected-algebra (Reflector.mahlo R) γ) ℓ)
    → Least (Realization.reflected-algebra (Reflector.mahlo R) γ) G (ℓ ⊔ ν)
    → Elimination (universe G) ν
  elimination G least =
    Construction.elimination
      (Realization.reflected-algebra (Reflector.mahlo R) γ)
      (Realization.reflected-law (Reflector.mahlo R) γ)
      (Reflector.unique R (Realization.operator γ))
      G least

------------------------------------------------------------------------
-- With propositional resizing

-- The resized intersection of the closed families of level ℓ is the
-- generation; it is least at ℓ ⊔ ν when propositions of that level
-- resize to ℓ.

module _
  {ℓ : Level} (R : Reflector ℓ) (γ : Desc {s = ℓ} (Set ℓ))
  (resize : Propositional-Resizing-Between (lsuc ℓ) ℓ)
  (extensionality :
    (k : Algebra.K (Realization.reflected-algebra (Reflector.mahlo R) γ))
    → FunExt
        (Closed-Family (Realization.reflected-algebra (Reflector.mahlo R) γ)
          ℓ)
        (λ C → Closed-Family.family C k))
  where

  resized-universe : Universe ℓ γ
  resized-universe =
    universe R γ
      (Resizing.generation
        (Realization.reflected-algebra (Reflector.mahlo R) γ) ℓ resize
        extensionality)

  resized-elimination :
    (ν : Level) → Propositional-Resizing-Between (ℓ ⊔ ν) ℓ
    → Elimination resized-universe ν
  resized-elimination ν resize-ν =
    elimination R γ
      (Resizing.generation
        (Realization.reflected-algebra (Reflector.mahlo R) γ) ℓ resize
        extensionality)
      (Resizing.least
        (Realization.reflected-algebra (Reflector.mahlo R) γ) ℓ resize
        extensionality (ℓ ⊔ ν) resize-ν)

------------------------------------------------------------------------
-- With an exact classifier

-- The intersection of the closed families of proxies is the generation;
-- it is least at ℓ, so elimination reaches every motive at level ℓ.

module _
  {ℓ : Level} (R : Reflector ℓ) (γ : Desc {s = ℓ} (Set ℓ))
  (funext : (A : Set ℓ) (B : A → Set ℓ) → FunExt A B)
  where

  classified-universe : Exact-Classifier ℓ → Universe ℓ γ
  classified-universe C =
    universe R γ
      (Classifier.generation
        (Realization.reflected-algebra (Reflector.mahlo R) γ) C funext)

  classified-elimination :
    (C : Exact-Classifier ℓ) → Elimination (classified-universe C) ℓ
  classified-elimination C =
    elimination R γ
      (Classifier.generation
        (Realization.reflected-algebra (Reflector.mahlo R) γ) C funext)
      (Classifier.least
        (Realization.reflected-algebra (Reflector.mahlo R) γ) C funext)

  decided-universe : Excluded-Middle ℓ → Universe ℓ γ
  decided-universe lem =
    classified-universe
      (exact-classifier (classifier-from-excluded-middle ℓ lem))

  decided-elimination :
    (lem : Excluded-Middle ℓ) → Elimination (decided-universe lem) ℓ
  decided-elimination lem =
    classified-elimination
      (exact-classifier (classifier-from-excluded-middle ℓ lem))
