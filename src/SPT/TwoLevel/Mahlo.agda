{-# OPTIONS --safe --without-K --two-level #-}

module SPT.TwoLevel.Mahlo where

-- The strict Mahlo rule for a Tarski family. Strict-Mahlo specifies a
-- parent code at each operator, an interpretation of its decoding, and
-- points naming every former and the operator's value. Each decoding law
-- is a strict identification between functions of all its arguments:
--
--   inner-β : (λ Ψ F → map (inner Ψ F)) ≐ (λ Ψ F → Ψ (map F)).
--
-- The laws hold in the context of the operator without function
-- extensionality. The record is a hypothesis; a labelled algebra with
-- classified carriers constructs it in Mahlo.StepAlgebra.

open import Agda.Primitive using (SSet)
open import SPT.Base
open import SPT.Mahlo.Specification using
  (Family; Operator; Formers; Decode; map)
open import SPT.TwoLevel.Coherence using (_≐_)

------------------------------------------------------------------------
-- Strict decoding laws in context

record Strict-Mahlo {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Formers C D) : SSet (κ ⊔ ℓ) where
  field
    carrier : Operator D → C
    interpret : (Ψ : Operator D) → D (carrier Ψ) → C

    empty unit two natural : (Ψ : Operator D) → D (carrier Ψ)
    product sum tree : (Ψ : Operator D) →
      Family (Decode D (interpret Ψ)) → D (carrier Ψ)
    identity : (Ψ : Operator D) (a : D (carrier Ψ)) →
      Decode D (interpret Ψ) a → Decode D (interpret Ψ) a → D (carrier Ψ)
    inner : (Ψ : Operator D) → Family (Decode D (interpret Ψ)) →
      Family (Decode D (interpret Ψ))

    empty-β : (λ (Ψ : Operator D) → interpret Ψ (empty Ψ)) ≐
      (λ Ψ → Formers.empty Q)
    unit-β : (λ (Ψ : Operator D) → interpret Ψ (unit Ψ)) ≐
      (λ Ψ → Formers.unit Q)
    two-β : (λ (Ψ : Operator D) → interpret Ψ (two Ψ)) ≐
      (λ Ψ → Formers.two Q)
    natural-β : (λ (Ψ : Operator D) → interpret Ψ (natural Ψ)) ≐
      (λ Ψ → Formers.natural Q)
    product-β :
      (λ (Ψ : Operator D) (F : Family (Decode D (interpret Ψ))) →
        interpret Ψ (product Ψ F)) ≐
      (λ Ψ F → Formers.product Q (map D (interpret Ψ) F))
    sum-β :
      (λ (Ψ : Operator D) (F : Family (Decode D (interpret Ψ))) →
        interpret Ψ (sum Ψ F)) ≐
      (λ Ψ F → Formers.sum Q (map D (interpret Ψ) F))
    tree-β :
      (λ (Ψ : Operator D) (F : Family (Decode D (interpret Ψ))) →
        interpret Ψ (tree Ψ F)) ≐
      (λ Ψ F → Formers.tree Q (map D (interpret Ψ) F))
    identity-β :
      (λ (Ψ : Operator D) (a : D (carrier Ψ))
         (x y : Decode D (interpret Ψ) a) →
        interpret Ψ (identity Ψ a x y)) ≐
      (λ Ψ a x y → Formers.identity Q (interpret Ψ a) x y)
    inner-β :
      (λ (Ψ : Operator D) (F : Family (Decode D (interpret Ψ))) →
        map D (interpret Ψ) (inner Ψ F)) ≐
      (λ Ψ F → Ψ (map D (interpret Ψ) F))
