{-# OPTIONS --safe --without-K #-}

module SPT.IR.Morphism where

-- Morphisms of algebras of a Dybjer–Setzer description, with their laws.
-- The fibers of N's decoding over M's decodings (`Fibers`) have a step:
-- N's operation at the shape Action assembles from a shape of M with
-- points of the fibers at its inputs, its decoding read back along M's
-- law (`step`). A morphism is a section of that step (`Morphism`): each
-- code goes to a code of N with an identification of decodings, and the
-- image of an operation is N's operation, with its decoding.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Fibers using (fiber)
open import SPT.Foundation.Induction.Initiality using (Section)

open import SPT.IR.Action using (assemble)
open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.IR.Description using (Desc; indexed)
open import SPT.IR.Restriction using (input)

------------------------------------------------------------------------
-- Morphisms

-- Over a shape z of M with a point of the fibers at each input, N's
-- operation at the assembled shape decodes to z's output by N's law and
-- the assembly, so to the decoding of M's operation at z, back along M's
-- law. A morphism sends every code of M into its fiber so that the image
-- of an operation is this step at the images of the inputs.

Fibers :
  {s κ κ′ j : Level} {E : Set j} {γ : Desc {s = s} E}
  (M : Algebra κ γ) (N : Algebra κ′ γ) → Algebra.K M → Set (κ′ ⊔ j)
Fibers M N k = fiber (Algebra.value N) (Algebra.value M k)

module _
  {s κ κ′ j : Level} {E : Set j} {γ : Desc {s = s} E}
  (extensionality : (A : Set s) → FunExt A (λ _ → E))
  (M : Algebra κ γ) (N : Algebra κ′ γ) (law : Law M) (law′ : Law N)
  where

  open Algebra M using (K; value; operation)

  step : Argument-Step (input γ (indexed K value)) operation (Fibers M N)
  step z h =
    let w =
          assemble extensionality (indexed K value)
            (indexed (Algebra.K N) (Algebra.value N)) γ z h
    in Algebra.operation N (pr₁ w) , (law′ (pr₁ w) ∙ (pr₂ w ∙ law z ⁻¹))

  Morphism : Set (s ⊔ κ ⊔ κ′ ⊔ j)
  Morphism = Section (input γ (indexed K value)) operation (Fibers M N) step
