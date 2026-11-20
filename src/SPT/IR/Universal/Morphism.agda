{-# OPTIONS --safe --without-K #-}

module SPT.IR.Universal.Morphism where

-- Initiality of the universal type of IR.Universal among the lawful
-- algebras of its description. With its source induction (Source) it is
-- an algebra to which IR.Morphism.Initiality applies: the fold into
-- every lawful algebra is a morphism (`fold`), every morphism is the fold
-- pointwise (`unique`), and the morphisms form a contractible type
-- (`initial`).

open import SPT.Base
open import SPT.Foundation.Contractible using (is-contractible)
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Induction.Initiality using (Section; uniform)

open import SPT.IR.Universal using (U; value)
open import SPT.IR.Universal.Induction using (intro)
open import SPT.IR.Universal.Source using (algebra; law; source; source-β)
open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.IR.Description using (Desc; indexed)
open import SPT.IR.Morphism using (Fibers; step; Morphism)
import SPT.IR.Morphism.Initiality as Initiality
open import SPT.IR.Restriction using (Position; input)

------------------------------------------------------------------------
-- The fold, its uniqueness, and initiality

-- The motive of a morphism is the fibers of N's decoding, of level κ′ ⊔ d,
-- over a universal type of level s: extensionality for functions from
-- types of level s into it serves for the positions, the carrier and the
-- source arguments.

module _
  {s d κ′ : Level} {D : Set d} {γ : Desc {s = s} D}
  (extensionality : (A : Set s) → FunExt A (λ _ → D))
  (motive : (A : Set s) (B : A → Set (κ′ ⊔ d)) → FunExt A B)
  (N : Algebra κ′ γ) (law′ : Law N)
  where

  fold : Morphism extensionality (algebra γ) N (law γ) law′
  fold =
    Initiality.fold extensionality (algebra γ) N (law γ) law′
      (source γ (κ′ ⊔ d)) (source-β γ (κ′ ⊔ d) motive)

  unique :
    (h : Morphism extensionality (algebra γ) N (law γ) law′) (u : U γ)
    → Section.valuation fold u ＝ Section.valuation h u
  unique =
    Initiality.unique extensionality (algebra γ) N (law γ) law′
      (source γ (κ′ ⊔ d)) (source-β γ (κ′ ⊔ d) motive)
      ( λ z →
          motive (Position γ (indexed (U γ) (value γ)) z)
            ( λ p →
                Fibers (algebra γ) N
                  (input γ (indexed (U γ) (value γ)) z p)))

  initial :
    is-contractible (Morphism extensionality (algebra γ) N (law γ) law′)
  initial =
    Initiality.initial extensionality (algebra γ) N (law γ) law′
      (source γ (κ′ ⊔ d)) (source-β γ (κ′ ⊔ d) motive)
      ( uniform (input γ (indexed (U γ) (value γ))) (intro γ)
          (source γ (κ′ ⊔ d))
          (Fibers (algebra γ) N)
          (step extensionality (algebra γ) N (law γ) law′)
          motive motive motive)
