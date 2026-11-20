{-# OPTIONS --safe --without-K #-}

module SPT.IR.Morphism.Fusion where

-- Fusion among algebras with their laws: a morphism after the fold is the
-- fold into its codomain, pointwise in the fibers (`fusion`), for any
-- algebra with induction on source arguments and its computation identity.
-- It is uniqueness of the fold, since a composite of morphisms is a
-- morphism (Composition). The generated part of every algebra is such an
-- algebra (`generated-fusion`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Induction.Initiality using (Section)

open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.IR.Description using (Desc; indexed)
import SPT.IR.Generated as Generated
open import SPT.IR.Induction.Generated using (source; source-β)
open import SPT.IR.Layers using (normal)
open import SPT.IR.Morphism using (Fibers; Morphism)
open import SPT.IR.Morphism.Composition using (compose)
open import SPT.IR.Morphism.Initiality using
  (fold; unique; generated; generated-fold)
import SPT.IR.Polynomial as Polynomial
open import SPT.IR.Restriction using (Position; input)

------------------------------------------------------------------------
-- A morphism after the fold

-- The composite of h with the fold into N is a morphism into P, so it is
-- the fold into P at every code, its identification of decodings included.

module _
  {s κ κ′ κ″ j : Level} {E : Set j} {γ : Desc {s = s} E}
  (arities : (A : Set s) (B : A → Set j) → FunExt A B)
  (positions′ : (A : Set s) (B : A → Set (κ′ ⊔ j)) → FunExt A B)
  (positions″ : (A : Set s) (B : A → Set (κ″ ⊔ j)) → FunExt A B)
  (M : Algebra κ γ) (N : Algebra κ′ γ) (P : Algebra κ″ γ)
  (law : Law M) (law′ : Law N) (law″ : Law P)
  (ind′ :
    Argument-Induction (input γ (indexed (Algebra.K M) (Algebra.value M)))
      (Algebra.operation M) (κ′ ⊔ j))
  (computation′ :
    Argument-Computation (input γ (indexed (Algebra.K M) (Algebra.value M)))
      (Algebra.operation M) ind′)
  (ind″ :
    Argument-Induction (input γ (indexed (Algebra.K M) (Algebra.value M)))
      (Algebra.operation M) (κ″ ⊔ j))
  (computation″ :
    Argument-Computation (input γ (indexed (Algebra.K M) (Algebra.value M)))
      (Algebra.operation M) ind″)
  (h : Morphism (normal E arities) N P law′ law″)
  where

  open Algebra M using (K; value)

  fusion :
    (k : K)
    → Section.valuation
        ( compose arities positions′ positions″ M N P law law′ law″ h
            (fold (normal E arities) M N law law′ ind′ computation′))
        k
      ＝ Section.valuation
          (fold (normal E arities) M P law law″ ind″ computation″) k
  fusion k =
    unique (normal E arities) M P law law″ ind″ computation″
      ( λ z →
          positions″ (Position γ (indexed K value) z)
            (λ p → Fibers M P (input γ (indexed K value) z p)))
      ( compose arities positions′ positions″ M N P law law′ law″ h
          (fold (normal E arities) M N law law′ ind′ computation′))
      k
    ⁻¹

------------------------------------------------------------------------
-- The generated part

module _
  {s κ κ′ κ″ j : Level} {E : Set j} {γ : Desc {s = s} E}
  (arities : (A : Set s) (B : A → Set j) → FunExt A B)
  (positions : Polynomial.Extensionality s κ)
  (motive′ : (A : Set s) (B : A → Set (κ′ ⊔ j)) → FunExt A B)
  (motive″ : (A : Set s) (B : A → Set (κ″ ⊔ j)) → FunExt A B)
  (M : Algebra κ γ) (law : Law M)
  (N : Algebra κ′ γ) (law′ : Law N) (P : Algebra κ″ γ) (law″ : Law P)
  (h : Morphism (normal E arities) N P law′ law″)
  where

  generated-fusion :
    (g : Generated.G M)
    → Section.valuation
        ( compose arities motive′ motive″ (generated M) N P
            (Generated.make-β M law) law′ law″ h
            ( generated-fold (normal E arities) positions motive′ M law N
                law′))
        g
      ＝ Section.valuation
          ( generated-fold (normal E arities) positions motive″ M law P
              law″)
          g
  generated-fusion =
    fusion arities motive′ motive″ (generated M) N P
      (Generated.make-β M law) law′ law″
      (source M positions (κ′ ⊔ j))
      (source-β M positions (κ′ ⊔ j) motive′)
      (source M positions (κ″ ⊔ j))
      (source-β M positions (κ″ ⊔ j) motive″)
      h
