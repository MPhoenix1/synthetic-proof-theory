{-# OPTIONS --safe --without-K #-}

module SPT.IR.Smallness.Initiality where

-- The induction–recursion that smallness derives has a unique eliminator:
-- every valuation satisfying the computation equations of congruent
-- methods is Smallness's induction (`ind-unique`). This is
-- Generated.Initiality at a description's small algebra, which also gives
-- there the relational form, the fundamental theorem and fusion.

open import SPT.Base

open import SPT.IR.Description using (Desc)
import SPT.IR.Generated.Initiality as Initiality
open import SPT.IR.Smallness using (Smallness; G; Method; ind)

------------------------------------------------------------------------
-- Uniqueness of induction from smallness

-- The carrier, methods and induction of Smallness are those of Generated
-- at the small algebra, so the theorem is an instance there.

module _
  {ℓ ν : Level} (small : Smallness ℓ) (γ : Desc {s = ℓ} (Set ℓ))
  (P : G small γ → Set ν)
  where

  ind-unique :
    (v : (g : G small γ) → P g) (m : Method small γ P)
    → Initiality.Congruent (Smallness.algebra small γ) P m
    → Initiality.Homomorphic (Smallness.algebra small γ) P v m
    → (g : G small γ) → v g ＝ ind small γ P m g
  ind-unique = Initiality.ind-unique (Smallness.algebra small γ) P
