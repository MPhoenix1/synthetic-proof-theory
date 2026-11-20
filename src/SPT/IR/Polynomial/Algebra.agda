{-# OPTIONS --safe --without-K #-}

module SPT.IR.Polynomial.Algebra where

-- An algebra of a scheme: a family of small carriers with readouts, and at
-- each index an operation on the arguments of that index's rule over the
-- family (`Algebra`), whose law says that it reads out to the rule's output
-- (`law`).

open import SPT.Base

open import SPT.IR.Polynomial using
  (Family; carrier; readout; Args; info; shape; output; Scheme)

record Algebra {ℓ κ : Level} (s : Scheme ℓ κ) : Set (lsuc ℓ ⊔ κ) where
  field
    family : Family ℓ κ (Scheme.Data s)
    operation :
      (i : Scheme.Index s) → Args (shape (Scheme.rule s i)) family
      → carrier family i
    law :
      (i : Scheme.Index s) (a : Args (shape (Scheme.rule s i)) family)
      → readout family i (operation i a)
        ＝ output (Scheme.rule s i)
            (info (shape (Scheme.rule s i)) family a)
