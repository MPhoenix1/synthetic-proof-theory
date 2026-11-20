{-# OPTIONS --safe --without-K #-}

module SPT.IR.Indexed.Induction.Initiality.Discriminator where

-- Ordinary induction at Indexed.Discriminator's universe, under any
-- extensionality for information. It transports along the comparison, so
-- it does not compute at a variable extensionality; uniqueness pins it to
-- native depth, which does (`depth-ordinary`, `nested-ordinary`: 2 at a
-- nested sum). At the strict order, which is not reflexive, it lies below
-- ordinary induction counting a sum twice (`depth-below`), and fusion
-- carries it along the successor (`successor-fusion`). Each method is a
-- native one read at native arguments (Initiality.Discriminator's).

open import SPT.Base
open import SPT.Foundation.Isomorphisms using (backward)

open import SPT.IR.Indexed using (U)
open import SPT.IR.Indexed.Comparison using (arguments)
open import SPT.IR.Indexed.Discriminator using
  (universe; Depth; step; depth; unit; sum; nested-depth)
open import SPT.IR.Indexed.Induction using (ind)
open import SPT.IR.Indexed.Induction.Initiality using
  (ind-rel; ordinary; agrees-with-native; ind-fusion)
open import SPT.IR.Indexed.Initiality.Discriminator using
  ( depth-congruent; Below; twice; related; successor; shifted
  ; shifted-congruent; carries)
open import SPT.IR.Polynomial using
  (Scheme; shape; Extensionality)

------------------------------------------------------------------------
-- Ordinary depth is native depth

-- The native step read at native arguments is congruent where the native
-- one is, so ordinary induction with it is native depth, and its value at
-- a closed code is the native one, computed by refl.

module _ (extensionality : Extensionality lzero (lsuc lzero)) where

  depth-ordinary :
    (u : U universe ⋆)
    → depth u
      ＝ ind extensionality universe Depth
          (ordinary extensionality universe Depth step) ⋆ u
  depth-ordinary =
    agrees-with-native extensionality universe Depth step depth-congruent ⋆

  nested-ordinary :
    ind extensionality universe Depth
      (ordinary extensionality universe Depth step) ⋆
      (sum (sum unit (λ x → unit)) (λ x → unit))
    ＝ suc (suc zero)
  nested-ordinary =
    depth-ordinary (sum (sum unit (λ x → unit)) (λ x → unit)) ⁻¹
    ∙ nested-depth

------------------------------------------------------------------------
-- Ordinary depth lies strictly below a second ordinary induction

-- The native clauses of depth and `twice` are related at the strict
-- order at every native argument, so at every ordinary one.

module _ (extensionality : Extensionality lzero (lsuc lzero)) where

  depth-below :
    (u : U universe ⋆)
    → ind extensionality universe Depth
        (ordinary extensionality universe Depth step) ⋆ u
      <ℕˢ ind extensionality universe Depth
            (ordinary extensionality universe Depth twice) ⋆ u
  depth-below =
    ind-rel extensionality universe Depth Depth Below
      (ordinary extensionality universe Depth step)
      (ordinary extensionality universe Depth twice)
      ( λ i b →
          related i
            (backward
              (arguments extensionality universe
                (shape (Scheme.rule universe i)))
              b))
      ⋆

------------------------------------------------------------------------
-- Fusion along the successor

-- The successor carries depth's native clauses to `shifted`'s at every
-- native argument, and `shifted` is congruent there.

module _ (extensionality : Extensionality lzero (lsuc lzero)) where

  successor-fusion :
    (u : U universe ⋆)
    → suc
        (ind extensionality universe Depth
          (ordinary extensionality universe Depth step) ⋆ u)
      ＝ ind extensionality universe Depth
          (ordinary extensionality universe Depth shifted) ⋆ u
  successor-fusion =
    ind-fusion extensionality universe Depth Depth successor
      (ordinary extensionality universe Depth step)
      (ordinary extensionality universe Depth shifted)
      ( λ i b →
          shifted-congruent i
            (backward
              (arguments extensionality universe
                (shape (Scheme.rule universe i)))
              b))
      ( λ i b →
          carries i
            (backward
              (arguments extensionality universe
                (shape (Scheme.rule universe i)))
              b))
      ⋆
