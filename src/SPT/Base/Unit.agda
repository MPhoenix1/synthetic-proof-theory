{-# OPTIONS --safe --without-K #-}

module SPT.Base.Unit where

-- The unit type `𝟙` has exactly one point, `⋆`. It is the record of
-- `Agda.Builtin.Unit`, under SPT's names given in the renaming; it has no
-- fields, so every point of it is `⋆` by eta, definitionally.

open import Agda.Builtin.Unit public
  renaming (⊤ to 𝟙; tt to ⋆)

open import SPT.Base.Identity using (_＝_; refl)

------------------------------------------------------------------------
-- Properties

every-point-is-⋆ : (u : 𝟙) → u ＝ ⋆
every-point-is-⋆ u = refl
