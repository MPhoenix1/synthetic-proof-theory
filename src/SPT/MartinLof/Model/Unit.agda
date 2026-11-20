{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Model.Unit where

-- A 1-structure on a Russell model (`Unit`). `unit` is a closed type at
-- level 0 and `star` a closed term of it, both read in a context Γ along
-- ε Γ. Every term of type unit is star (η). Closed terms need no law of
-- substitution: one follows from the category's.

open import SPT.Base hiding (_∘_; id)
open import SPT.MartinLof.Model.Russell using (Russell)

record Unit {ℓ : Level} (R : Russell ℓ) : Set ℓ where
  open Russell R
  field
    unit : Tm ◇
    star : Tm ◇

    unit-type : type-of unit ＝ universe 0
    star-type : type-of star ＝ unit

    star-unique :
      {Γ : Ob} (t : Tm Γ) → type-of t ＝ unit [ ε Γ ] → t ＝ star [ ε Γ ]
