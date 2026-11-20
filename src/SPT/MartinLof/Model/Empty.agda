{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Model.Empty where

-- A 0-structure on a Russell model (`Empty`). `empty` is a closed type at
-- level 0, read in a context Γ along ε Γ. `absurd k M t` eliminates a term
-- t of it into a motive M at level k over it. The laws: their types and
-- stability under substitution.
--
-- Each law holds where the arguments have their types. A model in which
-- no closed term has type `empty` is one in which the core theory derives
-- no closed term of 0.

open import SPT.Base hiding (_∘_; id)
open import SPT.MartinLof.Model.Russell using (Russell; Code)

record Empty {ℓ : Level} (R : Russell ℓ) : Set ℓ where
  open Russell R
  field
    empty : Tm ◇
    absurd : {Γ : Ob} (k : ℕ) → Tm (Γ ▸ empty [ ε Γ ]) → Tm Γ → Tm Γ

    empty-type : type-of empty ＝ universe 0
    absurd-type :
      {Γ : Ob} (k : ℕ) (M : Tm (Γ ▸ empty [ ε Γ ])) (t : Tm Γ)
      → Code R k M → type-of t ＝ empty [ ε Γ ]
      → type-of (absurd k M t) ＝ M [ id ⨾ t ]

    absurd-[] :
      {Γ Δ : Ob} (k : ℕ) (M : Tm (Γ ▸ empty [ ε Γ ])) (t : Tm Γ)
      (σ : Hom Δ Γ)
      → Code R k M → type-of t ＝ empty [ ε Γ ]
      → absurd k M t [ σ ]
        ＝ absurd k (M [ σ ∘ p ⨾ q (empty [ ε Δ ]) ]) (t [ σ ])
