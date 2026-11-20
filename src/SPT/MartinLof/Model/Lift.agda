{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Model.Lift where

-- A Lift-structure on a Russell model (`Lift`). For a type a at level m,
-- `lifted m k a` is a type at level m ⊔ k, with `lift` into it and
-- `lower` out of it. The laws: their types, lower (lift x) = x, and
-- lift (lower y) = y, all stable under substitution.
--
-- Each law holds where the arguments have their types. In the simplicial
-- model the code is the inclusion of the universe at m into the one at
-- m ⊔ k, and lift and lower are identities.

open import SPT.Base hiding (Lift; _∘_; id; lift; lower)
open import SPT.MartinLof.Model.Russell using (Russell; Code)

record Lift {ℓ : Level} (R : Russell ℓ) : Set ℓ where
  open Russell R
  field
    lifted : {Γ : Ob} (m k : ℕ) → Tm Γ → Tm Γ
    lift : {Γ : Ob} (m k : ℕ) → Tm Γ → Tm Γ → Tm Γ
    lower : {Γ : Ob} (m k : ℕ) → Tm Γ → Tm Γ → Tm Γ

    lifted-type :
      {Γ : Ob} (m k : ℕ) (a : Tm Γ) → Code R m a
      → Code R (m ⊔ℕ k) (lifted m k a)
    lift-type :
      {Γ : Ob} (m k : ℕ) (a x : Tm Γ) → Code R m a → type-of x ＝ a
      → type-of (lift m k a x) ＝ lifted m k a
    lower-type :
      {Γ : Ob} (m k : ℕ) (a y : Tm Γ) → Code R m a
      → type-of y ＝ lifted m k a → type-of (lower m k a y) ＝ a

    lower-lift :
      {Γ : Ob} (m k : ℕ) (a x : Tm Γ) → Code R m a → type-of x ＝ a
      → lower m k a (lift m k a x) ＝ x
    lift-lower :
      {Γ : Ob} (m k : ℕ) (a y : Tm Γ) → Code R m a
      → type-of y ＝ lifted m k a → lift m k a (lower m k a y) ＝ y

    lifted-[] :
      {Γ Δ : Ob} (m k : ℕ) (a : Tm Γ) (σ : Hom Δ Γ) → Code R m a
      → lifted m k a [ σ ] ＝ lifted m k (a [ σ ])
    lift-[] :
      {Γ Δ : Ob} (m k : ℕ) (a x : Tm Γ) (σ : Hom Δ Γ) → Code R m a
      → type-of x ＝ a → lift m k a x [ σ ] ＝ lift m k (a [ σ ]) (x [ σ ])
    lower-[] :
      {Γ Δ : Ob} (m k : ℕ) (a y : Tm Γ) (σ : Hom Δ Γ) → Code R m a
      → type-of y ＝ lifted m k a
      → lower m k a y [ σ ] ＝ lower m k (a [ σ ]) (y [ σ ])
