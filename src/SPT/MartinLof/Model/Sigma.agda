{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Model.Sigma where

-- A Σ-structure on a Russell model (`Sigma`). For a type a at level m and
-- a type b at level k over it, `sigma m k a b` is a type at level m ⊔ k,
-- with `pair`, `first` and `second`. The laws: their types, both
-- projections of a pair (β), the pair of the projections (η), and
-- stability under substitution.
--
-- Each law holds where the arguments have their types. The simplicial
-- model has them strictly.

open import SPT.Base hiding (_∘_; id)
open import SPT.MartinLof.Model.Russell using (Russell; Code)

record Sigma {ℓ : Level} (R : Russell ℓ) : Set ℓ where
  open Russell R
  field
    sigma : {Γ : Ob} (m k : ℕ) (a : Tm Γ) → Tm (Γ ▸ a) → Tm Γ
    pair :
      {Γ : Ob} (m k : ℕ) (a : Tm Γ) → Tm (Γ ▸ a) → Tm Γ → Tm Γ → Tm Γ
    first : {Γ : Ob} (m k : ℕ) (a : Tm Γ) → Tm (Γ ▸ a) → Tm Γ → Tm Γ
    second : {Γ : Ob} (m k : ℕ) (a : Tm Γ) → Tm (Γ ▸ a) → Tm Γ → Tm Γ

    sigma-type :
      {Γ : Ob} (m k : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a))
      → Code R m a → Code R k b → Code R (m ⊔ℕ k) (sigma m k a b)
    pair-type :
      {Γ : Ob} (m k : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a)) (x y : Tm Γ)
      → Code R m a → Code R k b → type-of x ＝ a → type-of y ＝ b [ id ⨾ x ]
      → type-of (pair m k a b x y) ＝ sigma m k a b
    first-type :
      {Γ : Ob} (m k : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a)) (z : Tm Γ)
      → Code R m a → Code R k b → type-of z ＝ sigma m k a b
      → type-of (first m k a b z) ＝ a
    second-type :
      {Γ : Ob} (m k : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a)) (z : Tm Γ)
      → Code R m a → Code R k b → type-of z ＝ sigma m k a b
      → type-of (second m k a b z) ＝ b [ id ⨾ first m k a b z ]

    first-pair :
      {Γ : Ob} (m k : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a)) (x y : Tm Γ)
      → Code R m a → Code R k b → type-of x ＝ a → type-of y ＝ b [ id ⨾ x ]
      → first m k a b (pair m k a b x y) ＝ x
    second-pair :
      {Γ : Ob} (m k : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a)) (x y : Tm Γ)
      → Code R m a → Code R k b → type-of x ＝ a → type-of y ＝ b [ id ⨾ x ]
      → second m k a b (pair m k a b x y) ＝ y
    pair-projections :
      {Γ : Ob} (m k : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a)) (z : Tm Γ)
      → Code R m a → Code R k b → type-of z ＝ sigma m k a b
      → pair m k a b (first m k a b z) (second m k a b z) ＝ z

    sigma-[] :
      {Γ Δ : Ob} (m k : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a)) (σ : Hom Δ Γ)
      → Code R m a → Code R k b
      → sigma m k a b [ σ ] ＝ sigma m k (a [ σ ]) (b [ σ ∘ p ⨾ q (a [ σ ]) ])
    pair-[] :
      {Γ Δ : Ob} (m k : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a)) (x y : Tm Γ)
      (σ : Hom Δ Γ)
      → Code R m a → Code R k b → type-of x ＝ a → type-of y ＝ b [ id ⨾ x ]
      → pair m k a b x y [ σ ]
        ＝ pair m k (a [ σ ]) (b [ σ ∘ p ⨾ q (a [ σ ]) ]) (x [ σ ]) (y [ σ ])
    first-[] :
      {Γ Δ : Ob} (m k : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a)) (z : Tm Γ)
      (σ : Hom Δ Γ)
      → Code R m a → Code R k b → type-of z ＝ sigma m k a b
      → first m k a b z [ σ ]
        ＝ first m k (a [ σ ]) (b [ σ ∘ p ⨾ q (a [ σ ]) ]) (z [ σ ])
    second-[] :
      {Γ Δ : Ob} (m k : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a)) (z : Tm Γ)
      (σ : Hom Δ Γ)
      → Code R m a → Code R k b → type-of z ＝ sigma m k a b
      → second m k a b z [ σ ]
        ＝ second m k (a [ σ ]) (b [ σ ∘ p ⨾ q (a [ σ ]) ]) (z [ σ ])
