{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Model.Pi where

-- A Π-structure on a Russell model (`Pi`). For a type a at level m and a
-- type b at level k over it, `pi m k a b` is a type at level m ⊔ k, with
-- `lambda` and `application`. The laws:
-- - their types;
-- - β: application of a lambda is its body at the argument;
-- - η: the lambda of λ x. f x is f, where the application carries a
--   weakened and b with its bound variable kept and the others weakened
--   twice;
-- - stability under substitution, with b taken under the binder by
--   replacing its last variable.
--
-- Each law holds where the arguments have their types. The simplicial
-- model has them strictly (Kapulkin–Lumsdaine Thm 2.3.4, η Prop. 2.3.6).

open import SPT.Base hiding (_∘_; id)
open import SPT.MartinLof.Model.Russell using (Russell; Code)

record Pi {ℓ : Level} (R : Russell ℓ) : Set ℓ where
  open Russell R
  field
    pi : {Γ : Ob} (m k : ℕ) (a : Tm Γ) → Tm (Γ ▸ a) → Tm Γ
    lambda : {Γ : Ob} (m k : ℕ) (a : Tm Γ) → Tm (Γ ▸ a) → Tm (Γ ▸ a) → Tm Γ
    application :
      {Γ : Ob} (m k : ℕ) (a : Tm Γ) → Tm (Γ ▸ a) → Tm Γ → Tm Γ → Tm Γ

    pi-type :
      {Γ : Ob} (m k : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a))
      → Code R m a → Code R k b → Code R (m ⊔ℕ k) (pi m k a b)
    lambda-type :
      {Γ : Ob} (m k : ℕ) (a : Tm Γ) (b t : Tm (Γ ▸ a))
      → Code R m a → Code R k b → type-of t ＝ b
      → type-of (lambda m k a b t) ＝ pi m k a b
    application-type :
      {Γ : Ob} (m k : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a)) (f x : Tm Γ)
      → Code R m a → Code R k b → type-of f ＝ pi m k a b → type-of x ＝ a
      → type-of (application m k a b f x) ＝ b [ id ⨾ x ]

    application-lambda :
      {Γ : Ob} (m k : ℕ) (a : Tm Γ) (b t : Tm (Γ ▸ a)) (x : Tm Γ)
      → Code R m a → Code R k b → type-of t ＝ b → type-of x ＝ a
      → application m k a b (lambda m k a b t) x ＝ t [ id ⨾ x ]
    lambda-application :
      {Γ : Ob} (m k : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a)) (f : Tm Γ)
      → Code R m a → Code R k b → type-of f ＝ pi m k a b
      → lambda m k a b
          (application m k (a [ p ]) (b [ p ∘ p ⨾ q (a [ p ]) ]) (f [ p ])
            (q a))
        ＝ f

    pi-[] :
      {Γ Δ : Ob} (m k : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a)) (σ : Hom Δ Γ)
      → Code R m a → Code R k b
      → pi m k a b [ σ ] ＝ pi m k (a [ σ ]) (b [ σ ∘ p ⨾ q (a [ σ ]) ])
    lambda-[] :
      {Γ Δ : Ob} (m k : ℕ) (a : Tm Γ) (b t : Tm (Γ ▸ a)) (σ : Hom Δ Γ)
      → Code R m a → Code R k b → type-of t ＝ b
      → lambda m k a b t [ σ ]
        ＝ lambda m k (a [ σ ]) (b [ σ ∘ p ⨾ q (a [ σ ]) ])
            (t [ σ ∘ p ⨾ q (a [ σ ]) ])
    application-[] :
      {Γ Δ : Ob} (m k : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a)) (f x : Tm Γ)
      (σ : Hom Δ Γ)
      → Code R m a → Code R k b → type-of f ＝ pi m k a b → type-of x ＝ a
      → application m k a b f x [ σ ]
        ＝ application m k (a [ σ ]) (b [ σ ∘ p ⨾ q (a [ σ ]) ]) (f [ σ ])
            (x [ σ ])
