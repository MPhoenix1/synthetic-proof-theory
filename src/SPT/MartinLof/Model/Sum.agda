{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Model.Sum where

-- A +-structure on a Russell model (`Sum`). For types a at level m and b
-- at level k, `sum m k a b` is a type at level m ⊔ k, with `left` and
-- `right`. Case analysis `case m k l a b M c d s` has a motive M at level
-- l over the sum, a method c at left x over a and a method d at right y
-- over b. The laws: their types, case at left and at right (β), and
-- stability under substitution.
--
-- Each law holds where the arguments have their types. The simplicial
-- model has them strictly.

open import SPT.Base hiding (_∘_; id)
open import SPT.MartinLof.Model.Russell using (Russell; Code)

record Sum {ℓ : Level} (R : Russell ℓ) : Set ℓ where
  open Russell R
  field
    sum : {Γ : Ob} (m k : ℕ) → Tm Γ → Tm Γ → Tm Γ
    left : {Γ : Ob} (m k : ℕ) → Tm Γ → Tm Γ → Tm Γ → Tm Γ
    right : {Γ : Ob} (m k : ℕ) → Tm Γ → Tm Γ → Tm Γ → Tm Γ
    case :
      {Γ : Ob} (m k l : ℕ) (a b : Tm Γ) → Tm (Γ ▸ sum m k a b)
      → Tm (Γ ▸ a) → Tm (Γ ▸ b) → Tm Γ → Tm Γ

    sum-type :
      {Γ : Ob} (m k : ℕ) (a b : Tm Γ) → Code R m a → Code R k b
      → Code R (m ⊔ℕ k) (sum m k a b)
    left-type :
      {Γ : Ob} (m k : ℕ) (a b x : Tm Γ) → Code R m a → Code R k b
      → type-of x ＝ a → type-of (left m k a b x) ＝ sum m k a b
    right-type :
      {Γ : Ob} (m k : ℕ) (a b y : Tm Γ) → Code R m a → Code R k b
      → type-of y ＝ b → type-of (right m k a b y) ＝ sum m k a b
    case-type :
      {Γ : Ob} (m k l : ℕ) (a b : Tm Γ) (M : Tm (Γ ▸ sum m k a b))
      (c : Tm (Γ ▸ a)) (d : Tm (Γ ▸ b)) (s : Tm Γ)
      → Code R m a → Code R k b → Code R l M
      → type-of c ＝ M [ p ⨾ left m k (a [ p ]) (b [ p ]) (q a) ]
      → type-of d ＝ M [ p ⨾ right m k (a [ p ]) (b [ p ]) (q b) ]
      → type-of s ＝ sum m k a b
      → type-of (case m k l a b M c d s) ＝ M [ id ⨾ s ]

    case-left :
      {Γ : Ob} (m k l : ℕ) (a b : Tm Γ) (M : Tm (Γ ▸ sum m k a b))
      (c : Tm (Γ ▸ a)) (d : Tm (Γ ▸ b)) (x : Tm Γ)
      → Code R m a → Code R k b → Code R l M
      → type-of c ＝ M [ p ⨾ left m k (a [ p ]) (b [ p ]) (q a) ]
      → type-of d ＝ M [ p ⨾ right m k (a [ p ]) (b [ p ]) (q b) ]
      → type-of x ＝ a
      → case m k l a b M c d (left m k a b x) ＝ c [ id ⨾ x ]
    case-right :
      {Γ : Ob} (m k l : ℕ) (a b : Tm Γ) (M : Tm (Γ ▸ sum m k a b))
      (c : Tm (Γ ▸ a)) (d : Tm (Γ ▸ b)) (y : Tm Γ)
      → Code R m a → Code R k b → Code R l M
      → type-of c ＝ M [ p ⨾ left m k (a [ p ]) (b [ p ]) (q a) ]
      → type-of d ＝ M [ p ⨾ right m k (a [ p ]) (b [ p ]) (q b) ]
      → type-of y ＝ b
      → case m k l a b M c d (right m k a b y) ＝ d [ id ⨾ y ]

    sum-[] :
      {Γ Δ : Ob} (m k : ℕ) (a b : Tm Γ) (σ : Hom Δ Γ)
      → Code R m a → Code R k b
      → sum m k a b [ σ ] ＝ sum m k (a [ σ ]) (b [ σ ])
    left-[] :
      {Γ Δ : Ob} (m k : ℕ) (a b x : Tm Γ) (σ : Hom Δ Γ)
      → Code R m a → Code R k b → type-of x ＝ a
      → left m k a b x [ σ ] ＝ left m k (a [ σ ]) (b [ σ ]) (x [ σ ])
    right-[] :
      {Γ Δ : Ob} (m k : ℕ) (a b y : Tm Γ) (σ : Hom Δ Γ)
      → Code R m a → Code R k b → type-of y ＝ b
      → right m k a b y [ σ ] ＝ right m k (a [ σ ]) (b [ σ ]) (y [ σ ])
    case-[] :
      {Γ Δ : Ob} (m k l : ℕ) (a b : Tm Γ) (M : Tm (Γ ▸ sum m k a b))
      (c : Tm (Γ ▸ a)) (d : Tm (Γ ▸ b)) (s : Tm Γ) (σ : Hom Δ Γ)
      → Code R m a → Code R k b → Code R l M
      → type-of c ＝ M [ p ⨾ left m k (a [ p ]) (b [ p ]) (q a) ]
      → type-of d ＝ M [ p ⨾ right m k (a [ p ]) (b [ p ]) (q b) ]
      → type-of s ＝ sum m k a b
      → case m k l a b M c d s [ σ ]
        ＝ case m k l (a [ σ ]) (b [ σ ])
            (M [ σ ∘ p ⨾ q (sum m k (a [ σ ]) (b [ σ ])) ])
            (c [ σ ∘ p ⨾ q (a [ σ ]) ]) (d [ σ ∘ p ⨾ q (b [ σ ]) ])
            (s [ σ ])
