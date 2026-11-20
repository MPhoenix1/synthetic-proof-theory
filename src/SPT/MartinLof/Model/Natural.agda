{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Model.Natural where

-- An ℕ-structure on a Russell model (`Natural`). `natural` is a closed
-- type at level 0 and `zero` a closed term of it, both read in a context Γ
-- along ε Γ; `successor` maps terms of it to terms of it. Induction
-- `natural-induction l M z s t` has a motive M at level l over it, a
-- value z at zero, and a step s over a number and a value of M there.
--
-- The laws: their types, induction at zero and at a successor (β), and
-- stability under substitution. In the stability law, the step is taken
-- under its two binders: the first by extending along a typing proof (the
-- closed type is read along ε twice), the second by replacing its last
-- variable.
--
-- Each law holds where the arguments have their types. The simplicial
-- model has them strictly.

open import SPT.Base hiding (_∘_; id; zero)
open import SPT.MartinLof.Model.Russell using (Russell; Code; section)

record Natural {ℓ : Level} (R : Russell ℓ) : Set ℓ where
  open Russell R
  field
    natural : Tm ◇
    zero : Tm ◇
    successor : {Γ : Ob} → Tm Γ → Tm Γ
    natural-induction :
      {Γ : Ob} (l : ℕ) (M : Tm (Γ ▸ natural [ ε Γ ])) → Tm Γ
      → Tm (Γ ▸ natural [ ε Γ ] ▸ M) → Tm Γ → Tm Γ

    natural-type : type-of natural ＝ universe 0
    zero-type : type-of zero ＝ natural
    successor-type :
      {Γ : Ob} (t : Tm Γ) → type-of t ＝ natural [ ε Γ ]
      → type-of (successor t) ＝ natural [ ε Γ ]
    natural-induction-type :
      {Γ : Ob} (l : ℕ) (M : Tm (Γ ▸ natural [ ε Γ ])) (z : Tm Γ)
      (s : Tm (Γ ▸ natural [ ε Γ ] ▸ M)) (t : Tm Γ)
      → Code R l M → type-of z ＝ M [ id ⨾ zero [ ε Γ ] ]
      → type-of s ＝ M [ p ∘ p ⨾ successor (q (natural [ ε Γ ]) [ p ]) ]
      → type-of t ＝ natural [ ε Γ ]
      → type-of (natural-induction l M z s t) ＝ M [ id ⨾ t ]

    natural-induction-zero :
      {Γ : Ob} (l : ℕ) (M : Tm (Γ ▸ natural [ ε Γ ])) (z : Tm Γ)
      (s : Tm (Γ ▸ natural [ ε Γ ] ▸ M))
      → Code R l M → type-of z ＝ M [ id ⨾ zero [ ε Γ ] ]
      → type-of s ＝ M [ p ∘ p ⨾ successor (q (natural [ ε Γ ]) [ p ]) ]
      → natural-induction l M z s (zero [ ε Γ ]) ＝ z
    natural-induction-successor :
      {Γ : Ob} (l : ℕ) (M : Tm (Γ ▸ natural [ ε Γ ])) (z : Tm Γ)
      (s : Tm (Γ ▸ natural [ ε Γ ] ▸ M)) (t : Tm Γ)
      → Code R l M → type-of z ＝ M [ id ⨾ zero [ ε Γ ] ]
      → type-of s ＝ M [ p ∘ p ⨾ successor (q (natural [ ε Γ ]) [ p ]) ]
      → (⋆ : type-of t ＝ natural [ ε Γ ])
      → natural-induction l M z s (successor t)
        ＝ s [ section R (natural [ ε Γ ]) t ⋆
            ⨾ natural-induction l M z s t ]

    successor-[] :
      {Γ Δ : Ob} (t : Tm Γ) (σ : Hom Δ Γ) → type-of t ＝ natural [ ε Γ ]
      → successor t [ σ ] ＝ successor (t [ σ ])
    natural-induction-[] :
      {Γ Δ : Ob} (l : ℕ) (M : Tm (Γ ▸ natural [ ε Γ ])) (z : Tm Γ)
      (s : Tm (Γ ▸ natural [ ε Γ ] ▸ M)) (t : Tm Γ) (σ : Hom Δ Γ)
      → Code R l M → type-of z ＝ M [ id ⨾ zero [ ε Γ ] ]
      → type-of s ＝ M [ p ∘ p ⨾ successor (q (natural [ ε Γ ]) [ p ]) ]
      → type-of t ＝ natural [ ε Γ ]
      → (e : type-of (q (natural [ ε Δ ])) ＝ natural [ ε Γ ] [ σ ∘ p ])
      → natural-induction l M z s t [ σ ]
        ＝ natural-induction l (M [ σ ∘ p ⨾ q (natural [ ε Δ ]) ]) (z [ σ ])
            (s [ extend (natural [ ε Γ ]) (σ ∘ p) (q (natural [ ε Δ ])) e
                 ∘ p
               ⨾ q (M [ σ ∘ p ⨾ q (natural [ ε Δ ]) ]) ])
            (t [ σ ])
