{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Model.Identity where

-- An identity structure on a Russell model (`Identity`). For a type a at
-- level m and terms x y of it, `identity m a x y` is a type at level m,
-- with `reflexivity`. Based path induction `path-induction m k a x M d y
-- w` has a motive M at level k over the points of a and the paths from x
-- to them, and a value d at x and reflexivity.
--
-- The laws: their types, J at reflexivity is d (β), and stability under
-- substitution. In the stability law, the motive is taken under its two
-- binders: the first along `under`, the second by replacing its last
-- variable.
--
-- Each law holds where the arguments have their types. The simplicial
-- model has them strictly, J with strict β.

open import SPT.Base hiding (_∘_; id)
open import SPT.MartinLof.Model.Russell using
  (Russell; Code; section; under)

record Identity {ℓ : Level} (R : Russell ℓ) : Set ℓ where
  open Russell R
  field
    identity : {Γ : Ob} (m : ℕ) → Tm Γ → Tm Γ → Tm Γ → Tm Γ
    reflexivity : {Γ : Ob} (m : ℕ) → Tm Γ → Tm Γ → Tm Γ
    path-induction :
      {Γ : Ob} (m k : ℕ) (a x : Tm Γ)
      → Tm (Γ ▸ a ▸ identity m (a [ p ]) (x [ p ]) (q a))
      → Tm Γ → Tm Γ → Tm Γ → Tm Γ

    identity-type :
      {Γ : Ob} (m : ℕ) (a x y : Tm Γ) → Code R m a → type-of x ＝ a
      → type-of y ＝ a → Code R m (identity m a x y)
    reflexivity-type :
      {Γ : Ob} (m : ℕ) (a x : Tm Γ) → Code R m a → type-of x ＝ a
      → type-of (reflexivity m a x) ＝ identity m a x x
    path-induction-type :
      {Γ : Ob} (m k : ℕ) (a x : Tm Γ)
      (M : Tm (Γ ▸ a ▸ identity m (a [ p ]) (x [ p ]) (q a)))
      (d y w : Tm Γ)
      → Code R m a → (tx : type-of x ＝ a) → Code R k M
      → type-of d ＝ M [ section R a x tx ⨾ reflexivity m a x ]
      → (ty : type-of y ＝ a) → type-of w ＝ identity m a x y
      → type-of (path-induction m k a x M d y w) ＝ M [ section R a y ty ⨾ w ]

    path-induction-reflexivity :
      {Γ : Ob} (m k : ℕ) (a x : Tm Γ)
      (M : Tm (Γ ▸ a ▸ identity m (a [ p ]) (x [ p ]) (q a))) (d : Tm Γ)
      → Code R m a → (tx : type-of x ＝ a) → Code R k M
      → type-of d ＝ M [ section R a x tx ⨾ reflexivity m a x ]
      → path-induction m k a x M d x (reflexivity m a x) ＝ d

    identity-[] :
      {Γ Δ : Ob} (m : ℕ) (a x y : Tm Γ) (σ : Hom Δ Γ)
      → Code R m a → type-of x ＝ a → type-of y ＝ a
      → identity m a x y [ σ ] ＝ identity m (a [ σ ]) (x [ σ ]) (y [ σ ])
    reflexivity-[] :
      {Γ Δ : Ob} (m : ℕ) (a x : Tm Γ) (σ : Hom Δ Γ)
      → Code R m a → type-of x ＝ a
      → reflexivity m a x [ σ ] ＝ reflexivity m (a [ σ ]) (x [ σ ])
    path-induction-[] :
      {Γ Δ : Ob} (m k : ℕ) (a x : Tm Γ)
      (M : Tm (Γ ▸ a ▸ identity m (a [ p ]) (x [ p ]) (q a)))
      (d y w : Tm Γ) (σ : Hom Δ Γ)
      → (ta : Code R m a) → (tx : type-of x ＝ a) → Code R k M
      → type-of d ＝ M [ section R a x tx ⨾ reflexivity m a x ]
      → type-of y ＝ a → type-of w ＝ identity m a x y
      → path-induction m k a x M d y w [ σ ]
        ＝ path-induction m k (a [ σ ]) (x [ σ ])
            (M [ under R m a σ ta ∘ p
               ⨾ q (identity m (a [ σ ] [ p ]) (x [ σ ] [ p ])
                     (q (a [ σ ]))) ])
            (d [ σ ]) (y [ σ ]) (w [ σ ])
