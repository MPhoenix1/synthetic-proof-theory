{-# OPTIONS --safe --without-K --no-projection-like #-}

module SPT.MartinLof.Model.WellFounded where

-- A W-structure on a Russell model with a Π-structure (`WellFounded`).
-- For a type a at level m and a type b at level k over it, `tree m k a b`
-- is a type at level m ⊔ k, with `supremum` taking a shape x and children
-- f : b x → tree. Induction into a motive M at level l is given at the
-- generic tree, a term of M over the extension by the tree
-- (`tree-induction`); at a tree w it is that term with its variable
-- replaced by w. Its method lives over a shape x, children f, and
-- hypotheses h : (y : b x) → M (f y). The three types are named once:
-- `children-type`, `hypotheses-type` and `method-context`.
--
-- The laws:
-- - their types;
-- - β: induction at a supremum is the method at its shape, its children,
--   and λ y. the generic term at f y; given at the generic tree, the
--   recursive value needs no copy of the method under the new binder;
-- - stability under substitution, with the method taken under its three
--   binders: two by extending, the last by replacing its last variable.
--
-- Each law holds where the arguments have their types. The simplicial
-- model has them strictly (Kapulkin–Lumsdaine Thm 2.3.4).

open import SPT.Base hiding (_∘_; id)
open import SPT.MartinLof.Model.Pi using (Pi)
open import SPT.MartinLof.Model.Russell using
  (Russell; Code; section; under)

------------------------------------------------------------------------
-- The context of the induction method

module _ {ℓ : Level} (R : Russell ℓ) (P : Pi R) where

  open Russell R
  open Pi P

  -- The children at a shape x : a, b x → w, over Γ, x : a.
  children-type :
    {Γ : Ob} (m k : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a)) (w : Tm Γ) → Tm (Γ ▸ a)
  children-type m k a b w = pi k (m ⊔ℕ k) b (w [ p ] [ p ])

  -- The hypotheses (y : b x) → M (f y), over Γ, x : a, f.
  hypotheses-type :
    {Γ : Ob} (m k l : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a)) (w : Tm Γ)
    (M : Tm (Γ ▸ w))
    → Tm (Γ ▸ a ▸ children-type m k a b w)
  hypotheses-type m k l a b w M =
    pi k l (b [ p ])
      (M [ p ∘ p ∘ p
         ⨾ application k (m ⊔ℕ k) (b [ p ] [ p ]) (w [ p ] [ p ] [ p ] [ p ])
             (q (children-type m k a b w) [ p ]) (q (b [ p ])) ])

  -- Γ, x : a, f : b x → w, h : (y : b x) → M (f y).
  method-context :
    {Γ : Ob} (m k l : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a)) (w : Tm Γ)
    (M : Tm (Γ ▸ w))
    → Ob
  method-context {Γ} m k l a b w M =
    Γ ▸ a ▸ children-type m k a b w ▸ hypotheses-type m k l a b w M

------------------------------------------------------------------------
-- W-structures

record WellFounded {ℓ : Level} (R : Russell ℓ) (P : Pi R) : Set ℓ where
  open Russell R
  open Pi P
  field
    tree : {Γ : Ob} (m k : ℕ) (a : Tm Γ) → Tm (Γ ▸ a) → Tm Γ
    supremum :
      {Γ : Ob} (m k : ℕ) (a : Tm Γ) → Tm (Γ ▸ a) → Tm Γ → Tm Γ → Tm Γ
    tree-induction :
      {Γ : Ob} (m k l : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a))
      (M : Tm (Γ ▸ tree m k a b))
      → Tm (method-context R P m k l a b (tree m k a b) M)
      → Tm (Γ ▸ tree m k a b)

    tree-type :
      {Γ : Ob} (m k : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a))
      → Code R m a → Code R k b → Code R (m ⊔ℕ k) (tree m k a b)
    supremum-type :
      {Γ : Ob} (m k : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a)) (x f : Tm Γ)
      → Code R m a → Code R k b → type-of x ＝ a
      → type-of f ＝ pi k (m ⊔ℕ k) (b [ id ⨾ x ]) (tree m k a b [ p ])
      → type-of (supremum m k a b x f) ＝ tree m k a b
    tree-induction-type :
      {Γ : Ob} (m k l : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a))
      (M : Tm (Γ ▸ tree m k a b))
      (c : Tm (method-context R P m k l a b (tree m k a b) M))
      → Code R m a → Code R k b → Code R l M
      → type-of c
        ＝ M [ p ∘ p ∘ p
            ⨾ supremum m k (a [ p ] [ p ] [ p ])
                (b [ (p ∘ p ∘ p) ∘ p ⨾ q (a [ p ] [ p ] [ p ]) ])
                (q a [ p ] [ p ])
                (q (children-type R P m k a b (tree m k a b)) [ p ]) ]
      → type-of (tree-induction m k l a b M c) ＝ M

    tree-induction-supremum :
      {Γ : Ob} (m k l : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a))
      (M : Tm (Γ ▸ tree m k a b))
      (c : Tm (method-context R P m k l a b (tree m k a b) M)) (x f : Tm Γ)
      → Code R m a → Code R k b → Code R l M
      → type-of c
        ＝ M [ p ∘ p ∘ p
            ⨾ supremum m k (a [ p ] [ p ] [ p ])
                (b [ (p ∘ p ∘ p) ∘ p ⨾ q (a [ p ] [ p ] [ p ]) ])
                (q a [ p ] [ p ])
                (q (children-type R P m k a b (tree m k a b)) [ p ]) ]
      → (tx : type-of x ＝ a)
      → type-of f ＝ pi k (m ⊔ℕ k) (b [ id ⨾ x ]) (tree m k a b [ p ])
      → (e : type-of f
             ＝ children-type R P m k a b (tree m k a b) [ section R a x tx ])
      → let child =
              application k (m ⊔ℕ k) (b [ id ⨾ x ] [ p ])
                (tree m k a b [ p ] [ p ]) (f [ p ]) (q (b [ id ⨾ x ]))
        in tree-induction m k l a b M c [ id ⨾ supremum m k a b x f ]
           ＝ c [ extend (children-type R P m k a b (tree m k a b))
                   (section R a x tx) f e
               ⨾ lambda k l (b [ id ⨾ x ]) (M [ p ⨾ child ])
                   (tree-induction m k l a b M c [ p ⨾ child ]) ]

    tree-[] :
      {Γ Δ : Ob} (m k : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a)) (σ : Hom Δ Γ)
      → Code R m a → Code R k b
      → tree m k a b [ σ ] ＝ tree m k (a [ σ ]) (b [ σ ∘ p ⨾ q (a [ σ ]) ])
    supremum-[] :
      {Γ Δ : Ob} (m k : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a)) (x f : Tm Γ)
      (σ : Hom Δ Γ)
      → Code R m a → Code R k b → type-of x ＝ a
      → type-of f ＝ pi k (m ⊔ℕ k) (b [ id ⨾ x ]) (tree m k a b [ p ])
      → supremum m k a b x f [ σ ]
        ＝ supremum m k (a [ σ ]) (b [ σ ∘ p ⨾ q (a [ σ ]) ]) (x [ σ ])
            (f [ σ ])
    tree-induction-[] :
      {Γ Δ : Ob} (m k l : ℕ) (a : Tm Γ) (b : Tm (Γ ▸ a))
      (M : Tm (Γ ▸ tree m k a b))
      (c : Tm (method-context R P m k l a b (tree m k a b) M))
      (σ : Hom Δ Γ)
      → (ta : Code R m a) → Code R k b → Code R l M
      → type-of c
        ＝ M [ p ∘ p ∘ p
            ⨾ supremum m k (a [ p ] [ p ] [ p ])
                (b [ (p ∘ p ∘ p) ∘ p ⨾ q (a [ p ] [ p ] [ p ]) ])
                (q a [ p ] [ p ])
                (q (children-type R P m k a b (tree m k a b)) [ p ]) ]
      → let b′ = b [ σ ∘ p ⨾ q (a [ σ ]) ]
            w′ = tree m k (a [ σ ]) b′
            M′ = M [ σ ∘ p ⨾ q w′ ]
            F′ = children-type R P m k (a [ σ ]) b′ w′
        in (e : type-of (q F′)
                ＝ children-type R P m k a b (tree m k a b)
                    [ under R m a σ ta ∘ p ])
        → tree-induction m k l a b M c [ σ ∘ p ⨾ q w′ ]
          ＝ tree-induction m k l (a [ σ ]) b′ M′
              (c [ extend (children-type R P m k a b (tree m k a b))
                     (under R m a σ ta ∘ p) (q F′) e
                     ∘ p
                 ⨾ q (hypotheses-type R P m k l (a [ σ ]) b′ w′ M′) ])
