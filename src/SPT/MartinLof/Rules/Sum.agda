{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Rules.Sum where

-- The rules of binary sums, as a signature over the judgments of the
-- core theory (`Rule`, `premises`, `rules`): for A at level m and B at
-- level k, A + B is a type at level m ⊔ k (formation), with inl and inr
-- (introductions), case analysis into a motive M at level l over A + B
-- whose methods have types M (inl x) and M (inr y) (`on-left`,
-- `on-right`; elimination), its two β rules (computations), and the
-- congruence of each former.

open import SPT.Base
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Signature.Sum as Sig
import SPT.Foundation.Tree as Tree
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Formers using
  (sum; left; right; case; weaken; instantiate; instantiate-past)
open import SPT.MartinLof.Judgment using
  (Context; _▸[_]_; Judgment; term; term-equal; type; type-equal
  ; rule-signature)

-- M at inl x, in the context Γ, x : A.
on-left :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n → Raw.Expression C n
  → Raw.Expression C (suc n) → Raw.Expression C (suc n)
on-left m k A B M =
  instantiate-past 1 M (left m k (weaken A) (weaken B) (Tree.hole fzero))

-- M at inr y, in the context Γ, y : B.
on-right :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n → Raw.Expression C n
  → Raw.Expression C (suc n) → Raw.Expression C (suc n)
on-right m k A B M =
  instantiate-past 1 M (right m k (weaken A) (weaken B) (Tree.hole fzero))

data Rule (C : Set) : Judgment C → Set where
  formation :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A B : Raw.Expression C n)
    → Rule C (type Γ (m ⊔ℕ k) (sum m k A B))
  left-introduction :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A B a : Raw.Expression C n)
    → Rule C (term Γ (m ⊔ℕ k) (left m k A B a) (sum m k A B))
  right-introduction :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A B b : Raw.Expression C n)
    → Rule C (term Γ (m ⊔ℕ k) (right m k A B b) (sum m k A B))
  elimination :
    {n : ℕ} (Γ : Context C n) (m k l : ℕ) (A B : Raw.Expression C n)
    (M c d : Raw.Expression C (suc n)) (s : Raw.Expression C n)
    → Rule C (term Γ l (case m k l A B M c d s) (instantiate M s))
  left-computation :
    {n : ℕ} (Γ : Context C n) (m k l : ℕ) (A B : Raw.Expression C n)
    (M c d : Raw.Expression C (suc n)) (a : Raw.Expression C n)
    → Rule C
        (term-equal Γ l (case m k l A B M c d (left m k A B a))
          (instantiate c a) (instantiate M (left m k A B a)))
  right-computation :
    {n : ℕ} (Γ : Context C n) (m k l : ℕ) (A B : Raw.Expression C n)
    (M c d : Raw.Expression C (suc n)) (b : Raw.Expression C n)
    → Rule C
        (term-equal Γ l (case m k l A B M c d (right m k A B b))
          (instantiate d b) (instantiate M (right m k A B b)))
  formation-equal :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A A′ B B′ : Raw.Expression C n)
    → Rule C (type-equal Γ (m ⊔ℕ k) (sum m k A B) (sum m k A′ B′))
  left-introduction-equal :
    {n : ℕ} (Γ : Context C n) (m k : ℕ)
    (A A′ B B′ a a′ : Raw.Expression C n)
    → Rule C
        (term-equal Γ (m ⊔ℕ k) (left m k A B a) (left m k A′ B′ a′)
          (sum m k A B))
  right-introduction-equal :
    {n : ℕ} (Γ : Context C n) (m k : ℕ)
    (A A′ B B′ b b′ : Raw.Expression C n)
    → Rule C
        (term-equal Γ (m ⊔ℕ k) (right m k A B b) (right m k A′ B′ b′)
          (sum m k A B))
  elimination-equal :
    {n : ℕ} (Γ : Context C n) (m k l : ℕ) (A A′ B B′ : Raw.Expression C n)
    (M M′ c c′ d d′ : Raw.Expression C (suc n))
    (s s′ : Raw.Expression C n)
    → Rule C
        (term-equal Γ l (case m k l A B M c d s)
          (case m k l A′ B′ M′ c′ d′ s′) (instantiate M s))

premises : {C : Set} {j : Judgment C} → Rule C j → List (Judgment C)
premises (formation Γ m k A B) = type Γ m A ∷ type Γ k B ∷ []
premises (left-introduction Γ m k A B a) =
  type Γ m A ∷ type Γ k B ∷ term Γ m a A ∷ []
premises (right-introduction Γ m k A B b) =
  type Γ m A ∷ type Γ k B ∷ term Γ k b B ∷ []
premises (elimination Γ m k l A B M c d s) =
  type Γ m A ∷ type Γ k B ∷ type (Γ ▸[ m ⊔ℕ k ] sum m k A B) l M
  ∷ term (Γ ▸[ m ] A) l c (on-left m k A B M)
  ∷ term (Γ ▸[ k ] B) l d (on-right m k A B M)
  ∷ term Γ (m ⊔ℕ k) s (sum m k A B) ∷ []
premises (left-computation Γ m k l A B M c d a) =
  type Γ m A ∷ type Γ k B ∷ type (Γ ▸[ m ⊔ℕ k ] sum m k A B) l M
  ∷ term (Γ ▸[ m ] A) l c (on-left m k A B M)
  ∷ term (Γ ▸[ k ] B) l d (on-right m k A B M)
  ∷ term Γ m a A ∷ []
premises (right-computation Γ m k l A B M c d b) =
  type Γ m A ∷ type Γ k B ∷ type (Γ ▸[ m ⊔ℕ k ] sum m k A B) l M
  ∷ term (Γ ▸[ m ] A) l c (on-left m k A B M)
  ∷ term (Γ ▸[ k ] B) l d (on-right m k A B M)
  ∷ term Γ k b B ∷ []
premises (formation-equal Γ m k A A′ B B′) =
  type-equal Γ m A A′ ∷ type-equal Γ k B B′ ∷ []
premises (left-introduction-equal Γ m k A A′ B B′ a a′) =
  type-equal Γ m A A′ ∷ type-equal Γ k B B′ ∷ term-equal Γ m a a′ A ∷ []
premises (right-introduction-equal Γ m k A A′ B B′ b b′) =
  type-equal Γ m A A′ ∷ type-equal Γ k B B′ ∷ term-equal Γ k b b′ B ∷ []
premises (elimination-equal Γ m k l A A′ B B′ M M′ c c′ d d′ s s′) =
  type-equal Γ m A A′ ∷ type-equal Γ k B B′
  ∷ type-equal (Γ ▸[ m ⊔ℕ k ] sum m k A B) l M M′
  ∷ term-equal (Γ ▸[ m ] A) l c c′ (on-left m k A B M)
  ∷ term-equal (Γ ▸[ k ] B) l d d′ (on-right m k A B M)
  ∷ term-equal Γ (m ⊔ℕ k) s s′ (sum m k A B) ∷ []

rules : (C : Set) → Sig.Signature-Over (Judgment C) lzero lzero
rules C = rule-signature (Rule C) premises
