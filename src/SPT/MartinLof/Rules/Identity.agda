{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Rules.Identity where

-- The rules of identity types, as a signature over the judgments of
-- the core theory (`Rule`, `premises`, `rules`): for A at level m, Id_A a b
-- is a type at level m (formation), with refl (introduction), based path
-- induction J into a motive at level k over the points x of A and the
-- paths from a to x (`paths`; elimination), its β rule (computation), and
-- the congruence of each former. There is no uniqueness rule: identity
-- proofs are not identified.

open import SPT.Base
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Signature.Sum as Sig
import SPT.Foundation.Tree as Tree
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Formers using
  (identity; reflexivity; path-induction; weaken; instantiate₂)
open import SPT.MartinLof.Judgment using
  (Context; _▸[_]_; Judgment; term; term-equal; type; type-equal
  ; rule-signature)

-- Γ extended by a point x of A and a path from a to x.
paths :
  {C : Set} {n : ℕ} → Context C n → ℕ → Raw.Expression C n
  → Raw.Expression C n → Context C (suc (suc n))
paths Γ m A a =
  Γ ▸[ m ] A ▸[ m ] identity m (weaken A) (weaken a) (Tree.hole fzero)

data Rule (C : Set) : Judgment C → Set where
  formation :
    {n : ℕ} (Γ : Context C n) (m : ℕ) (A a b : Raw.Expression C n)
    → Rule C (type Γ m (identity m A a b))
  introduction :
    {n : ℕ} (Γ : Context C n) (m : ℕ) (A a : Raw.Expression C n)
    → Rule C (term Γ m (reflexivity m A a) (identity m A a a))
  elimination :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A : Raw.Expression C n)
    (M : Raw.Expression C (suc (suc n)))
    (a d b p : Raw.Expression C n)
    → Rule C
        (term Γ k (path-induction m k A M a d b p) (instantiate₂ M b p))
  computation :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A : Raw.Expression C n)
    (M : Raw.Expression C (suc (suc n))) (a d : Raw.Expression C n)
    → Rule C
        (term-equal Γ k (path-induction m k A M a d a (reflexivity m A a)) d
          (instantiate₂ M a (reflexivity m A a)))
  formation-equal :
    {n : ℕ} (Γ : Context C n) (m : ℕ) (A A′ a a′ b b′ : Raw.Expression C n)
    → Rule C (type-equal Γ m (identity m A a b) (identity m A′ a′ b′))
  introduction-equal :
    {n : ℕ} (Γ : Context C n) (m : ℕ) (A A′ a a′ : Raw.Expression C n)
    → Rule C
        (term-equal Γ m (reflexivity m A a) (reflexivity m A′ a′)
          (identity m A a a))
  elimination-equal :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A A′ : Raw.Expression C n)
    (M M′ : Raw.Expression C (suc (suc n)))
    (a a′ d d′ b b′ p p′ : Raw.Expression C n)
    → Rule C
        (term-equal Γ k (path-induction m k A M a d b p)
          (path-induction m k A′ M′ a′ d′ b′ p′) (instantiate₂ M b p))

premises : {C : Set} {j : Judgment C} → Rule C j → List (Judgment C)
premises (formation Γ m A a b) =
  type Γ m A ∷ term Γ m a A ∷ term Γ m b A ∷ []
premises (introduction Γ m A a) = type Γ m A ∷ term Γ m a A ∷ []
premises (elimination Γ m k A M a d b p) =
  type Γ m A ∷ term Γ m a A ∷ type (paths Γ m A a) k M
  ∷ term Γ k d (instantiate₂ M a (reflexivity m A a)) ∷ term Γ m b A
  ∷ term Γ m p (identity m A a b) ∷ []
premises (computation Γ m k A M a d) =
  type Γ m A ∷ term Γ m a A ∷ type (paths Γ m A a) k M
  ∷ term Γ k d (instantiate₂ M a (reflexivity m A a)) ∷ []
premises (formation-equal Γ m A A′ a a′ b b′) =
  type-equal Γ m A A′ ∷ term-equal Γ m a a′ A ∷ term-equal Γ m b b′ A ∷ []
premises (introduction-equal Γ m A A′ a a′) =
  type-equal Γ m A A′ ∷ term-equal Γ m a a′ A ∷ []
premises (elimination-equal Γ m k A A′ M M′ a a′ d d′ b b′ p p′) =
  type-equal Γ m A A′ ∷ term-equal Γ m a a′ A
  ∷ type-equal (paths Γ m A a) k M M′
  ∷ term-equal Γ k d d′ (instantiate₂ M a (reflexivity m A a))
  ∷ term-equal Γ m b b′ A ∷ term-equal Γ m p p′ (identity m A a b) ∷ []

rules : (C : Set) → Sig.Signature-Over (Judgment C) lzero lzero
rules C = rule-signature (Rule C) premises
