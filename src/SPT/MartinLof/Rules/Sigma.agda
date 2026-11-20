{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Rules.Sigma where

-- The rules of Σ, as a signature over the judgments of the core
-- theory (`Rule`, `premises`, `rules`): for A at level m and B at level k
-- over A, Σ A B is a type at level m ⊔ k (formation), with pairs
-- (introduction), both projections, their β rules (computation), η
-- (uniqueness: p = (fst p , snd p)), and the congruence of each former.

open import SPT.Base
import SPT.Foundation.Signature.Sum as Sig
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Formers using
  (sigma; pair; first; second; instantiate)
open import SPT.MartinLof.Judgment using
  (Context; _▸[_]_; Judgment; term; term-equal; type; type-equal
  ; rule-signature)

data Rule (C : Set) : Judgment C → Set where
  formation :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n))
    → Rule C (type Γ (m ⊔ℕ k) (sigma m k A B))
  introduction :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (a b : Raw.Expression C n)
    → Rule C (term Γ (m ⊔ℕ k) (pair m k A B a b) (sigma m k A B))
  first-projection :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (p : Raw.Expression C n)
    → Rule C (term Γ m (first m k A B p) A)
  second-projection :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (p : Raw.Expression C n)
    → Rule C
        (term Γ k (second m k A B p) (instantiate B (first m k A B p)))
  first-computation :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (a b : Raw.Expression C n)
    → Rule C (term-equal Γ m (first m k A B (pair m k A B a b)) a A)
  second-computation :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (a b : Raw.Expression C n)
    → Rule C
        (term-equal Γ k (second m k A B (pair m k A B a b)) b
          (instantiate B a))
  uniqueness :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (p : Raw.Expression C n)
    → Rule C
        (term-equal Γ (m ⊔ℕ k)
          (pair m k A B (first m k A B p) (second m k A B p)) p
          (sigma m k A B))
  formation-equal :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A A′ : Raw.Expression C n)
    (B B′ : Raw.Expression C (suc n))
    → Rule C (type-equal Γ (m ⊔ℕ k) (sigma m k A B) (sigma m k A′ B′))
  introduction-equal :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A A′ : Raw.Expression C n)
    (B B′ : Raw.Expression C (suc n)) (a a′ b b′ : Raw.Expression C n)
    → Rule C
        (term-equal Γ (m ⊔ℕ k) (pair m k A B a b) (pair m k A′ B′ a′ b′)
          (sigma m k A B))
  first-projection-equal :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A A′ : Raw.Expression C n)
    (B B′ : Raw.Expression C (suc n)) (p p′ : Raw.Expression C n)
    → Rule C (term-equal Γ m (first m k A B p) (first m k A′ B′ p′) A)
  second-projection-equal :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A A′ : Raw.Expression C n)
    (B B′ : Raw.Expression C (suc n)) (p p′ : Raw.Expression C n)
    → Rule C
        (term-equal Γ k (second m k A B p) (second m k A′ B′ p′)
          (instantiate B (first m k A B p)))

premises : {C : Set} {j : Judgment C} → Rule C j → List (Judgment C)
premises (formation Γ m k A B) = type Γ m A ∷ type (Γ ▸[ m ] A) k B ∷ []
premises (introduction Γ m k A B a b) =
  type Γ m A ∷ type (Γ ▸[ m ] A) k B ∷ term Γ m a A
  ∷ term Γ k b (instantiate B a) ∷ []
premises (first-projection Γ m k A B p) =
  type Γ m A ∷ type (Γ ▸[ m ] A) k B ∷ term Γ (m ⊔ℕ k) p (sigma m k A B)
  ∷ []
premises (second-projection Γ m k A B p) =
  type Γ m A ∷ type (Γ ▸[ m ] A) k B ∷ term Γ (m ⊔ℕ k) p (sigma m k A B)
  ∷ []
premises (first-computation Γ m k A B a b) =
  type Γ m A ∷ type (Γ ▸[ m ] A) k B ∷ term Γ m a A
  ∷ term Γ k b (instantiate B a) ∷ []
premises (second-computation Γ m k A B a b) =
  type Γ m A ∷ type (Γ ▸[ m ] A) k B ∷ term Γ m a A
  ∷ term Γ k b (instantiate B a) ∷ []
premises (uniqueness Γ m k A B p) =
  type Γ m A ∷ type (Γ ▸[ m ] A) k B ∷ term Γ (m ⊔ℕ k) p (sigma m k A B)
  ∷ []
premises (formation-equal Γ m k A A′ B B′) =
  type-equal Γ m A A′ ∷ type-equal (Γ ▸[ m ] A) k B B′ ∷ []
premises (introduction-equal Γ m k A A′ B B′ a a′ b b′) =
  type-equal Γ m A A′ ∷ type-equal (Γ ▸[ m ] A) k B B′
  ∷ term-equal Γ m a a′ A ∷ term-equal Γ k b b′ (instantiate B a) ∷ []
premises (first-projection-equal Γ m k A A′ B B′ p p′) =
  type-equal Γ m A A′ ∷ type-equal (Γ ▸[ m ] A) k B B′
  ∷ term-equal Γ (m ⊔ℕ k) p p′ (sigma m k A B) ∷ []
premises (second-projection-equal Γ m k A A′ B B′ p p′) =
  type-equal Γ m A A′ ∷ type-equal (Γ ▸[ m ] A) k B B′
  ∷ term-equal Γ (m ⊔ℕ k) p p′ (sigma m k A B) ∷ []

rules : (C : Set) → Sig.Signature-Over (Judgment C) lzero lzero
rules C = rule-signature (Rule C) premises
