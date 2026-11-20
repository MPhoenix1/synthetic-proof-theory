{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Rules.Lift where

-- The rules of Lift, as a signature over the judgments of the core
-- theory (`Rule`, `premises`, `rules`): for a type A at level m, Lift A is
-- a type at level m ⊔ k (formation), with lift and lower (introduction,
-- elimination), lower (lift a) = a (computation), lift (lower x) = x
-- (uniqueness), and the congruence of each former.

open import SPT.Base hiding (lift; lower)
import SPT.Foundation.Signature.Sum as Sig
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Formers using (lifted; lift; lower)
open import SPT.MartinLof.Judgment using
  (Context; Judgment; term; term-equal; type; type-equal; rule-signature)

data Rule (C : Set) : Judgment C → Set where
  formation :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A : Raw.Expression C n)
    → Rule C (type Γ (m ⊔ℕ k) (lifted m k A))
  introduction :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A a : Raw.Expression C n)
    → Rule C (term Γ (m ⊔ℕ k) (lift m k A a) (lifted m k A))
  elimination :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A x : Raw.Expression C n)
    → Rule C (term Γ m (lower m k A x) A)
  computation :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A a : Raw.Expression C n)
    → Rule C (term-equal Γ m (lower m k A (lift m k A a)) a A)
  uniqueness :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A x : Raw.Expression C n)
    → Rule C
        (term-equal Γ (m ⊔ℕ k) (lift m k A (lower m k A x)) x
          (lifted m k A))
  formation-equal :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A A′ : Raw.Expression C n)
    → Rule C (type-equal Γ (m ⊔ℕ k) (lifted m k A) (lifted m k A′))
  introduction-equal :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A A′ a a′ : Raw.Expression C n)
    → Rule C
        (term-equal Γ (m ⊔ℕ k) (lift m k A a) (lift m k A′ a′)
          (lifted m k A))
  elimination-equal :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A A′ x x′ : Raw.Expression C n)
    → Rule C (term-equal Γ m (lower m k A x) (lower m k A′ x′) A)

premises : {C : Set} {j : Judgment C} → Rule C j → List (Judgment C)
premises (formation Γ m k A) = type Γ m A ∷ []
premises (introduction Γ m k A a) = type Γ m A ∷ term Γ m a A ∷ []
premises (elimination Γ m k A x) =
  type Γ m A ∷ term Γ (m ⊔ℕ k) x (lifted m k A) ∷ []
premises (computation Γ m k A a) = type Γ m A ∷ term Γ m a A ∷ []
premises (uniqueness Γ m k A x) =
  type Γ m A ∷ term Γ (m ⊔ℕ k) x (lifted m k A) ∷ []
premises (formation-equal Γ m k A A′) = type-equal Γ m A A′ ∷ []
premises (introduction-equal Γ m k A A′ a a′) =
  type-equal Γ m A A′ ∷ term-equal Γ m a a′ A ∷ []
premises (elimination-equal Γ m k A A′ x x′) =
  type-equal Γ m A A′ ∷ term-equal Γ (m ⊔ℕ k) x x′ (lifted m k A) ∷ []

rules : (C : Set) → Sig.Signature-Over (Judgment C) lzero lzero
rules C = rule-signature (Rule C) premises
