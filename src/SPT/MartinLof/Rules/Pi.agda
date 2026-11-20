{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Rules.Pi where

-- The rules of Π, as a signature over the judgments of the core
-- theory (`Rule`, `premises`, `rules`): for A at level m and B at level k
-- over A, Π A B is a type at level m ⊔ k (formation), with λ and
-- application (introduction, elimination), β (computation), η
-- (uniqueness: f = λ x. f x, where the application carries A weakened and
-- B weakened past its bound variable), and the congruence of each former.

open import SPT.Base
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Signature.Sum as Sig
import SPT.Foundation.Tree as Tree
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Formers using
  (pi; lambda; application; weaken; weaken-past; instantiate)
open import SPT.MartinLof.Judgment using
  (Context; _▸[_]_; Judgment; term; term-equal; type; type-equal
  ; rule-signature)

data Rule (C : Set) : Judgment C → Set where
  formation :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n))
    → Rule C (type Γ (m ⊔ℕ k) (pi m k A B))
  introduction :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A : Raw.Expression C n)
    (B t : Raw.Expression C (suc n))
    → Rule C (term Γ (m ⊔ℕ k) (lambda m k A B t) (pi m k A B))
  elimination :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (f a : Raw.Expression C n)
    → Rule C (term Γ k (application m k A B f a) (instantiate B a))
  computation :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A : Raw.Expression C n)
    (B t : Raw.Expression C (suc n)) (a : Raw.Expression C n)
    → Rule C
        (term-equal Γ k (application m k A B (lambda m k A B t) a)
          (instantiate t a) (instantiate B a))
  uniqueness :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (f : Raw.Expression C n)
    → Rule C
        (term-equal Γ (m ⊔ℕ k)
          (lambda m k A B
            (application m k (weaken A) (weaken-past n 1 1 B) (weaken f)
              (Tree.hole fzero)))
          f (pi m k A B))
  formation-equal :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A A′ : Raw.Expression C n)
    (B B′ : Raw.Expression C (suc n))
    → Rule C (type-equal Γ (m ⊔ℕ k) (pi m k A B) (pi m k A′ B′))
  introduction-equal :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A A′ : Raw.Expression C n)
    (B B′ t t′ : Raw.Expression C (suc n))
    → Rule C
        (term-equal Γ (m ⊔ℕ k) (lambda m k A B t) (lambda m k A′ B′ t′)
          (pi m k A B))
  elimination-equal :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A A′ : Raw.Expression C n)
    (B B′ : Raw.Expression C (suc n)) (f f′ a a′ : Raw.Expression C n)
    → Rule C
        (term-equal Γ k (application m k A B f a)
          (application m k A′ B′ f′ a′) (instantiate B a))

premises : {C : Set} {j : Judgment C} → Rule C j → List (Judgment C)
premises (formation Γ m k A B) = type Γ m A ∷ type (Γ ▸[ m ] A) k B ∷ []
premises (introduction Γ m k A B t) =
  type Γ m A ∷ type (Γ ▸[ m ] A) k B ∷ term (Γ ▸[ m ] A) k t B ∷ []
premises (elimination Γ m k A B f a) =
  type Γ m A ∷ type (Γ ▸[ m ] A) k B ∷ term Γ (m ⊔ℕ k) f (pi m k A B)
  ∷ term Γ m a A ∷ []
premises (computation Γ m k A B t a) =
  type Γ m A ∷ type (Γ ▸[ m ] A) k B ∷ term (Γ ▸[ m ] A) k t B
  ∷ term Γ m a A ∷ []
premises (uniqueness Γ m k A B f) =
  type Γ m A ∷ type (Γ ▸[ m ] A) k B ∷ term Γ (m ⊔ℕ k) f (pi m k A B) ∷ []
premises (formation-equal Γ m k A A′ B B′) =
  type-equal Γ m A A′ ∷ type-equal (Γ ▸[ m ] A) k B B′ ∷ []
premises (introduction-equal Γ m k A A′ B B′ t t′) =
  type-equal Γ m A A′ ∷ type-equal (Γ ▸[ m ] A) k B B′
  ∷ term-equal (Γ ▸[ m ] A) k t t′ B ∷ []
premises (elimination-equal Γ m k A A′ B B′ f f′ a a′) =
  type-equal Γ m A A′ ∷ type-equal (Γ ▸[ m ] A) k B B′
  ∷ term-equal Γ (m ⊔ℕ k) f f′ (pi m k A B) ∷ term-equal Γ m a a′ A ∷ []

rules : (C : Set) → Sig.Signature-Over (Judgment C) lzero lzero
rules C = rule-signature (Rule C) premises
