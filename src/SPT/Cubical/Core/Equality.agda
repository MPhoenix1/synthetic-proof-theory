{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.Equality where

-- Propositions, sets and loop spaces in terms of the identity type, and
-- function extensionality for one dependent function space, or one function
-- space, as a named hypothesis.  Nothing here assumes K, UIP or function
-- extensionality.

open import Agda.Primitive using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- IsProposition(A) = Π(x y : A). x = y.

IsProposition :
    ∀ {ℓ : Level}
  → Set ℓ
  → Set ℓ
IsProposition A =
  (left right : A) → left ≡ right


-- IsSet(A) = Π(x y : A). IsProposition(x = y).

IsSet :
    ∀ {ℓ : Level}
  → Set ℓ
  → Set ℓ
IsSet A =
  (left right : A) → IsProposition (left ≡ right)


-- Function extensionality for the one dependent function space Π x. B(x):
--
--   DependentΠExt(A,B) = Π(f g : Π x. B(x)). (Π x. f(x) = g(x)) → f = g.
--
-- It is a hypothesis; the modules taking it say which conclusions need it.

DependentΠExt :
    ∀ {ℓa ℓb : Level}
  → (A : Set ℓa)
  → (B : A → Set ℓb)
  → Set (ℓa ⊔ ℓb)
DependentΠExt A B =
  (left right : (point : A) → B point)
  → ((point : A) → left point ≡ right point)
  → left ≡ right

-- The non-dependent case, for one function space A → B:
--
--   MapΠExt(A,B) = DependentΠExt(A, λ _. B).

MapΠExt :
    ∀ {ℓa ℓb : Level}
  → Set ℓa
  → Set ℓb
  → Set (ℓa ⊔ ℓb)
MapΠExt A B =
  DependentΠExt A (λ _ → B)

module WithDependentΠExt
    {ℓa ℓb : Level}
    {A : Set ℓa}
    {B : A → Set ℓb}
    (πext : DependentΠExt A B)
  where

  dependentFunction-isProposition :
      ((point : A) → IsProposition (B point))
    → IsProposition ((point : A) → B point)
  dependentFunction-isProposition fiber-proposition left right =
    πext left right
      (λ point → fiber-proposition point (left point) (right point))


-- The loop space of A at a point.

Loop :
    ∀ {ℓ : Level}
  → (A : Set ℓ)
  → A
  → Set ℓ
Loop A point =
  point ≡ point
