{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Rules.Empty where

-- The rules of the empty type, as a signature over the judgments of
-- the core theory (`Rule`, `premises`, `rules`): 0 is a type at level 0
-- (formation), eliminated into any motive at level k over it
-- (elimination), with the congruence of the eliminator.

open import SPT.Base
import SPT.Foundation.Signature.Sum as Sig
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Formers using (empty; absurd; instantiate)
open import SPT.MartinLof.Judgment using
  (Context; _▸[_]_; Judgment; context; term; term-equal; type; type-equal
  ; rule-signature)

data Rule (C : Set) : Judgment C → Set where
  formation : {n : ℕ} (Γ : Context C n) → Rule C (type Γ 0 empty)
  elimination :
    {n : ℕ} (Γ : Context C n) (k : ℕ) (M : Raw.Expression C (suc n))
    (t : Raw.Expression C n)
    → Rule C (term Γ k (absurd k M t) (instantiate M t))
  elimination-equal :
    {n : ℕ} (Γ : Context C n) (k : ℕ)
    (M M′ : Raw.Expression C (suc n)) (t t′ : Raw.Expression C n)
    → Rule C
        (term-equal Γ k (absurd k M t) (absurd k M′ t′) (instantiate M t))

premises : {C : Set} {j : Judgment C} → Rule C j → List (Judgment C)
premises (formation Γ) = context Γ ∷ []
premises (elimination Γ k M t) =
  type (Γ ▸[ 0 ] empty) k M ∷ term Γ 0 t empty ∷ []
premises (elimination-equal Γ k M M′ t t′) =
  type-equal (Γ ▸[ 0 ] empty) k M M′ ∷ term-equal Γ 0 t t′ empty ∷ []

rules : (C : Set) → Sig.Signature-Over (Judgment C) lzero lzero
rules C = rule-signature (Rule C) premises
