{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Rules.Natural where

-- The rules of the natural numbers, as a signature over the judgments
-- of the core theory (`Rule`, `premises`, `rules`): ℕ is a type at level 0
-- (formation), with zero and successor (introductions), induction into a
-- motive M at level l over ℕ whose step lives over a number x and a value
-- of M at x (`steps`) with type M (suc x) (`next`; elimination), its two β
-- rules (computations), and the congruence of the successor and of the
-- eliminator.

open import SPT.Base hiding (zero)
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Signature.Sum as Sig
import SPT.Foundation.Tree as Tree
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Formers using
  (natural; zero; successor; natural-induction; instantiate; instantiate-past
  ; instantiate₂)
open import SPT.MartinLof.Judgment using
  (Context; _▸[_]_; Judgment; context; term; term-equal; type; type-equal
  ; rule-signature)

-- Γ extended by a number x and a value of M at x.
steps :
  {C : Set} {n : ℕ} → Context C n → ℕ → Raw.Expression C (suc n)
  → Context C (suc (suc n))
steps Γ l M = Γ ▸[ 0 ] natural ▸[ l ] M

-- M at the successor of x, in the context steps Γ l M.
next :
  {C : Set} {n : ℕ} → Raw.Expression C (suc n)
  → Raw.Expression C (suc (suc n))
next M = instantiate-past 2 M (successor (Tree.hole (fsuc fzero)))

data Rule (C : Set) : Judgment C → Set where
  formation : {n : ℕ} (Γ : Context C n) → Rule C (type Γ 0 natural)
  zero-introduction :
    {n : ℕ} (Γ : Context C n) → Rule C (term Γ 0 zero natural)
  successor-introduction :
    {n : ℕ} (Γ : Context C n) (t : Raw.Expression C n)
    → Rule C (term Γ 0 (successor t) natural)
  elimination :
    {n : ℕ} (Γ : Context C n) (l : ℕ) (M : Raw.Expression C (suc n))
    (z : Raw.Expression C n) (s : Raw.Expression C (suc (suc n)))
    (t : Raw.Expression C n)
    → Rule C (term Γ l (natural-induction l M z s t) (instantiate M t))
  zero-computation :
    {n : ℕ} (Γ : Context C n) (l : ℕ) (M : Raw.Expression C (suc n))
    (z : Raw.Expression C n) (s : Raw.Expression C (suc (suc n)))
    → Rule C
        (term-equal Γ l (natural-induction l M z s zero) z
          (instantiate M zero))
  successor-computation :
    {n : ℕ} (Γ : Context C n) (l : ℕ) (M : Raw.Expression C (suc n))
    (z : Raw.Expression C n) (s : Raw.Expression C (suc (suc n)))
    (t : Raw.Expression C n)
    → Rule C
        (term-equal Γ l (natural-induction l M z s (successor t))
          (instantiate₂ s t (natural-induction l M z s t))
          (instantiate M (successor t)))
  successor-introduction-equal :
    {n : ℕ} (Γ : Context C n) (t t′ : Raw.Expression C n)
    → Rule C (term-equal Γ 0 (successor t) (successor t′) natural)
  elimination-equal :
    {n : ℕ} (Γ : Context C n) (l : ℕ)
    (M M′ : Raw.Expression C (suc n)) (z z′ : Raw.Expression C n)
    (s s′ : Raw.Expression C (suc (suc n)))
    (t t′ : Raw.Expression C n)
    → Rule C
        (term-equal Γ l (natural-induction l M z s t)
          (natural-induction l M′ z′ s′ t′) (instantiate M t))

premises : {C : Set} {j : Judgment C} → Rule C j → List (Judgment C)
premises (formation Γ) = context Γ ∷ []
premises (zero-introduction Γ) = context Γ ∷ []
premises (successor-introduction Γ t) = term Γ 0 t natural ∷ []
premises (elimination Γ l M z s t) =
  type (Γ ▸[ 0 ] natural) l M ∷ term Γ l z (instantiate M zero)
  ∷ term (steps Γ l M) l s (next M) ∷ term Γ 0 t natural ∷ []
premises (zero-computation Γ l M z s) =
  type (Γ ▸[ 0 ] natural) l M ∷ term Γ l z (instantiate M zero)
  ∷ term (steps Γ l M) l s (next M) ∷ []
premises (successor-computation Γ l M z s t) =
  type (Γ ▸[ 0 ] natural) l M ∷ term Γ l z (instantiate M zero)
  ∷ term (steps Γ l M) l s (next M) ∷ term Γ 0 t natural ∷ []
premises (successor-introduction-equal Γ t t′) =
  term-equal Γ 0 t t′ natural ∷ []
premises (elimination-equal Γ l M M′ z z′ s s′ t t′) =
  type-equal (Γ ▸[ 0 ] natural) l M M′
  ∷ term-equal Γ l z z′ (instantiate M zero)
  ∷ term-equal (steps Γ l M) l s s′ (next M)
  ∷ term-equal Γ 0 t t′ natural ∷ []

rules : (C : Set) → Sig.Signature-Over (Judgment C) lzero lzero
rules C = rule-signature (Rule C) premises
