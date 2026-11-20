{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Rules.Subuniverse where

-- The rules of Kubánek's Mahlo subuniverses (Canonicity of the Mahlo
-- Universe, MSc thesis, Chalmers 2025, §3.3), as a signature over the
-- judgments of the core theory (`Rule`, `premises`, `rules`). Every rule
-- has the four parameters among its premises, typed by Subuniverse's
-- `family`, `operator` and `operator-decoding` (`parameters`), or equal
-- there for the congruences (`parameters-equal`). For them:
-- - Ma is a type at level i (formation); El0' u is in it for u : U0, and
--   El+' A B c for A in it, B : El A → Ma and c of the point type
--   (introductions); El a is a type at level i for a in it (decoding);
--   maElim M b s a is in M a, for a motive M : Ma → U j with the two
--   methods (elimination);
-- - El (El0' u) = E0 u and El (El+' A B c) = E+ (El A) (λ x. El (B x)) c
--   (decoding at both kinds of code), and maElim at El0' u and at
--   El+' A B c (computation);
-- - the congruence of each former.

open import SPT.Base
import SPT.Foundation.Signature.Sum as Sig
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Formers using
  (universe; application; subuniverse; inclusion; closure; decoding
  ; subuniverse-induction)
open import SPT.MartinLof.Judgment using
  (Context; Judgment; term; term-equal; type; type-equal; rule-signature)
open import SPT.MartinLof.Subuniverse using
  (family-level; operator-level; plus-decoding-level; motive-level
  ; inclusion-method-level; closure-method-level; family; operator
  ; operator-decoding; family-of; point-type; decoding-closure; motive-type
  ; motive-at; inclusion-method; closure-method; induction-inclusion
  ; induction-closure)

data Rule (C : Set) : Judgment C → Set where
  formation :
    {n : ℕ} (Γ : Context C n) (i : ℕ) (U0 E0 U+ E+ : Raw.Expression C n)
    → Rule C (type Γ i (subuniverse i U0 E0 U+ E+))
  inclusion-introduction :
    {n : ℕ} (Γ : Context C n) (i : ℕ) (U0 E0 U+ E+ u : Raw.Expression C n)
    → Rule C
        (term Γ i (inclusion i U0 E0 U+ E+ u) (subuniverse i U0 E0 U+ E+))
  closure-introduction :
    {n : ℕ} (Γ : Context C n) (i : ℕ)
    (U0 E0 U+ E+ A B c : Raw.Expression C n)
    → Rule C
        (term Γ i (closure i U0 E0 U+ E+ A B c) (subuniverse i U0 E0 U+ E+))
  decoding-formation :
    {n : ℕ} (Γ : Context C n) (i : ℕ) (U0 E0 U+ E+ a : Raw.Expression C n)
    → Rule C (type Γ i (decoding i U0 E0 U+ E+ a))
  elimination :
    {n : ℕ} (Γ : Context C n) (i j : ℕ)
    (U0 E0 U+ E+ M b s a : Raw.Expression C n)
    → Rule C
        (term Γ j (subuniverse-induction i j U0 E0 U+ E+ M b s a)
          (motive-at i j U0 E0 U+ E+ M a))
  inclusion-decoding :
    {n : ℕ} (Γ : Context C n) (i : ℕ) (U0 E0 U+ E+ u : Raw.Expression C n)
    → Rule C
        (type-equal Γ i (decoding i U0 E0 U+ E+ (inclusion i U0 E0 U+ E+ u))
          (application i (suc i) U0 (universe i) E0 u))
  closure-decoding :
    {n : ℕ} (Γ : Context C n) (i : ℕ)
    (U0 E0 U+ E+ A B c : Raw.Expression C n)
    → Rule C
        (type-equal Γ i
          (decoding i U0 E0 U+ E+ (closure i U0 E0 U+ E+ A B c))
          (decoding-closure i U0 E0 U+ E+ A B c))
  inclusion-computation :
    {n : ℕ} (Γ : Context C n) (i j : ℕ)
    (U0 E0 U+ E+ M b s u : Raw.Expression C n)
    → Rule C
        (term-equal Γ j
          (subuniverse-induction i j U0 E0 U+ E+ M b s
            (inclusion i U0 E0 U+ E+ u))
          (induction-inclusion i j U0 E0 U+ E+ M b u)
          (motive-at i j U0 E0 U+ E+ M (inclusion i U0 E0 U+ E+ u)))
  closure-computation :
    {n : ℕ} (Γ : Context C n) (i j : ℕ)
    (U0 E0 U+ E+ M b s A B c : Raw.Expression C n)
    → Rule C
        (term-equal Γ j
          (subuniverse-induction i j U0 E0 U+ E+ M b s
            (closure i U0 E0 U+ E+ A B c))
          (induction-closure i j U0 E0 U+ E+ M b s A B c)
          (motive-at i j U0 E0 U+ E+ M (closure i U0 E0 U+ E+ A B c)))
  formation-equal :
    {n : ℕ} (Γ : Context C n) (i : ℕ)
    (U0 U0′ E0 E0′ U+ U+′ E+ E+′ : Raw.Expression C n)
    → Rule C
        (type-equal Γ i (subuniverse i U0 E0 U+ E+)
          (subuniverse i U0′ E0′ U+′ E+′))
  inclusion-equal :
    {n : ℕ} (Γ : Context C n) (i : ℕ)
    (U0 U0′ E0 E0′ U+ U+′ E+ E+′ u u′ : Raw.Expression C n)
    → Rule C
        (term-equal Γ i (inclusion i U0 E0 U+ E+ u)
          (inclusion i U0′ E0′ U+′ E+′ u′) (subuniverse i U0 E0 U+ E+))
  closure-equal :
    {n : ℕ} (Γ : Context C n) (i : ℕ)
    (U0 U0′ E0 E0′ U+ U+′ E+ E+′ A A′ B B′ c c′ : Raw.Expression C n)
    → Rule C
        (term-equal Γ i (closure i U0 E0 U+ E+ A B c)
          (closure i U0′ E0′ U+′ E+′ A′ B′ c′) (subuniverse i U0 E0 U+ E+))
  decoding-equal :
    {n : ℕ} (Γ : Context C n) (i : ℕ)
    (U0 U0′ E0 E0′ U+ U+′ E+ E+′ a a′ : Raw.Expression C n)
    → Rule C
        (type-equal Γ i (decoding i U0 E0 U+ E+ a)
          (decoding i U0′ E0′ U+′ E+′ a′))
  elimination-equal :
    {n : ℕ} (Γ : Context C n) (i j : ℕ)
    (U0 U0′ E0 E0′ U+ U+′ E+ E+′ M M′ b b′ s s′ a a′ : Raw.Expression C n)
    → Rule C
        (term-equal Γ j (subuniverse-induction i j U0 E0 U+ E+ M b s a)
          (subuniverse-induction i j U0′ E0′ U+′ E+′ M′ b′ s′ a′)
          (motive-at i j U0 E0 U+ E+ M a))

-- The four parameters with their types, and their equalities.
parameters :
  {C : Set} {n : ℕ} → Context C n → (i : ℕ)
  → (U0 E0 U+ E+ : Raw.Expression C n) → List (Judgment C)
parameters Γ i U0 E0 U+ E+ =
  type Γ i U0 ∷ term Γ (family-level i) E0 (family i U0)
  ∷ term Γ (operator-level i) U+ (operator i)
  ∷ term Γ (plus-decoding-level i) E+ (operator-decoding i U+) ∷ []

parameters-equal :
  {C : Set} {n : ℕ} → Context C n → (i : ℕ)
  → (U0 U0′ E0 E0′ U+ U+′ E+ E+′ : Raw.Expression C n) → List (Judgment C)
parameters-equal Γ i U0 U0′ E0 E0′ U+ U+′ E+ E+′ =
  type-equal Γ i U0 U0′ ∷ term-equal Γ (family-level i) E0 E0′ (family i U0)
  ∷ term-equal Γ (operator-level i) U+ U+′ (operator i)
  ∷ term-equal Γ (plus-decoding-level i) E+ E+′ (operator-decoding i U+)
  ∷ []

-- The closure's arguments; the motive and the methods.
arguments :
  {C : Set} {n : ℕ} → Context C n → (i : ℕ)
  → (U0 E0 U+ E+ A B c : Raw.Expression C n) → List (Judgment C)
arguments Γ i U0 E0 U+ E+ A B c =
  term Γ i A (subuniverse i U0 E0 U+ E+)
  ∷ term Γ (i ⊔ℕ i) B (family-of i U0 E0 U+ E+ A)
  ∷ term Γ i c (point-type i U0 E0 U+ E+ A B) ∷ []

methods :
  {C : Set} {n : ℕ} → Context C n → (i j : ℕ)
  → (U0 E0 U+ E+ M b s : Raw.Expression C n) → List (Judgment C)
methods Γ i j U0 E0 U+ E+ M b s =
  term Γ (motive-level i j) M (motive-type i j U0 E0 U+ E+)
  ∷ term Γ (inclusion-method-level i j) b (inclusion-method i j U0 E0 U+ E+ M)
  ∷ term Γ (closure-method-level i j) s (closure-method i j U0 E0 U+ E+ M)
  ∷ []

premises : {C : Set} {j : Judgment C} → Rule C j → List (Judgment C)
premises (formation Γ i U0 E0 U+ E+) = parameters Γ i U0 E0 U+ E+
premises (inclusion-introduction Γ i U0 E0 U+ E+ u) =
  parameters Γ i U0 E0 U+ E+ ++ term Γ i u U0 ∷ []
premises (closure-introduction Γ i U0 E0 U+ E+ A B c) =
  parameters Γ i U0 E0 U+ E+ ++ arguments Γ i U0 E0 U+ E+ A B c
premises (decoding-formation Γ i U0 E0 U+ E+ a) =
  parameters Γ i U0 E0 U+ E+ ++ term Γ i a (subuniverse i U0 E0 U+ E+) ∷ []
premises (elimination Γ i j U0 E0 U+ E+ M b s a) =
  parameters Γ i U0 E0 U+ E+ ++ methods Γ i j U0 E0 U+ E+ M b s
  ++ term Γ i a (subuniverse i U0 E0 U+ E+) ∷ []
premises (inclusion-decoding Γ i U0 E0 U+ E+ u) =
  parameters Γ i U0 E0 U+ E+ ++ term Γ i u U0 ∷ []
premises (closure-decoding Γ i U0 E0 U+ E+ A B c) =
  parameters Γ i U0 E0 U+ E+ ++ arguments Γ i U0 E0 U+ E+ A B c
premises (inclusion-computation Γ i j U0 E0 U+ E+ M b s u) =
  parameters Γ i U0 E0 U+ E+ ++ methods Γ i j U0 E0 U+ E+ M b s
  ++ term Γ i u U0 ∷ []
premises (closure-computation Γ i j U0 E0 U+ E+ M b s A B c) =
  parameters Γ i U0 E0 U+ E+ ++ methods Γ i j U0 E0 U+ E+ M b s
  ++ arguments Γ i U0 E0 U+ E+ A B c
premises (formation-equal Γ i U0 U0′ E0 E0′ U+ U+′ E+ E+′) =
  parameters-equal Γ i U0 U0′ E0 E0′ U+ U+′ E+ E+′
premises (inclusion-equal Γ i U0 U0′ E0 E0′ U+ U+′ E+ E+′ u u′) =
  parameters-equal Γ i U0 U0′ E0 E0′ U+ U+′ E+ E+′
  ++ term-equal Γ i u u′ U0 ∷ []
premises (closure-equal Γ i U0 U0′ E0 E0′ U+ U+′ E+ E+′ A A′ B B′ c c′) =
  parameters-equal Γ i U0 U0′ E0 E0′ U+ U+′ E+ E+′
  ++ term-equal Γ i A A′ (subuniverse i U0 E0 U+ E+)
  ∷ term-equal Γ (i ⊔ℕ i) B B′ (family-of i U0 E0 U+ E+ A)
  ∷ term-equal Γ i c c′ (point-type i U0 E0 U+ E+ A B) ∷ []
premises (decoding-equal Γ i U0 U0′ E0 E0′ U+ U+′ E+ E+′ a a′) =
  parameters-equal Γ i U0 U0′ E0 E0′ U+ U+′ E+ E+′
  ++ term-equal Γ i a a′ (subuniverse i U0 E0 U+ E+) ∷ []
premises
  (elimination-equal Γ i j U0 U0′ E0 E0′ U+ U+′ E+ E+′ M M′ b b′ s s′ a a′) =
  parameters-equal Γ i U0 U0′ E0 E0′ U+ U+′ E+ E+′
  ++ term-equal Γ (motive-level i j) M M′ (motive-type i j U0 E0 U+ E+)
  ∷ term-equal Γ (inclusion-method-level i j) b b′
      (inclusion-method i j U0 E0 U+ E+ M)
  ∷ term-equal Γ (closure-method-level i j) s s′
      (closure-method i j U0 E0 U+ E+ M)
  ∷ term-equal Γ i a a′ (subuniverse i U0 E0 U+ E+) ∷ []

rules : (C : Set) → Sig.Signature-Over (Judgment C) lzero lzero
rules C = rule-signature (Rule C) premises
