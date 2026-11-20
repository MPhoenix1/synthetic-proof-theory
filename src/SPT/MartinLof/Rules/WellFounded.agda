{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Rules.WellFounded where

-- The rules of W-types, as a signature over the judgments of the core
-- theory (`Rule`, `premises`, `rules`): for A at level m and B at level k
-- over A, W A B is a type at level m ⊔ k (formation), with sup a f for f :
-- B a → W A B (introduction), induction into a motive M at level l over W
-- A B (elimination), its β rule (computation), and the congruence of each
-- former. The induction method lives over a shape x, its children f : B x
-- → W A B and the induction hypotheses h : (y : B x) → M (f y)
-- (`method-context`), with type M (sup x f) (`method-type`). At sup a f
-- the hypotheses are λ y. rec (f y) (`child`, `hypotheses`).

open import SPT.Base
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Signature.Sum as Sig
import SPT.Foundation.Tree as Tree
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Formers using
  (pi; lambda; application; tree; supremum; tree-induction; weaken; weaken-past
  ; instantiate; instantiate-past; instantiate₃)
open import SPT.MartinLof.Judgment using
  (Context; _▸[_]_; Judgment; term; term-equal; type; type-equal
  ; rule-signature)

------------------------------------------------------------------------
-- The induction method

-- Γ extended by a shape x : A, children f : B x → W A B and hypotheses
-- h : (y : B x) → M (f y).
method-context :
  {C : Set} {n : ℕ} → Context C n → (m k l : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc n) → Raw.Expression C (suc n)
  → Context C (suc (suc (suc n)))
method-context Γ m k l A B M =
  Γ ▸[ m ] A
    ▸[ k ⊔ℕ (m ⊔ℕ k) ] pi k (m ⊔ℕ k) B (weaken (weaken (tree m k A B)))
    ▸[ k ⊔ℕ l ] pi k l (weaken B)
      (instantiate-past 3 M
        (application k (m ⊔ℕ k) (weaken (weaken B))
          (weaken (weaken (weaken (weaken (tree m k A B)))))
          (Tree.hole (fsuc fzero)) (Tree.hole fzero)))

-- M at sup x f, in the method context.
method-type :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc n) → Raw.Expression C (suc n)
  → Raw.Expression C (suc (suc (suc n)))
method-type {n = n} m k A B M =
  instantiate-past 3 M
    (supremum m k (weaken (weaken (weaken A))) (weaken-past n 1 3 B)
      (Tree.hole (fsuc (fsuc fzero)))
      (Tree.hole (fsuc fzero)))

-- The child f y of sup a f at a position y : B a, in the scope of y.
child :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc n) → Raw.Expression C n → Raw.Expression C n
  → Raw.Expression C (suc n)
child m k A B a f =
  application k (m ⊔ℕ k) (weaken (instantiate B a))
    (weaken (weaken (tree m k A B))) (weaken f) (Tree.hole fzero)

-- The induction hypotheses at sup a f: λ y. rec (f y).
hypotheses :
  {C : Set} {n : ℕ} (m k l : ℕ) → Raw.Expression C n
  → Raw.Expression C (suc n) → Raw.Expression C (suc n)
  → Raw.Expression C (suc (suc (suc n)))
  → Raw.Expression C n → Raw.Expression C n → Raw.Expression C n
hypotheses {n = n} m k l A B M c a f =
  lambda k l (instantiate B a)
    (instantiate (weaken-past n 1 1 M) (child m k A B a f))
    (tree-induction m k l (weaken A) (weaken-past n 1 1 B)
      (weaken-past n 1 1 M) (weaken-past n 3 1 c) (child m k A B a f))

------------------------------------------------------------------------
-- Rules

data Rule (C : Set) : Judgment C → Set where
  formation :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n))
    → Rule C (type Γ (m ⊔ℕ k) (tree m k A B))
  introduction :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (a f : Raw.Expression C n)
    → Rule C (term Γ (m ⊔ℕ k) (supremum m k A B a f) (tree m k A B))
  elimination :
    {n : ℕ} (Γ : Context C n) (m k l : ℕ) (A : Raw.Expression C n)
    (B M : Raw.Expression C (suc n))
    (c : Raw.Expression C (suc (suc (suc n))))
    (w : Raw.Expression C n)
    → Rule C (term Γ l (tree-induction m k l A B M c w) (instantiate M w))
  computation :
    {n : ℕ} (Γ : Context C n) (m k l : ℕ) (A : Raw.Expression C n)
    (B M : Raw.Expression C (suc n))
    (c : Raw.Expression C (suc (suc (suc n))))
    (a f : Raw.Expression C n)
    → Rule C
        (term-equal Γ l
          (tree-induction m k l A B M c (supremum m k A B a f))
          (instantiate₃ c a f (hypotheses m k l A B M c a f))
          (instantiate M (supremum m k A B a f)))
  formation-equal :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A A′ : Raw.Expression C n)
    (B B′ : Raw.Expression C (suc n))
    → Rule C (type-equal Γ (m ⊔ℕ k) (tree m k A B) (tree m k A′ B′))
  introduction-equal :
    {n : ℕ} (Γ : Context C n) (m k : ℕ) (A A′ : Raw.Expression C n)
    (B B′ : Raw.Expression C (suc n)) (a a′ f f′ : Raw.Expression C n)
    → Rule C
        (term-equal Γ (m ⊔ℕ k) (supremum m k A B a f)
          (supremum m k A′ B′ a′ f′) (tree m k A B))
  elimination-equal :
    {n : ℕ} (Γ : Context C n) (m k l : ℕ) (A A′ : Raw.Expression C n)
    (B B′ M M′ : Raw.Expression C (suc n))
    (c c′ : Raw.Expression C (suc (suc (suc n))))
    (w w′ : Raw.Expression C n)
    → Rule C
        (term-equal Γ l (tree-induction m k l A B M c w)
          (tree-induction m k l A′ B′ M′ c′ w′) (instantiate M w))

premises : {C : Set} {j : Judgment C} → Rule C j → List (Judgment C)
premises (formation Γ m k A B) = type Γ m A ∷ type (Γ ▸[ m ] A) k B ∷ []
premises (introduction Γ m k A B a f) =
  type Γ m A ∷ type (Γ ▸[ m ] A) k B ∷ term Γ m a A
  ∷ term Γ (k ⊔ℕ (m ⊔ℕ k)) f
      (pi k (m ⊔ℕ k) (instantiate B a) (weaken (tree m k A B)))
  ∷ []
premises (elimination Γ m k l A B M c w) =
  type Γ m A ∷ type (Γ ▸[ m ] A) k B
  ∷ type (Γ ▸[ m ⊔ℕ k ] tree m k A B) l M
  ∷ term (method-context Γ m k l A B M) l c (method-type m k A B M)
  ∷ term Γ (m ⊔ℕ k) w (tree m k A B) ∷ []
premises (computation Γ m k l A B M c a f) =
  type Γ m A ∷ type (Γ ▸[ m ] A) k B
  ∷ type (Γ ▸[ m ⊔ℕ k ] tree m k A B) l M
  ∷ term (method-context Γ m k l A B M) l c (method-type m k A B M)
  ∷ term Γ m a A
  ∷ term Γ (k ⊔ℕ (m ⊔ℕ k)) f
      (pi k (m ⊔ℕ k) (instantiate B a) (weaken (tree m k A B)))
  ∷ []
premises (formation-equal Γ m k A A′ B B′) =
  type-equal Γ m A A′ ∷ type-equal (Γ ▸[ m ] A) k B B′ ∷ []
premises (introduction-equal Γ m k A A′ B B′ a a′ f f′) =
  type-equal Γ m A A′ ∷ type-equal (Γ ▸[ m ] A) k B B′
  ∷ term-equal Γ m a a′ A
  ∷ term-equal Γ (k ⊔ℕ (m ⊔ℕ k)) f f′
      (pi k (m ⊔ℕ k) (instantiate B a) (weaken (tree m k A B)))
  ∷ []
premises (elimination-equal Γ m k l A A′ B B′ M M′ c c′ w w′) =
  type-equal Γ m A A′ ∷ type-equal (Γ ▸[ m ] A) k B B′
  ∷ type-equal (Γ ▸[ m ⊔ℕ k ] tree m k A B) l M M′
  ∷ term-equal (method-context Γ m k l A B M) l c c′
      (method-type m k A B M)
  ∷ term-equal Γ (m ⊔ℕ k) w w′ (tree m k A B) ∷ []

rules : (C : Set) → Sig.Signature-Over (Judgment C) lzero lzero
rules C = rule-signature (Rule C) premises
