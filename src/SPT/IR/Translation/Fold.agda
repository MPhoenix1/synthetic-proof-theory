{-# OPTIONS --safe --without-K #-}

module SPT.IR.Translation.Fold where

-- Initiality along translations for algebras with induction on source
-- arguments. Along a translation τ over φ, for an algebra M with induction
-- on its source arguments and its computation identity, the fold into
-- every algebra of the target is a morphism along τ, every morphism along
-- τ is the fold pointwise (`fold`, `unique`), and the morphisms form a
-- contractible type (`initial`), by Foundation.Induction.Initiality at the
-- step of Translation.Morphism. So the fold along the identity translation
-- is the identity (`fold-identity`), and the fold along a composite is the
-- composite of the folds through an algebra of the middle description
-- with induction (`fold-compose`):
--
--   fold (identity γ) M M k = (k , refl),
--   fold (compose τ′ τ) M N k = composed (fold τ′ M′ N) (fold τ M M′) k.
--
-- The generated parts of algebras (Translation.Initiality) and the
-- universal type of IR.Universal (IR.Universal.Translation) are such
-- algebras. The extensionality is that of Morphism.Initiality: over the
-- positions for uniqueness, the rest of Induction.Initiality's for
-- initiality.

open import SPT.Base
open import SPT.Foundation.Contractible using (is-contractible)
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Induction.Initiality using
  (Section; Extensionality; center; homotopy; contractible)

open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.IR.Description using (Desc; indexed; Shape)
open import SPT.IR.Restriction using (Position; input)
open import SPT.IR.Translation using (Translation; identity; compose)
open import SPT.IR.Translation.Morphism using
  (Fibers; step; Along; identity-along; composed; compose-along)

------------------------------------------------------------------------
-- The fold along a translation

-- The morphisms along τ out of M are the sections of N's step over M, so
-- Foundation.Induction.Initiality applies at M's induction: induction at
-- the step is the fold; with extensionality over the positions every
-- morphism along τ is the fold pointwise, and with the rest of its
-- extensionality the morphisms form a contractible type.

module _
  {s κ κ′ j j′ : Level} {E : Set j} {E′ : Set j′} {φ : E → E′}
  {γ : Desc {s = s} E} {γ′ : Desc {s = s} E′}
  (arities : (A : Set s) (B : A → Set j′) → FunExt A B)
  (τ : Translation φ γ γ′) (M : Algebra κ γ) (law : Law M)
  (ind :
    Argument-Induction (input γ (indexed (Algebra.K M) (Algebra.value M)))
      (Algebra.operation M) (κ′ ⊔ j′))
  (computation :
    Argument-Computation (input γ (indexed (Algebra.K M) (Algebra.value M)))
      (Algebra.operation M) ind)
  (N : Algebra κ′ γ′) (law′ : Law N)
  where

  fold : Along arities τ M N law law′
  fold =
    center (input γ (indexed (Algebra.K M) (Algebra.value M)))
      (Algebra.operation M) ind computation (Fibers φ M N)
      (step arities τ M N law law′)

  unique :
    ( (z : Shape γ (indexed (Algebra.K M) (Algebra.value M)))
      → FunExt (Position γ (indexed (Algebra.K M) (Algebra.value M)) z)
          ( λ p →
              Fibers φ M N
                (input γ (indexed (Algebra.K M) (Algebra.value M)) z p)))
    → (h : Along arities τ M N law law′) (k : Algebra.K M)
    → Section.valuation fold k ＝ Section.valuation h k
  unique =
    homotopy (input γ (indexed (Algebra.K M) (Algebra.value M)))
      (Algebra.operation M) ind computation (Fibers φ M N)
      (step arities τ M N law law′)

  initial :
    Extensionality (input γ (indexed (Algebra.K M) (Algebra.value M)))
      (Algebra.operation M) ind (Fibers φ M N)
      (step arities τ M N law law′)
    → is-contractible (Along arities τ M N law law′)
  initial =
    contractible (input γ (indexed (Algebra.K M) (Algebra.value M)))
      (Algebra.operation M) ind computation (Fibers φ M N)
      (step arities τ M N law law′)

------------------------------------------------------------------------
-- The functor laws

-- The identity map and the composite of two folds are morphisms along the
-- identity and the composite translation (Translation.Morphism), so
-- uniqueness identifies the folds along those with them. The composite
-- passes through an algebra M′ of the middle description with induction.

module _
  {s κ j : Level} {E : Set j} {γ : Desc {s = s} E}
  (arities : (A : Set s) (B : A → Set j) → FunExt A B)
  (M : Algebra κ γ) (law : Law M)
  (ind :
    Argument-Induction (input γ (indexed (Algebra.K M) (Algebra.value M)))
      (Algebra.operation M) (κ ⊔ j))
  (computation :
    Argument-Computation (input γ (indexed (Algebra.K M) (Algebra.value M)))
      (Algebra.operation M) ind)
  (positions :
    (z : Shape γ (indexed (Algebra.K M) (Algebra.value M)))
    → FunExt (Position γ (indexed (Algebra.K M) (Algebra.value M)) z)
        ( λ p →
            Fibers (λ e → e) M M
              (input γ (indexed (Algebra.K M) (Algebra.value M)) z p)))
  where

  fold-identity :
    (k : Algebra.K M)
    → Section.valuation
        (fold arities (identity γ) M law ind computation M law) k
      ＝ (k , refl)
  fold-identity =
    unique arities (identity γ) M law ind computation M law positions
      (identity-along arities M law)

module _
  {s κ κ′ κ″ j j′ j″ : Level} {E : Set j} {E′ : Set j′} {E″ : Set j″}
  {φ : E → E′} {φ′ : E′ → E″}
  {γ : Desc {s = s} E} {γ′ : Desc {s = s} E′} {γ″ : Desc {s = s} E″}
  (arities′ : (A : Set s) (B : A → Set j′) → FunExt A B)
  (arities″ : (A : Set s) (B : A → Set j″) → FunExt A B)
  (motive′ : (A : Set s) (B : A → Set (κ′ ⊔ j′)) → FunExt A B)
  (motive″ : (A : Set s) (B : A → Set (κ″ ⊔ j″)) → FunExt A B)
  (τ′ : Translation φ′ γ′ γ″) (τ : Translation φ γ γ′)
  (M : Algebra κ γ) (law : Law M)
  (ind :
    Argument-Induction (input γ (indexed (Algebra.K M) (Algebra.value M)))
      (Algebra.operation M) (κ′ ⊔ j′))
  (computation :
    Argument-Computation (input γ (indexed (Algebra.K M) (Algebra.value M)))
      (Algebra.operation M) ind)
  (ind″ :
    Argument-Induction (input γ (indexed (Algebra.K M) (Algebra.value M)))
      (Algebra.operation M) (κ″ ⊔ j″))
  (computation″ :
    Argument-Computation (input γ (indexed (Algebra.K M) (Algebra.value M)))
      (Algebra.operation M) ind″)
  (M′ : Algebra κ′ γ′) (law′ : Law M′)
  (ind′ :
    Argument-Induction (input γ′ (indexed (Algebra.K M′) (Algebra.value M′)))
      (Algebra.operation M′) (κ″ ⊔ j″))
  (computation′ :
    Argument-Computation (input γ′ (indexed (Algebra.K M′) (Algebra.value M′)))
      (Algebra.operation M′) ind′)
  (N : Algebra κ″ γ″) (law″ : Law N)
  (positions :
    (z : Shape γ (indexed (Algebra.K M) (Algebra.value M)))
    → FunExt (Position γ (indexed (Algebra.K M) (Algebra.value M)) z)
        ( λ p →
            Fibers (λ e → φ′ (φ e)) M N
              (input γ (indexed (Algebra.K M) (Algebra.value M)) z p)))
  where

  fold-compose :
    (k : Algebra.K M)
    → Section.valuation
        (fold arities″ (compose τ′ τ) M law ind″ computation″ N law″) k
      ＝ composed arities′ motive′ arities″ motive″ τ′ τ M M′ N law law′
          law″
          (fold arities″ τ′ M′ law′ ind′ computation′ N law″)
          (fold arities′ τ M law ind computation M′ law′)
          k
  fold-compose =
    unique arities″ (compose τ′ τ) M law ind″ computation″ N law″ positions
      ( compose-along arities′ motive′ arities″ motive″ τ′ τ M M′ N law
          law′ law″
          (fold arities″ τ′ M′ law′ ind′ computation′ N law″)
          (fold arities′ τ M law ind computation M′ law′))
