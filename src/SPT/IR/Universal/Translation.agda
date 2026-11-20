{-# OPTIONS --safe --without-K #-}

module SPT.IR.Universal.Translation where

-- The action of translations on the universal types of IR.Universal, as
-- a fold, and its functor laws. Along a translation τ from γ to γ′, the
-- universal type of γ with its source induction (Source) has a morphism
-- into every lawful algebra of γ′ (`fold`); every morphism along τ is the
-- fold pointwise (`unique`), and they form a contractible type
-- (`initial`): IR.Translation.Fold at the universal type with its
-- source induction. So the fold along the identity translation is the
-- identity (`fold-identity`), and the fold along a composite is the
-- composite of the folds through the universal type of the middle
-- description (`fold-compose`).

open import SPT.Base
open import SPT.Foundation.Contractible using (is-contractible)
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Induction.Initiality using (Section; uniform)

open import SPT.IR.Universal using (U; value)
open import SPT.IR.Universal.Induction using (intro)
open import SPT.IR.Universal.Source using (algebra; law; source; source-β)
open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.IR.Description using (Desc; indexed)
open import SPT.IR.Restriction using (Position; input)
open import SPT.IR.Translation using (Translation; identity; compose)
open import SPT.IR.Translation.Morphism using
  (Fibers; step; Along; composed)
import SPT.IR.Translation.Fold as Fold

------------------------------------------------------------------------
-- The fold along a translation

-- Translation.Fold at the universal type with its source induction. The
-- motive is the fibers of N's decoding, of level κ′ ⊔ d′, over a carrier
-- of level s, so one extensionality from types of level s serves for the
-- positions, the carrier and the source arguments.

module _
  {s d d′ κ′ : Level} {D : Set d} {D′ : Set d′} {φ : D → D′}
  {γ : Desc {s = s} D} {γ′ : Desc {s = s} D′}
  (arities : (A : Set s) (B : A → Set d′) → FunExt A B)
  (motive : (A : Set s) (B : A → Set (κ′ ⊔ d′)) → FunExt A B)
  (τ : Translation φ γ γ′) (N : Algebra κ′ γ′) (law′ : Law N)
  where

  fold : Along arities τ (algebra γ) N (law γ) law′
  fold =
    Fold.fold arities τ (algebra γ) (law γ) (source γ (κ′ ⊔ d′))
      (source-β γ (κ′ ⊔ d′) motive) N law′

  unique :
    (h : Along arities τ (algebra γ) N (law γ) law′) (u : U γ)
    → Section.valuation fold u ＝ Section.valuation h u
  unique =
    Fold.unique arities τ (algebra γ) (law γ) (source γ (κ′ ⊔ d′))
      (source-β γ (κ′ ⊔ d′) motive) N law′
      ( λ z →
          motive (Position γ (indexed (U γ) (value γ)) z)
            ( λ p →
                Fibers φ (algebra γ) N
                  (input γ (indexed (U γ) (value γ)) z p)))

  initial : is-contractible (Along arities τ (algebra γ) N (law γ) law′)
  initial =
    Fold.initial arities τ (algebra γ) (law γ) (source γ (κ′ ⊔ d′))
      (source-β γ (κ′ ⊔ d′) motive) N law′
      ( uniform (input γ (indexed (U γ) (value γ))) (intro γ)
          (source γ (κ′ ⊔ d′))
          (Fibers φ (algebra γ) N)
          (step arities τ (algebra γ) N (law γ) law′)
          motive motive motive)

------------------------------------------------------------------------
-- The functor laws

-- Translation.Fold's functor laws at the universal types: the identity map
-- and the composite of two folds are morphisms along the identity and the
-- composite translation, so uniqueness identifies the folds along those
-- with them. The composite passes through the universal type of the
-- middle description.

fold-identity :
  {s d : Level} {D : Set d} (γ : Desc {s = s} D)
  (arities : (A : Set s) (B : A → Set d) → FunExt A B)
  (motive : (A : Set s) (B : A → Set (s ⊔ d)) → FunExt A B)
  (u : U γ)
  → Section.valuation
      (fold arities motive (identity γ) (algebra γ) (law γ)) u
    ＝ (u , refl)
fold-identity {s} {d} γ arities motive =
  Fold.fold-identity arities (algebra γ) (law γ) (source γ (s ⊔ d))
    (source-β γ (s ⊔ d) motive)
    ( λ z →
        motive (Position γ (indexed (U γ) (value γ)) z)
          ( λ p →
              Fibers (λ e → e) (algebra γ) (algebra γ)
                (input γ (indexed (U γ) (value γ)) z p)))

module _
  {s d d′ d″ κ″ : Level} {D : Set d} {D′ : Set d′} {D″ : Set d″}
  {φ : D → D′} {φ′ : D′ → D″}
  {γ : Desc {s = s} D} {γ′ : Desc {s = s} D′} {γ″ : Desc {s = s} D″}
  (arities′ : (A : Set s) (B : A → Set d′) → FunExt A B)
  (arities″ : (A : Set s) (B : A → Set d″) → FunExt A B)
  (motive′ : (A : Set s) (B : A → Set (s ⊔ d′)) → FunExt A B)
  (motive″ : (A : Set s) (B : A → Set (κ″ ⊔ d″)) → FunExt A B)
  (τ′ : Translation φ′ γ′ γ″) (τ : Translation φ γ γ′)
  (N : Algebra κ″ γ″) (law″ : Law N)
  where

  fold-compose :
    (u : U γ)
    → Section.valuation (fold arities″ motive″ (compose τ′ τ) N law″) u
      ＝ composed arities′ motive′ arities″ motive″ τ′ τ (algebra γ)
          (algebra γ′) N (law γ) (law γ′) law″
          (fold arities″ motive″ τ′ N law″)
          (fold arities′ motive′ τ (algebra γ′) (law γ′))
          u
  fold-compose =
    Fold.fold-compose arities′ arities″ motive′ motive″ τ′ τ (algebra γ)
      (law γ) (source γ (s ⊔ d′)) (source-β γ (s ⊔ d′) motive′)
      (source γ (κ″ ⊔ d″)) (source-β γ (κ″ ⊔ d″) motive″)
      (algebra γ′) (law γ′) (source γ′ (κ″ ⊔ d″))
      (source-β γ′ (κ″ ⊔ d″) motive″) N law″
      ( λ z →
          motive″ (Position γ (indexed (U γ) (value γ)) z)
            ( λ p →
                Fibers (λ e → φ′ (φ e)) (algebra γ) N
                  (input γ (indexed (U γ) (value γ)) z p)))
