{-# OPTIONS --safe --without-K #-}

module SPT.IR.Translation.Initiality where

-- The action of translations on generated parts, as a fold, and its
-- functor laws. Along a translation τ the generated part of a lawful
-- algebra M has a morphism into every lawful algebra of the target
-- (`fold`), every morphism along τ is the fold pointwise (`unique`), and
-- they form a contractible type (`initial`): Translation.Fold at the
-- generated part with its source induction. So the fold along the
-- identity translation is the identity (`fold-identity`), and the fold
-- along a composite is the composite of the folds (`fold-compose`).

open import SPT.Base
open import SPT.Foundation.Contractible using (is-contractible)
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Induction.Initiality using (Section; uniform)

open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.IR.Description using (Desc; indexed)
import SPT.IR.Generated as Generated
open import SPT.IR.Induction.Generated using (source; source-β)
open import SPT.IR.Morphism.Initiality using (generated)
import SPT.IR.Polynomial as Polynomial
open import SPT.IR.Restriction using (Position; input)
open import SPT.IR.Translation using
  (Translation; identity; compose)
open import SPT.IR.Translation.Morphism using
  (Fibers; step; Along; composed)
import SPT.IR.Translation.Fold as Fold

------------------------------------------------------------------------
-- The fold along a translation

-- Translation.Fold at the generated part of M with its source induction,
-- with extensionality for functions from the arities' level for the fold
-- and its uniqueness, as in Morphism.Initiality.

module _
  {s κ κ′ j j′ : Level} {E : Set j} {E′ : Set j′} {φ : E → E′}
  {γ : Desc {s = s} E} {γ′ : Desc {s = s} E′}
  (arities : (A : Set s) (B : A → Set j′) → FunExt A B)
  (positions : Polynomial.Extensionality s κ)
  (motive : (A : Set s) (B : A → Set (κ′ ⊔ j′)) → FunExt A B)
  (τ : Translation φ γ γ′) (M : Algebra κ γ) (law : Law M)
  (N : Algebra κ′ γ′) (law′ : Law N)
  where

  fold : Along arities τ (generated M) N (Generated.make-β M law) law′
  fold =
    Fold.fold arities τ (generated M) (Generated.make-β M law)
      (source M positions (κ′ ⊔ j′))
      (source-β M positions (κ′ ⊔ j′) motive) N law′

  unique :
    (h : Along arities τ (generated M) N (Generated.make-β M law) law′)
    (g : Generated.G M)
    → Section.valuation fold g ＝ Section.valuation h g
  unique =
    Fold.unique arities τ (generated M) (Generated.make-β M law)
      (source M positions (κ′ ⊔ j′))
      (source-β M positions (κ′ ⊔ j′) motive) N law′
      ( λ z →
          motive (Position γ (indexed (Generated.G M) (Generated.t M)) z)
            ( λ p →
                Fibers φ (generated M) N
                  (input γ (indexed (Generated.G M) (Generated.t M)) z p)))

  initial :
    ((A : Set (s ⊔ κ)) (B : A → Set (κ′ ⊔ j′)) → FunExt A B)
    → is-contractible
        (Along arities τ (generated M) N (Generated.make-β M law) law′)
  initial total =
    Fold.initial arities τ (generated M) (Generated.make-β M law)
      (source M positions (κ′ ⊔ j′))
      (source-β M positions (κ′ ⊔ j′) motive) N law′
      ( uniform (input γ (indexed (Generated.G M) (Generated.t M)))
          (Generated.make M) (source M positions (κ′ ⊔ j′))
          (Fibers φ (generated M) N)
          (step arities τ (generated M) N (Generated.make-β M law) law′)
          motive total total)

------------------------------------------------------------------------
-- The functor laws

-- Translation.Fold's functor laws at the generated parts: the identity map
-- and the composite of two folds are morphisms along the identity and the
-- composite translation, so uniqueness identifies the folds along those
-- with them.

module _
  {s κ j : Level} {E : Set j} {γ : Desc {s = s} E}
  (arities : (A : Set s) (B : A → Set j) → FunExt A B)
  (positions : Polynomial.Extensionality s κ)
  (motive : (A : Set s) (B : A → Set (s ⊔ κ ⊔ j)) → FunExt A B)
  (M : Algebra κ γ) (law : Law M)
  where

  fold-identity :
    (g : Generated.G M)
    → Section.valuation
        ( fold arities positions motive (identity γ) M law (generated M)
            (Generated.make-β M law))
        g
      ＝ (g , refl)
  fold-identity =
    Fold.fold-identity arities (generated M) (Generated.make-β M law)
      (source M positions (s ⊔ κ ⊔ j))
      (source-β M positions (s ⊔ κ ⊔ j) motive)
      ( λ z →
          motive (Position γ (indexed (Generated.G M) (Generated.t M)) z)
            ( λ p →
                Fibers (λ e → e) (generated M) (generated M)
                  (input γ (indexed (Generated.G M) (Generated.t M)) z p)))

module _
  {s κ κ′ κ″ j j′ j″ : Level}
  {E : Set j} {E′ : Set j′} {E″ : Set j″}
  {φ : E → E′} {φ′ : E′ → E″}
  {γ : Desc {s = s} E} {γ′ : Desc {s = s} E′} {γ″ : Desc {s = s} E″}
  (arities′ : (A : Set s) (B : A → Set j′) → FunExt A B)
  (arities″ : (A : Set s) (B : A → Set j″) → FunExt A B)
  (positions : Polynomial.Extensionality s κ)
  (positions′ : Polynomial.Extensionality s κ′)
  (motive′ : (A : Set s) (B : A → Set (s ⊔ κ′ ⊔ j′)) → FunExt A B)
  (motive″ : (A : Set s) (B : A → Set (κ″ ⊔ j″)) → FunExt A B)
  (τ′ : Translation φ′ γ′ γ″) (τ : Translation φ γ γ′)
  (M : Algebra κ γ) (law : Law M)
  (M′ : Algebra κ′ γ′) (law′ : Law M′)
  (N : Algebra κ″ γ″) (law″ : Law N)
  where

  fold-compose :
    (g : Generated.G M)
    → Section.valuation
        (fold arities″ positions motive″ (compose τ′ τ) M law N law″) g
      ＝ composed arities′ motive′ arities″ motive″ τ′ τ (generated M)
          (generated M′) N (Generated.make-β M law)
          (Generated.make-β M′ law′) law″
          (fold arities″ positions′ motive″ τ′ M′ law′ N law″)
          ( fold arities′ positions motive′ τ M law (generated M′)
              (Generated.make-β M′ law′))
          g
  fold-compose =
    Fold.fold-compose arities′ arities″ motive′ motive″ τ′ τ (generated M)
      (Generated.make-β M law) (source M positions (s ⊔ κ′ ⊔ j′))
      (source-β M positions (s ⊔ κ′ ⊔ j′) motive′)
      (source M positions (κ″ ⊔ j″))
      (source-β M positions (κ″ ⊔ j″) motive″)
      (generated M′) (Generated.make-β M′ law′)
      (source M′ positions′ (κ″ ⊔ j″))
      (source-β M′ positions′ (κ″ ⊔ j″) motive″) N law″
      ( λ z →
          motive″ (Position γ (indexed (Generated.G M) (Generated.t M)) z)
            ( λ p →
                Fibers (λ e → φ′ (φ e)) (generated M) N
                  (input γ (indexed (Generated.G M) (Generated.t M)) z p)))

-- The action of translations on the universal type of IR.Universal, with
-- its functor laws, is IR.Universal.Translation, through that type's
-- induction on source arguments; this folder imports no native
-- induction–recursion.
