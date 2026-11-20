{-# OPTIONS --safe --without-K #-}

module SPT.IR.Translation.Fusion where

-- Fusion along a translation. The composite of τ after the identity
-- translation has τ's shape map and positions, and laws identified with
-- τ's, so it has τ's steps (`translate-left-unit`, `steps-left-unit`,
-- `left-unit`). A morphism after the fold along τ is the fold along τ into
-- its codomain (`fusion`). So the fold along τ into an algebra is the fold
-- of that algebra out of the target's generated part after the action of τ
-- (`action-fusion`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Fibers using (fiber)
open import SPT.Foundation.Induction.Initiality using (Section)

open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.IR.Description using
  (Desc; Indexed; index; indexed; Shape; Mark)
import SPT.IR.Generated as Generated
open import SPT.IR.Layers using
  (skeleton; read; collect; normal; up)
open import SPT.IR.Morphism using (Morphism)
open import SPT.IR.Morphism.Initiality using
  (generated; generated-fold)
import SPT.IR.Polynomial as Polynomial
open import SPT.IR.Restriction using (Position; input)
open import SPT.IR.Translation using
  (Translation; identity; compose; Pointed; translate)
open import SPT.IR.Translation.Initiality using (fold; unique)
open import SPT.IR.Translation.Morphism using
  (Fibers; step; Along; composed; compose-along; morphism-along)

------------------------------------------------------------------------
-- The identity translation is a left unit

-- The composite of τ after the identity has τ's shape map and positions
-- by computation; its inputs and output are τ's with `ap` of the identity,
-- identified with τ's. So it translates a layer to the same layer, and a
-- section of its step is a section of τ's.

unit-law :
  {ℓ : Level} {A : Set ℓ} {x y : A} (p : x ＝ y)
  → ap (λ e → e) p ∙ refl ＝ p
unit-law refl = refl

module _
  {s κ j j′ : Level} {E : Set j} {E′ : Set j′} {φ : E → E′}
  {γ : Desc {s = s} E} {γ′ : Desc {s = s} E′}
  (positions : (A : Set s) (B : A → Set (κ ⊔ j′)) → FunExt A B)
  (τ : Translation φ γ γ′) (W : Indexed κ E′)
  where

  translate-left-unit :
    (o : E′) (l : Pointed φ γ W o)
    → translate (compose (identity γ′) τ) W o l ＝ translate τ W o l
  translate-left-unit o ((c , h) , m) =
    ap₂
      (λ G n → (Translation.shape τ c , G) , n)
      ( positions
          (Position γ′ (indexed E′ (λ e → e)) (Translation.shape τ c))
          ( λ q →
              fiber (index W)
                (input γ′ (indexed E′ (λ e → e)) (Translation.shape τ c) q))
          ( λ q →
              transport (fiber (index W))
                (ap (λ e → e) (Translation.inputs τ c q) ∙ refl)
                (h (Translation.back τ c q)))
          ( λ q →
              transport (fiber (index W)) (Translation.inputs τ c q)
                (h (Translation.back τ c q)))
          ( λ q →
              ap
                ( λ d →
                    transport (fiber (index W)) d
                      (h (Translation.back τ c q)))
                (unit-law (Translation.inputs τ c q))))
      (ap (λ w → w ∙ m) (ap-id (Translation.output τ c)))

module _
  {s κ κ′ j j′ : Level} {E : Set j} {E′ : Set j′} {φ : E → E′}
  {γ : Desc {s = s} E} {γ′ : Desc {s = s} E′}
  (arities : (A : Set s) (B : A → Set j′) → FunExt A B)
  (positions : (A : Set s) (B : A → Set (κ′ ⊔ j′)) → FunExt A B)
  (τ : Translation φ γ γ′) (M : Algebra κ γ) (N : Algebra κ′ γ′)
  (law : Law M) (law′ : Law N)
  where

  open Algebra M using (K; value; operation)

  steps-left-unit :
    (z : Shape γ (indexed K value))
    (h :
      (p : Position γ (indexed K value) z)
      → Fibers φ M N (input γ (indexed K value) z p))
    → step arities (compose (identity γ′) τ) M N law law′ z h
      ＝ step arities τ M N law law′ z h
  steps-left-unit z h =
    ap
      ( λ t →
          Algebra.operation N (pr₁ t)
          , (law′ (pr₁ t) ∙ (pr₂ t ∙ ap φ (law z ⁻¹))))
      ( ap
          ( up arities (indexed (Algebra.K N) (Algebra.value N)) γ′
              (φ (Mark γ (indexed K value) z)))
          ( translate-left-unit positions τ
              (indexed (Algebra.K N) (Algebra.value N))
              (φ (Mark γ (indexed K value) z))
              ( ( skeleton (indexed K value) γ z
                , collect (indexed K value)
                    (λ e → fiber (Algebra.value N) (φ e)) γ z h)
              , ap φ (read (indexed K value) γ z))))

  left-unit :
    Along arities (compose (identity γ′) τ) M N law law′
    → Along arities τ M N law law′
  left-unit v = record
    { valuation = Section.valuation v
    ; equations = λ z →
        Section.equations v z
        ∙ steps-left-unit z
            (λ p → Section.valuation v (input γ (indexed K value) z p))
    }

------------------------------------------------------------------------
-- A morphism after the fold along a translation

-- The composite of a morphism h with the fold along τ is a morphism along
-- the composite of τ after the identity, so along τ, so it is the fold
-- along τ into the codomain of h, its identification of decodings
-- included.

module _
  {s κ κ′ κ″ j j′ : Level} {E : Set j} {E′ : Set j′} {φ : E → E′}
  {γ : Desc {s = s} E} {γ′ : Desc {s = s} E′}
  (arities : (A : Set s) (B : A → Set j′) → FunExt A B)
  (positions : Polynomial.Extensionality s κ)
  (motive′ : (A : Set s) (B : A → Set (κ′ ⊔ j′)) → FunExt A B)
  (motive″ : (A : Set s) (B : A → Set (κ″ ⊔ j′)) → FunExt A B)
  (τ : Translation φ γ γ′) (M : Algebra κ γ) (law : Law M)
  (N : Algebra κ′ γ′) (law′ : Law N) (P : Algebra κ″ γ′) (law″ : Law P)
  (h : Morphism (normal E′ arities) N P law′ law″)
  where

  fusion :
    (g : Generated.G M)
    → composed arities motive′ arities motive″ (identity γ′) τ (generated M)
        N P (Generated.make-β M law) law′ law″
        (morphism-along arities N P law′ law″ h)
        (fold arities positions motive′ τ M law N law′)
        g
      ＝ Section.valuation
          (fold arities positions motive″ τ M law P law″) g
  fusion g =
    unique arities positions motive″ τ M law P law″
      ( left-unit arities motive″ τ (generated M) P
          (Generated.make-β M law) law″
          ( compose-along arities motive′ arities motive″ (identity γ′) τ
              (generated M) N P (Generated.make-β M law) law′ law″
              (morphism-along arities N P law′ law″ h)
              (fold arities positions motive′ τ M law N law′)))
      g
    ⁻¹

------------------------------------------------------------------------
-- The action of a translation, then a fold

-- At the fold of N out of the target's generated part, fusion says that
-- the fold along τ into N is the action of τ on generated parts followed
-- by that fold.

module _
  {s κ κ′ κ″ j j′ : Level} {E : Set j} {E′ : Set j′} {φ : E → E′}
  {γ : Desc {s = s} E} {γ′ : Desc {s = s} E′}
  (arities : (A : Set s) (B : A → Set j′) → FunExt A B)
  (positions : Polynomial.Extensionality s κ)
  (positions′ : Polynomial.Extensionality s κ′)
  (motive′ : (A : Set s) (B : A → Set (s ⊔ κ′ ⊔ j′)) → FunExt A B)
  (motive″ : (A : Set s) (B : A → Set (κ″ ⊔ j′)) → FunExt A B)
  (τ : Translation φ γ γ′) (M : Algebra κ γ) (law : Law M)
  (M′ : Algebra κ′ γ′) (law′ : Law M′) (N : Algebra κ″ γ′) (law″ : Law N)
  where

  action-fusion :
    (g : Generated.G M)
    → composed arities motive′ arities motive″ (identity γ′) τ (generated M)
        (generated M′) N (Generated.make-β M law)
        (Generated.make-β M′ law′) law″
        ( morphism-along arities (generated M′) N
            (Generated.make-β M′ law′) law″
            ( generated-fold (normal E′ arities) positions′ motive″ M′ law′
                N law″))
        ( fold arities positions motive′ τ M law (generated M′)
            (Generated.make-β M′ law′))
        g
      ＝ Section.valuation
          (fold arities positions motive″ τ M law N law″) g
  action-fusion =
    fusion arities positions motive′ motive″ τ M law (generated M′)
      (Generated.make-β M′ law′) N law″
      ( generated-fold (normal E′ arities) positions′ motive″ M′ law′ N
          law″)
