{-# OPTIONS --safe --without-K #-}

module SPT.IR.Morphism.Discriminator where

-- The decoding identifications of morphisms are load-bearing. For the
-- description with one constant constructor at e, every map from the
-- generated part of the one-point algebra into the one-point algebra
-- preserves codes (`Codes`, `codes`), but a morphism has decoding refl at
-- the introduction (`untwisted`, `pinned`): the map with a loop p there is
-- one only when p is refl (`twisted-not-morphism`, `codes-undetermined`).
-- With a second point, the identity algebra has no morphism into the
-- one-point algebra (`no-identity-morphism`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Induction.Initiality using (Section)

open import SPT.IR.Algebra using
  (Algebra; Law; identity; identity-β)
open import SPT.IR.Description using (Desc; ι; indexed; Shape)
import SPT.IR.Generated as Generated
open import SPT.IR.Morphism using (Fibers; step; Morphism)
open import SPT.IR.Morphism.Initiality using (generated)
open import SPT.IR.Restriction using (input)

------------------------------------------------------------------------
-- Preservation of codes

-- The law of a morphism with its decoding identification deleted: the
-- code of the image of an operation is the code of the step there.

module _
  {s κ κ′ j : Level} {E : Set j} {γ : Desc {s = s} E}
  (extensionality : (A : Set s) → FunExt A (λ _ → E))
  (M : Algebra κ γ) (N : Algebra κ′ γ) (law : Law M) (law′ : Law N)
  where

  open Algebra M using (K; value; operation)

  Codes : ((k : K) → Fibers M N k) → Set (s ⊔ κ ⊔ κ′)
  Codes v =
    (z : Shape γ (indexed K value))
    → pr₁ (v (operation z))
      ＝ pr₁
          ( step extensionality M N law law′ z
              (λ q → v (input γ (indexed K value) z q)))

------------------------------------------------------------------------
-- One constant constructor

-- The description with one shape, the unit, whose output is e. The
-- one-point algebra decodes its point to e, with its law by refl.

constant : {j : Level} {E : Set j} → E → Desc {s = lzero} E
constant e = ι e

module _ {j : Level} {E : Set j} (e : E) where

  point : Algebra lzero (constant e)
  point = record
    { K = 𝟙
    ; value = λ k → e
    ; operation = λ z → ⋆
    }

  point-law : Law point
  point-law z = refl

------------------------------------------------------------------------
-- Codes do not determine morphisms

-- From the generated part of the one-point algebra into the one-point
-- algebra every code is the point, so every map preserves codes. At the
-- introduction the step is (⋆ , refl) by computation, since the law of
-- the point, the assembly and make-β are refl there. So every morphism
-- has decoding refl at the introduction, and the map with a loop p there
-- is a morphism only when p is refl.

straight :
  {j : Level} {E : Set j} (e : E) (g : Algebra.K (generated (point e)))
  → Fibers (generated (point e)) (point e) g
straight e g = ⋆ , refl

twisted :
  {j : Level} {E : Set j} (e : E) (p : e ＝ e)
  (g : Algebra.K (generated (point e)))
  → Fibers (generated (point e)) (point e) g
twisted e p g = ⋆ , p

module _
  {j : Level} {E : Set j} (e : E)
  (extensionality : (A : Set) → FunExt A (λ _ → E))
  where

  codes :
    ( v :
        (g : Algebra.K (generated (point e)))
        → Fibers (generated (point e)) (point e) g)
    → Codes extensionality (generated (point e)) (point e)
        (Generated.make-β (point e) (point-law e)) (point-law e) v
  codes v z = refl

  untwisted :
    Morphism extensionality (generated (point e)) (point e)
      (Generated.make-β (point e) (point-law e)) (point-law e)
  untwisted = record
    { valuation = straight e
    ; equations = λ z → refl
    }

  pinned :
    ( h :
        Morphism extensionality (generated (point e)) (point e)
          (Generated.make-β (point e) (point-law e)) (point-law e))
    → Section.valuation h
        (Algebra.operation (generated (point e)) (lift ⋆))
      ＝ (⋆ , refl)
  pinned h = Section.equations h (lift ⋆)

module _
  {j : Level} {E : Set j} (e : E) (p : e ＝ e)
  (extensionality : (A : Set) → FunExt A (λ _ → E))
  where

  twisted-not-morphism :
    ( h :
        Morphism extensionality (generated (point e)) (point e)
          (Generated.make-β (point e) (point-law e)) (point-law e))
    → ( (g : Algebra.K (generated (point e)))
        → Section.valuation h g ＝ twisted e p g)
    → p ＝ refl
  twisted-not-morphism h agrees =
    ap pr₂
      ( agrees (Algebra.operation (generated (point e)) (lift ⋆)) ⁻¹
      ∙ pinned e extensionality h)

  codes-undetermined :
    ( ( v w :
          (g : Algebra.K (generated (point e)))
          → Fibers (generated (point e)) (point e) g)
      → Codes extensionality (generated (point e)) (point e)
          (Generated.make-β (point e) (point-law e)) (point-law e) v
      → Codes extensionality (generated (point e)) (point e)
          (Generated.make-β (point e) (point-law e)) (point-law e) w
      → (g : Algebra.K (generated (point e))) → v g ＝ w g)
    → p ＝ refl
  codes-undetermined determined =
    ap pr₂
      ( determined (twisted e p) (straight e)
          (codes e extensionality (twisted e p))
          (codes e extensionality (straight e))
          (Algebra.operation (generated (point e)) (lift ⋆)))

------------------------------------------------------------------------
-- The identity algebra is not initial

-- The identity algebra's carrier is every output, and the one-point
-- algebra decodes only to e, so a morphism would identify e with every
-- output.

module _
  {j : Level} {E : Set j} (e e′ : E) (apart : e ≠ e′)
  (extensionality : (A : Set) → FunExt A (λ _ → E))
  where

  no-identity-morphism :
    ¬ Morphism extensionality (identity (constant e)) (point e)
        (identity-β (constant e)) (point-law e)
  no-identity-morphism h = apart (pr₂ (Section.valuation h e′))
