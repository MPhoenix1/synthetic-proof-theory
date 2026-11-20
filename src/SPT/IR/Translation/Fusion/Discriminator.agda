{-# OPTIONS --safe --without-K #-}

module SPT.IR.Translation.Fusion.Discriminator where

-- Fusion at a morphism that moves codes, so no instance of congruence
-- along a path. Two algebras of one constant constructor have the numbers
-- as codes and their operation at 0 and at 1 (`starting`); the successor is
-- a morphism between them (`successor`) and the identity map is not
-- (`not-morphism`). So the fold into 1 is the successor of the fold into
-- 0, out of a generated part (`morphism-fusion-suc`) and along a
-- translation that merges two tags (`merge`, `translation-fusion-suc`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Fibers using (fiber)
open import SPT.Foundation.Induction.Initiality using (Section)

open import SPT.IR.Algebra using
  (Algebra; Law; identity; identity-β)
open import SPT.IR.Description using
  (Desc; ι; σ; indexed; Shape)
import SPT.IR.Generated as Generated
open import SPT.IR.Layers using (normal)
open import SPT.IR.Morphism using (Morphism)
open import SPT.IR.Morphism.Fusion using (generated-fusion)
open import SPT.IR.Morphism.Initiality using (generated-fold)
open import SPT.IR.Restriction using (Position; input)
open import SPT.IR.Translation using (Translation)
open import SPT.IR.Translation.Fusion using (fusion)
open import SPT.IR.Translation.Initiality using (fold)

------------------------------------------------------------------------
-- Two algebras and a translation

-- One constant constructor, and two tagged ones with the same output. The
-- algebras differ only in the code their operation returns. The
-- translation sends both tags to the one constructor; no position exists
-- on either side.

one : Desc {s = lzero} 𝟙
one = ι ⋆

tagged : Desc {s = lzero} 𝟙
tagged = σ 𝟚 (λ b → ι ⋆)

starting : ℕ → Algebra lzero one
starting n = record
  { K = ℕ
  ; value = λ k → ⋆
  ; operation = λ z → n
  }

starting-law : (n : ℕ) → Law (starting n)
starting-law n z = refl

merge-back :
  (c : Shape tagged (indexed 𝟙 (λ e → e)))
  → Position one (indexed 𝟙 (λ e → e)) (lift ⋆)
  → Position tagged (indexed 𝟙 (λ e → e)) c
merge-back c (lift ())

merge-input :
  (c : Shape tagged (indexed 𝟙 (λ e → e)))
  (q : Position one (indexed 𝟙 (λ e → e)) (lift ⋆))
  → input tagged (indexed 𝟙 (λ e → e)) c (merge-back c q)
    ＝ input one (indexed 𝟙 (λ e → e)) (lift ⋆) q
merge-input c (lift ())

merge : Translation (λ e → e) tagged one
merge = record
  { shape = λ c → lift ⋆
  ; back = merge-back
  ; inputs = merge-input
  ; output = λ c → refl
  }

------------------------------------------------------------------------
-- The first component along a path

-- Transport in a fiber changes only the identification.

first-along :
  {ℓ κ : Level} {A : Set ℓ} {B : Set κ} (f : A → B) {b c : B}
  (p : b ＝ c) (x : fiber f b) → pr₁ (transport (fiber f) p x) ＝ pr₁ x
first-along f refl x = refl

------------------------------------------------------------------------
-- The successor, and fusion at it

-- The successor commutes with the operations, 0 going to 1, and the
-- identity map does not. Fusion then says that the fold into 1 is the
-- successor of the fold into 0, for any extensionality for the arities.

module _ (arities : (A : Set) (B : A → Set) → FunExt A B) where

  successor :
    Morphism (normal 𝟙 arities) (starting zero) (starting (suc zero))
      (starting-law zero) (starting-law (suc zero))
  successor = record
    { valuation = λ n → suc n , refl
    ; equations = λ z → refl
    }

  not-morphism :
    (f :
      Morphism (normal 𝟙 arities) (starting zero) (starting (suc zero))
        (starting-law zero) (starting-law (suc zero)))
    → ((n : ℕ) → Section.valuation f n ＝ (n , refl))
    → 𝟘
  not-morphism f same =
    zero-is-not-suc (ap pr₁ (same zero ⁻¹ ∙ Section.equations f (lift ⋆)))

  morphism-fusion-suc :
    (g : Generated.G (identity one))
    → suc
        ( pr₁
            ( Section.valuation
                ( generated-fold (normal 𝟙 arities) arities arities
                    (identity one) (identity-β one) (starting zero)
                    (starting-law zero))
                g))
      ＝ pr₁
          ( Section.valuation
              ( generated-fold (normal 𝟙 arities) arities arities
                  (identity one) (identity-β one) (starting (suc zero))
                  (starting-law (suc zero)))
              g)
  morphism-fusion-suc g =
    let F =
          Section.valuation
            ( generated-fold (normal 𝟙 arities) arities arities
                (identity one) (identity-β one) (starting zero)
                (starting-law zero))
            g
    in
    first-along (λ k → ⋆) (pr₂ F) (suc (pr₁ F) , refl) ⁻¹
    ∙ ap pr₁
        ( generated-fusion arities arities arities arities (identity one)
            (identity-β one) (starting zero) (starting-law zero)
            (starting (suc zero)) (starting-law (suc zero)) successor g)

  translation-fusion-suc :
    (g : Generated.G (identity tagged))
    → suc
        ( pr₁
            ( Section.valuation
                ( fold arities arities arities merge (identity tagged)
                    (identity-β tagged) (starting zero) (starting-law zero))
                g))
      ＝ pr₁
          ( Section.valuation
              ( fold arities arities arities merge (identity tagged)
                  (identity-β tagged) (starting (suc zero))
                  (starting-law (suc zero)))
              g)
  translation-fusion-suc g =
    let F =
          Section.valuation
            ( fold arities arities arities merge (identity tagged)
                (identity-β tagged) (starting zero) (starting-law zero))
            g
    in
    first-along (λ k → ⋆) (pr₂ F) (suc (pr₁ F) , refl) ⁻¹
    ∙ ap pr₁
        ( fusion arities arities arities arities merge (identity tagged)
            (identity-β tagged) (starting zero) (starting-law zero)
            (starting (suc zero)) (starting-law (suc zero)) successor g)
