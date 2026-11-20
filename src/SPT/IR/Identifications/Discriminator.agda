{-# OPTIONS --safe --without-K #-}

module SPT.IR.Identifications.Discriminator where

-- Hostile tests of agreement. At δ, two shapes whose child maps decode
-- alike do not agree, since agreement identifies the maps themselves
-- (`children-decode-alike`, `children-differ`, `not-identified`). In the
-- generated part of the identity algebra, two codes with one decoding are
-- distinct, so generated names are not unique (`same-decoding`,
-- `distinct`). The isomorphisms compute: refl goes to the trivial
-- agreement and back (`forward-refl`, `backward-trivial`, `agree-refl`).

open import SPT.Base
open import SPT.Foundation.Isomorphisms using (forward; backward)

open import SPT.IR.Algebra using (identity; identity-β)
import SPT.IR.Arguments as Arguments
open import SPT.IR.Description using
  (DS; Desc; ι; σ; δ; Indexed; indexed; index; Shape)
import SPT.IR.Generated as Generated
open import SPT.IR.Identifications using
  (Agreement; identifications-are-agreements; identified-elements-agree)

------------------------------------------------------------------------
-- Child maps are compared as maps

-- One recursive child and an output, over the two points with the
-- constant decoding 𝟙. The two constant child maps decode alike, but
-- agreement asks for an identification of the maps themselves, which
-- would identify ₀ and ₁.

child : DS {s = lzero} Set Set
child = δ 𝟙 (λ _ → ι 𝟙)

points : Indexed lzero Set
points = indexed 𝟚 (λ _ → 𝟙)

at₀ at₁ : Shape child points
at₀ = (λ _ → ₀) , lift ⋆
at₁ = (λ _ → ₁) , lift ⋆

children-decode-alike :
  (λ (a : 𝟙) → index points (pr₁ at₀ a))
    ＝ (λ (a : 𝟙) → index points (pr₁ at₁ a))
children-decode-alike = refl

children-differ : ¬ Agreement child points at₀ at₁
children-differ (p , _) = ₀-is-not-₁ (ap (λ k → k ⋆) p)

not-identified : ¬ (at₀ ＝ at₁)
not-identified e =
  children-differ
    ( forward (identifications-are-agreements child points at₀ at₁) e)

-- refl goes to the trivial agreement, and back.

forward-refl :
  forward (identifications-are-agreements child points at₀ at₀) refl
    ＝ (refl , lift ⋆)
forward-refl = refl

backward-trivial :
  backward (identifications-are-agreements child points at₀ at₀)
    ( refl , lift ⋆)
    ＝ refl
backward-trivial = refl

------------------------------------------------------------------------
-- Generated names are not unique

-- Two tags, both decoding to 𝟙. In the generated part of the identity
-- algebra, the raised fixed point, the two codes have one decoding and are
-- distinct: an identification of them gives one of their source arguments
-- (introduction has the retraction `unroll`, by `unroll-make`), whose
-- agreement identifies the tags.

twins : Desc {s = lzero} Set
twins = σ 𝟚 (λ _ → ι 𝟙)

code₀ code₁ : Generated.G (identity twins)
code₀ = Generated.make (identity twins) (₀ , lift ⋆)
code₁ = Generated.make (identity twins) (₁ , lift ⋆)

same-decoding :
  Generated.t (identity twins) code₀ ＝ Generated.t (identity twins) code₁
same-decoding =
  Generated.make-β (identity twins) (identity-β twins) (₀ , lift ⋆)
    ∙ Generated.make-β (identity twins) (identity-β twins) (₁ , lift ⋆) ⁻¹

distinct : ¬ (code₀ ＝ code₁)
distinct e =
  ₀-is-not-₁
    ( pr₁
        ( forward
            ( identifications-are-agreements twins
                ( indexed
                    ( Generated.G (identity twins))
                    ( Generated.t (identity twins)))
                ( ₀ , lift ⋆)
                ( ₁ , lift ⋆))
            ( Arguments.unroll-make (identity twins) (₀ , lift ⋆) ⁻¹
                ∙ ( ap (Arguments.unroll (identity twins)) e
                    ∙ Arguments.unroll-make (identity twins) (₁ , lift ⋆)))))

-- At refl, the agreement of a generated element with itself is trivial.

agree-refl :
  identified-elements-agree (identity twins) code₀ code₀ refl
    ＝ (refl , lift ⋆)
agree-refl = refl
