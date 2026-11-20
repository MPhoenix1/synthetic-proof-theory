{-# OPTIONS --safe --without-K #-}

module SPT.IR.Identifications where

-- Identifications of shapes and of generated elements, layer by layer. Two
-- shapes agree when their tags are identified, their δ-children are
-- identified as whole maps, and the rest agrees after transport along these
-- (`Agreement`). For every indexed family, identifications of shapes are
-- agreements, with no hypothesis (`identifications-are-agreements`). So,
-- under extensionality for families over positions, identifications of
-- generated elements are agreements of their source arguments
-- (`generated-identifications`). Equal decodings do not give equal elements.

open import SPT.Base
open import SPT.Foundation.HalfAdjoint using (ap-is-isomorphism)
open import SPT.Foundation.Isomorphisms using
  ( _≅_
  ; forward
  ; backward
  ; backward-forward
  ; forward-backward
  ; ≅-trans
  ; Σ-cong
  ; Σ-＝-≅
  )
open import SPT.Foundation.Propositions using (propositions-are-sets)

open import SPT.IR.Algebra using (Algebra)
import SPT.IR.Arguments as Arguments
open import SPT.IR.Description using
  (DS; Desc; ι; σ; δ; Indexed; indexed; index; Shape)
import SPT.IR.Generated as Generated
open import SPT.IR.Polynomial using (Extensionality)

------------------------------------------------------------------------
-- Agreement of shapes

-- At ι two shapes agree trivially. At σ they agree through an
-- identification of their tags, and at δ through an identification of
-- their child maps as whole maps; in both, the rest of the shapes agrees
-- after transport along it. Mathematical shape:
--
--   Agreement (ι e) Z x y = 𝟙
--   Agreement (σ A f) Z (a , x) (b , y)
--     = Σ (p : a ＝ b). Agreement (f b) Z (p_* x) y
--   Agreement (δ A F) Z (g , x) (h , y)
--     = Σ (p : g ＝ h). Agreement (F (index Z ∘ h)) Z (p_* x) y.

Agreement :
  {s κ d e : Level} {D : Set d} {E : Set e} (γ : DS {s = s} D E)
  (Z : Indexed κ D) → Shape γ Z → Shape γ Z → Set (s ⊔ κ)
Agreement {s} {κ} (ι e) Z x y = Lift (s ⊔ κ) 𝟙
Agreement (σ A f) Z (a , x) (b , y) =
  Σ (a ＝ b) (λ p →
    Agreement (f b) Z (transport (λ c → Shape (f c) Z) p x) y)
Agreement (δ A F) Z (g , x) (h , y) =
  Σ (g ＝ h) (λ p →
    Agreement (F (λ a → index Z (h a))) Z
      ( transport (λ k → Shape (F (λ a → index Z (k a))) Z) p x)
      ( y))

------------------------------------------------------------------------
-- Identifications of shapes are agreements

-- By recursion on the description. At ι both shapes are the point of the
-- unit type, a proposition and so a set. At σ and δ, identifications of
-- pairs are pairs of identifications (SPT's `Σ-＝-≅`), and the
-- identification of the rest is the recursive case, after transport. No
-- extensionality is used: the child maps at δ are identified as maps.

-- Identifications of points of the unit type are its points.
units :
  {μ : Level} (x y : Lift μ 𝟙) → (x ＝ y) ≅ Lift μ 𝟙
units {μ} x y = record
  { forward = λ _ → lift ⋆
  ; backward = λ _ → refl
  ; backward-forward = λ p →
      propositions-are-sets {A = Lift μ 𝟙} (λ u v → refl) x y refl p
  ; forward-backward = λ _ → refl
  }

identifications-are-agreements :
  {s κ d e : Level} {D : Set d} {E : Set e} (γ : DS {s = s} D E)
  (Z : Indexed κ D) (x y : Shape γ Z) → (x ＝ y) ≅ Agreement γ Z x y
identifications-are-agreements (ι e) Z x y = units x y
identifications-are-agreements (σ A f) Z (a , x) (b , y) =
  ≅-trans
    ( Σ-＝-≅ {B = λ c → Shape (f c) Z} (a , x) (b , y))
    ( Σ-cong
        ( λ p →
            identifications-are-agreements (f b) Z
              ( transport (λ c → Shape (f c) Z) p x)
              ( y)))
identifications-are-agreements (δ A F) Z (g , x) (h , y) =
  ≅-trans
    ( Σ-＝-≅ {B = λ k → Shape (F (λ a → index Z (k a))) Z} (g , x) (h , y))
    ( Σ-cong
        ( λ p →
            identifications-are-agreements (F (λ a → index Z (h a))) Z
              ( transport (λ k → Shape (F (λ a → index Z (k a))) Z) p x)
              ( y)))

------------------------------------------------------------------------
-- Identifications of generated elements

-- An identification of generated elements gives an agreement of their
-- source arguments, with no hypothesis (`identified-elements-agree`).
-- Under extensionality for families over positions, unrolling is an
-- isomorphism (`unrolling`, by Arguments' `make-unroll` and
-- `unroll-make`). It acts on identifications by an isomorphism (SPT's
-- `ap-is-isomorphism`), so identifications of generated elements are
-- exactly agreements of their source arguments
-- (`generated-identifications`).

module _
  {s κ j : Level} {E : Set j} {γ : Desc {s = s} E} (M : Algebra κ γ)
  where

  unrolling :
    Extensionality s κ
    → Generated.G M ≅ Shape γ (indexed (Generated.G M) (Generated.t M))
  unrolling extensionality = record
    { forward = Arguments.unroll M
    ; backward = Generated.make M
    ; backward-forward = Arguments.make-unroll M extensionality
    ; forward-backward = Arguments.unroll-make M
    }

  identified-elements-agree :
    (g h : Generated.G M) → g ＝ h
    → Agreement γ (indexed (Generated.G M) (Generated.t M))
        ( Arguments.unroll M g)
        ( Arguments.unroll M h)
  identified-elements-agree g h e =
    forward
      ( identifications-are-agreements γ
          ( indexed (Generated.G M) (Generated.t M))
          ( Arguments.unroll M g)
          ( Arguments.unroll M h))
      ( ap (Arguments.unroll M) e)

  generated-identifications :
    Extensionality s κ → (g h : Generated.G M)
    → (g ＝ h)
      ≅ Agreement γ (indexed (Generated.G M) (Generated.t M))
          ( Arguments.unroll M g)
          ( Arguments.unroll M h)
  generated-identifications extensionality g h =
    ≅-trans
      ( ap-is-isomorphism (unrolling extensionality) g h)
      ( identifications-are-agreements γ
          ( indexed (Generated.G M) (Generated.t M))
          ( Arguments.unroll M g)
          ( Arguments.unroll M h))
