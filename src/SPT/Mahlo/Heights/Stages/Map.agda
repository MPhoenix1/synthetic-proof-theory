{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Heights.Stages.Map where

-- Codes along a map of universes that keeps decodings. For universes
-- (U , T) and (U′ , T′) and a map h : U → U′ with T′ (h a) ＝ T a, each
-- code of one layer over (U , T) (Heights.Stages' `Code`) goes to the same
-- former at the images of its codes (`code-map`), with the same decoding,
-- under extensionality for families of types (`code-map-β`):
--
--   decode (code-map c) ＝ decode c.
--
-- A family of codes and its image decode to one family of types
-- (`image-family`). So the layer of Φ's codes is functorial
-- (`codes-are-functorial`, Heights.Stages' `Functorial`), which includes
-- its stages along the simulation order.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
import SPT.Mahlo.Ambient as Ambient
open import SPT.Mahlo.DS.Realization.Family using (cast)
import SPT.Mahlo.Specification as Specification
open import SPT.Mahlo.Heights.Stages using
  ( Code; decode; codes; Functorial; family; reidentified; rebranched
  ; empty; unit; two; natural; product; sum; tree; result; identity
  ; branch )

module _ {ℓ : Level} (extensionality : (X : Set ℓ) → FunExt X (λ _ → Set ℓ))
  {U U′ : Set ℓ} (T : U → Set ℓ) (T′ : U′ → Set ℓ)
  (h : U → U′) (h-β : (a : U) → T′ (h a) ＝ T a)
  where

  -- A family of codes and its image decode to one family of types.
  image-family : (a : U) (b : T a → U) →
    _＝_ {A = Specification.Family (λ (A : Set ℓ) → A)}
      (T′ (h a) , (λ y → T′ (h (b (cast (h-β a) y)))))
      (T a , (λ x → T (b x)))
  image-family a b =
    family extensionality (h-β a) (λ y → h-β (b (cast (h-β a) y)))

  module _ (Φ : Ambient.Operator ℓ) where

    -- The image of a code: the same former at the images of its codes.
    code-map : Code Φ U T → Code Φ U′ T′
    code-map empty = empty
    code-map unit = unit
    code-map two = two
    code-map natural = natural
    code-map (product a b) = product (h a) (λ y → h (b (cast (h-β a) y)))
    code-map (sum a b) = sum (h a) (λ y → h (b (cast (h-β a) y)))
    code-map (tree a b) = tree (h a) (λ y → h (b (cast (h-β a) y)))
    code-map (result a b) = result (h a) (λ y → h (b (cast (h-β a) y)))
    code-map (identity a x y) =
      identity (h a) (cast (h-β a ⁻¹) x) (cast (h-β a ⁻¹) y)
    code-map (branch a b i) =
      branch (h a) (λ y → h (b (cast (h-β a) y)))
        (cast (ap (λ F → pr₁ (Φ F)) (image-family a b ⁻¹)) i)

    -- The image of a code decodes to the code's decoding.
    code-map-β : (c : Code Φ U T) → decode (code-map c) ＝ decode c
    code-map-β empty = refl
    code-map-β unit = refl
    code-map-β two = refl
    code-map-β natural = refl
    code-map-β (product a b) =
      ap (Specification.Formers.product (Ambient.formers ℓ)) (image-family a b)
    code-map-β (sum a b) =
      ap (Specification.Formers.sum (Ambient.formers ℓ)) (image-family a b)
    code-map-β (tree a b) =
      ap (Specification.Formers.tree (Ambient.formers ℓ)) (image-family a b)
    code-map-β (result a b) = ap (λ F → pr₁ (Φ F)) (image-family a b)
    code-map-β (identity a x y) = reidentified (h-β a) x y
    code-map-β (branch a b i) = rebranched Φ (image-family a b) i

------------------------------------------------------------------------
-- The layer of Φ's codes is functorial

codes-are-functorial : {ℓ : Level}
  (extensionality : (X : Set ℓ) → FunExt X (λ _ → Set ℓ))
  (Φ : Ambient.Operator ℓ) → Functorial (codes Φ)
codes-are-functorial extensionality Φ = record
  { move = λ T T′ h h-β → code-map extensionality T T′ h h-β Φ
  ; move-β = λ T T′ h h-β → code-map-β extensionality T T′ h h-β Φ
  }
