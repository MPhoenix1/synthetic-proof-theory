{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Impredicative.Classifier.Discriminator where

-- Recovery is the content of a power presentation. The power type of every
-- small type has a lawless small weak presentation, by the unit type with
-- the empty predicate as its return (`lawless-presentation`), and at an
-- inhabited type its maps admit no recovery law
-- (`lawless-presentation-is-unrecoverable`). So a weak presentation of the
-- power type is no power presentation: the `recover` field of Classifier's
-- `Power-Presentation` carries the strength.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Impredicative.WeakResizing using
  (Weak-Presentation)

module _ {ℓ : Level} (A : Set ℓ) where

  lawless-presentation : Weak-Presentation ℓ (A → Set ℓ)
  lawless-presentation =
    Lift ℓ 𝟙 ,
    (λ (u : Lift ℓ 𝟙) (a : A) → Lift ℓ 𝟘) ,
    (λ (X : A → Set ℓ) → lift ⋆)

  -- Recovery at the full predicate would return a point of the empty one.
  lawless-presentation-is-unrecoverable : A →
    ( (X : A → Set ℓ) (a : A) →
      ( X a →
        pr₁ (pr₂ lawless-presentation) (pr₂ (pr₂ lawless-presentation) X) a) ×
      ( pr₁ (pr₂ lawless-presentation) (pr₂ (pr₂ lawless-presentation) X) a →
        X a)) →
    𝟘
  lawless-presentation-is-unrecoverable a recover =
    lower (pr₁ (recover (λ (b : A) → Lift ℓ 𝟙) a) (lift ⋆))
