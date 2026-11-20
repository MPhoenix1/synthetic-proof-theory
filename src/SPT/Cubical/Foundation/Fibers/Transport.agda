{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Fibers.Transport where

-- Transport in the family of fibers of a map changes only the identification:
-- the point of the fiber is kept (`first-of-transport`).

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Fibers using (fiber)

module _ {ℓ κ : Level} {A : Set ℓ} {B : Set κ} (f : A → B) where

  first-of-transport : {b b′ : B} (p : b ＝ b′) (w : fiber f b) →
    pr₁ (transport (fiber f) p w) ＝ pr₁ w
  first-of-transport refl w = refl
