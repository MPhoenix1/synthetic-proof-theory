{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.HalfAdjoint.Extension where

-- A section given on the image of an isomorphism E : A ≅ B extends to the
-- whole codomain, transported along the coherent inverse law
-- (`extension`), and on the image it is the given section (`extension-β`),
-- by the half-adjoint condition and dependent application:
--
--   extension E F f b = transport F (coherent-forward-backward E b)
--                         (f (backward E b)),
--   extension E F f (forward E a) ＝ f a.
--
-- A predicate L on the fibers of F that holds of f at the images holds of
-- the extension at every point, by dependent transport along the same law
-- (`extension-preserves-predicates`, Identifications.Dependent):
--
--   ((a : A) → L (forward E a) (f a)) → (b : B) → L b (extension E F f b).
--
-- So a method given at the images of an isomorphism of arguments is a
-- method at every argument, computing as given at the images, and a law
-- it satisfies at the images holds of it at every argument.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.HalfAdjoint using
  (coherent-forward-backward; half-adjoint-condition)
open import SPT.Cubical.Foundation.Isomorphisms using
  (_≅_; forward; backward; backward-forward)

module _
  {α β ν : Level} {A : Set α} {B : Set β} (E : A ≅ B) (F : B → Set ν)
  (f : (a : A) → F (forward E a))
  where

  extension : (b : B) → F b
  extension b =
    transport F (coherent-forward-backward E b) (f (backward E b))

  extension-β : (a : A) → extension (forward E a) ＝ f a
  extension-β a =
    ap (λ c → transport F c (f (backward E (forward E a))))
      (half-adjoint-condition E a ⁻¹)
    ∙ ( transport-ap F (forward E) (backward-forward E a)
          (f (backward E (forward E a)))
        ⁻¹
      ∙ apd f (backward-forward E a))

-- A predicate on the fibers holds of the extension wherever it holds of
-- the given section at the images.

module _
  {α β ν ρ : Level} {A : Set α} {B : Set β} (E : A ≅ B) (F : B → Set ν)
  (f : (a : A) → F (forward E a)) (L : (b : B) → F b → Set ρ)
  where

  extension-preserves-predicates :
    ((a : A) → L (forward E a) (f a)) → (b : B) → L b (extension E F f b)
  extension-preserves-predicates l b =
    dependent-transport F L (coherent-forward-backward E b) (f (backward E b))
      (l (backward E b))
