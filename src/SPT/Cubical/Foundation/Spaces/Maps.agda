{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Spaces.Maps where

-- Points and maps of displayed spaces (Foundation.Spaces).
--
-- * A total point keeps a base point and an inhabitant of its exact fiber
--   (`total-point`, `project-base`, `project-fiber`, with their
--   computation laws by refl).
-- * A total map may read the fiber to choose the target base
--   (`Total-Map`, `apply-total-map`); total maps agree pointwise
--   (`Total-Map-Pointwise-Cell`), may be identified under extensionality
--   (`Total-Map-Extensionality`) and compose (`compose-total-map`).
-- * A split map fixes the target base from the source base alone
--   (`Split-Map`, fields `on-base`, `on-fiber`), and is a total map
--   (`split-to-total`); split maps compose, and the total map of the
--   composite agrees pointwise with the composite of the total maps
--   (`compose-split-map`, `split-to-total-compose-split-map`).

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Spaces using (DΣ; Base; Fiber; Total)

------------------------------------------------------------------------
-- Total points

-- A total point binds the determining base before its dependent inhabitant;
-- neither component is reconstructed from the other, and `project-base` has
-- no section in general.

module _ {ℓb ℓf : Level} (X : DΣ ℓb ℓf) where

  total-point : (j : Base X) → Fiber X j → Total X
  total-point j x = j , x

  project-base : Total X → Base X
  project-base = pr₁

  project-fiber : (p : Total X) → Fiber X (project-base p)
  project-fiber = pr₂

  project-base-total-point : (j : Base X) (x : Fiber X j) →
    project-base (total-point j x) ＝ j
  project-base-total-point j x = refl

  project-fiber-total-point : (j : Base X) (x : Fiber X j) →
    project-fiber (total-point j x) ＝ x
  project-fiber-total-point j x = refl

  total-point-project : (p : Total X) →
    total-point (project-base p) (project-fiber p) ＝ p
  total-point-project (j , x) = refl


------------------------------------------------------------------------
-- Total maps

-- A total map may inspect the complete source point, fiber included, before
-- it chooses the target base. A total map need not admit a split
-- presentation.

Total-Map : {ℓb₁ ℓf₁ ℓb₂ ℓf₂ : Level} → DΣ ℓb₁ ℓf₁ → DΣ ℓb₂ ℓf₂ →
  Set (ℓb₁ ⊔ ℓf₁ ⊔ ℓb₂ ⊔ ℓf₂)
Total-Map X Y = (j : Base X) → Fiber X j → Total Y

module _ {ℓb₁ ℓf₁ ℓb₂ ℓf₂ : Level} (X : DΣ ℓb₁ ℓf₁) (Y : DΣ ℓb₂ ℓf₂) where

  apply-total-map : Total-Map X Y → Total X → Total Y
  apply-total-map f (j , x) = f j x

  apply-total-map-total-point : (f : Total-Map X Y) (j : Base X)
    (x : Fiber X j) → apply-total-map f (total-point X j x) ＝ f j x
  apply-total-map-total-point f j x = refl

  -- Each complete source point carries its own alignment of the two complete
  -- target points; the two maps remain distinct data.

  Total-Map-Pointwise-Cell : Total-Map X Y → Total-Map X Y →
    Set (ℓb₁ ⊔ ℓf₁ ⊔ ℓb₂ ⊔ ℓf₂)
  Total-Map-Pointwise-Cell f g =
    (p : Total X) → apply-total-map f p ＝ apply-total-map g p

  reflexive-total-map-pointwise-cell : (f : Total-Map X Y) →
    Total-Map-Pointwise-Cell f f
  reflexive-total-map-pointwise-cell f p = refl

  -- Extensionality for one space of total maps, as a hypothesis: a pointwise
  -- cell gives an identification of the two curried maps.

  Total-Map-Extensionality : Set (ℓb₁ ⊔ ℓf₁ ⊔ ℓb₂ ⊔ ℓf₂)
  Total-Map-Extensionality =
    (f g : Total-Map X Y) → Total-Map-Pointwise-Cell f g → f ＝ g

-- The complete total point returned by the first map is supplied literally
-- to the second; neither component is rerun or reconstructed.

module _ {ℓb₀ ℓf₀ ℓb₁ ℓf₁ ℓb₂ ℓf₂ : Level} (X : DΣ ℓb₀ ℓf₀)
  (Y : DΣ ℓb₁ ℓf₁) (Z : DΣ ℓb₂ ℓf₂) where

  compose-total-map : Total-Map Y Z → Total-Map X Y → Total-Map X Z
  compose-total-map g f j x = apply-total-map Y Z g (f j x)

  apply-total-map-compose-total-map : (g : Total-Map Y Z)
    (f : Total-Map X Y) (p : Total X) →
    apply-total-map X Z (compose-total-map g f) p
      ＝ apply-total-map Y Z g (apply-total-map X Y f p)
  apply-total-map-compose-total-map g f (j , x) = refl

------------------------------------------------------------------------
-- Split maps

-- The target base is fixed from the source base before the source fiber
-- inhabitant is inspected; the target fiber inhabitant lies over the literal
-- `on-base` image. Not every total map is in the image of `split-to-total`.

record Split-Map {ℓb₁ ℓf₁ ℓb₂ ℓf₂ : Level} (X : DΣ ℓb₁ ℓf₁)
  (Y : DΣ ℓb₂ ℓf₂) : Set (ℓb₁ ⊔ ℓf₁ ⊔ ℓb₂ ⊔ ℓf₂) where
  field
    on-base : Base X → Base Y
    on-fiber : (j : Base X) → Fiber X j → Fiber Y (on-base j)

open Split-Map public

module _ {ℓb₁ ℓf₁ ℓb₂ ℓf₂ : Level} {X : DΣ ℓb₁ ℓf₁} {Y : DΣ ℓb₂ ℓf₂} where

  split-to-total : Split-Map X Y → Total-Map X Y
  split-to-total F j x = on-base F j , on-fiber F j x

  split-to-total-on-base : (F : Split-Map X Y) (j : Base X)
    (x : Fiber X j) → project-base Y (split-to-total F j x) ＝ on-base F j
  split-to-total-on-base F j x = refl

  split-to-total-on-fiber : (F : Split-Map X Y) (j : Base X)
    (x : Fiber X j) →
    project-fiber Y (split-to-total F j x) ＝ on-fiber F j x
  split-to-total-on-fiber F j x = refl

-- The second base map receives the literal base selected by the first, and
-- the second fiber action the literal fiber inhabitant over it.

module _ {ℓb₀ ℓf₀ ℓb₁ ℓf₁ ℓb₂ ℓf₂ : Level} {X : DΣ ℓb₀ ℓf₀}
  {Y : DΣ ℓb₁ ℓf₁} {Z : DΣ ℓb₂ ℓf₂} where

  compose-split-map : Split-Map Y Z → Split-Map X Y → Split-Map X Z
  compose-split-map G F = record
    { on-base = λ j → on-base G (on-base F j)
    ; on-fiber = λ j x → on-fiber G (on-base F j) (on-fiber F j x)
    }

  split-to-total-compose-split-map : (G : Split-Map Y Z) (F : Split-Map X Y)
    (p : Total X) →
    apply-total-map X Z (split-to-total (compose-split-map G F)) p
      ＝ apply-total-map X Z
        (compose-total-map X Y Z (split-to-total G) (split-to-total F)) p
  split-to-total-compose-split-map G F (j , x) = refl

  -- Under extensionality for the one space of total maps concerned, passed
  -- explicitly, the pointwise computation above gives an identification of
  -- the two maps. The pointwise statement stays available without it.

  split-to-total-compose-split-map-identification :
    Total-Map-Extensionality X Z →
    (G : Split-Map Y Z) (F : Split-Map X Y) →
    split-to-total (compose-split-map G F)
      ＝ compose-total-map X Y Z (split-to-total G) (split-to-total F)
  split-to-total-compose-split-map-identification extensionality G F =
    extensionality
      (split-to-total (compose-split-map G F))
      (compose-total-map X Y Z (split-to-total G) (split-to-total F))
      (split-to-total-compose-split-map G F)
