{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Signature.Relabeling where

-- Relabelings of signatures over one judgment type: the minimal data that
-- changes the operation labels of a tree while keeping its exact dependent
-- child geometry (`Signature-Relabeling`):
--
--   operation-map : Operation Σ j → Operation Ω j,
--   target-position-projection : Position Ω (operation-map o) → Position Σ o,
--   boundary-coherence : ∂Σ o (project p) ＝ ∂Ω (operation-map o) p.
--
-- A relabeling replaces each source operation and reads every target child
-- through its source position. The projection is contravariant, since a
-- target node needs a source child at every target position, and boundary
-- coherence supplies exactly the transport of that child's judgment. No
-- injectivity, forward position map or inverse law is asserted; an exact
-- translation (Signature.Translation) has both position maps.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Signature.Sum using
  (Signature-Over; Operation; Position; position-boundary)

------------------------------------------------------------------------
-- Relabelings over one judgment type

record Signature-Relabeling {ℓj ℓo₁ ℓp₁ ℓo₂ ℓp₂ : Level} {J : Set ℓj}
  (source : Signature-Over J ℓo₁ ℓp₁) (target : Signature-Over J ℓo₂ ℓp₂)
  : Set (lsuc (ℓj ⊔ ℓo₁ ⊔ ℓp₁ ⊔ ℓo₂ ⊔ ℓp₂)) where
  field
    operation-map : {j : J} → Operation source j → Operation target j
    target-position-projection : {j : J} (o : Operation source j) →
      Position target (operation-map o) → Position source o
    boundary-coherence : {j : J} (o : Operation source j)
      (p : Position target (operation-map o)) →
      position-boundary source o (target-position-projection o p) ＝
        position-boundary target (operation-map o) p

open Signature-Relabeling public
