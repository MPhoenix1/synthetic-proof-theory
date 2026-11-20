{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Impredicative.SmallIdentifications.Cayley where

-- Cayley's embedding under small identifications: a group of level ℓ + 1
-- acts faithfully on its elements by left multiplication, so under
-- univalence at ℓ + 1 its elements form a small type
-- (`elements-of-groups-are-small`). Transporting the multiplication along
-- that equivalence, which is not done here, gives an isomorphic group of
-- level ℓ; so a group of level ℓ + 1 isomorphic to no group of level ℓ, such
-- as the free group on the ordinals of level ℓ (Bezem, Coquand, Dybjer and
-- Escardó, TypeTopology's Ordinals.BuraliForti, `there-is-a-large-group`),
-- refutes small identifications.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Groups using
  (Group; Elements; left-multiplication; left-multiplication-at-the-unit)
open import SPT.Cubical.Foundation.Impredicative.SmallIdentifications using
  (Small-Identifications; faithfully-represented-types-are-small)
open import SPT.Cubical.Foundation.Size using (is-small)
open import SPT.Cubical.Foundation.Univalence using
  (is-univalent; funext-from-univalence)

------------------------------------------------------------------------
-- Groups of the next level are small

-- Left multiplications that agree at the unit are left multiplications by
-- one element, since g · 1 ＝ g.

module _ {ℓ : Level} (u₁ : is-univalent (lsuc ℓ))
  (s : Small-Identifications ℓ) (G : Group (lsuc ℓ)) where

  elements-of-groups-are-small : is-small ℓ (Elements G)
  elements-of-groups-are-small =
    faithfully-represented-types-are-small
      (λ X Y → funext-from-univalence X Y u₁ u₁) u₁ s
      (Elements G) (Group.elements-form-a-set G) (left-multiplication G)
      (λ g h agree →
        left-multiplication-at-the-unit G g ⁻¹
        ∙ agree (Group.unit G)
        ∙ left-multiplication-at-the-unit G h)
