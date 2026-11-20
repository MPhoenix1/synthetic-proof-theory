{-# OPTIONS --safe --without-K #-}

module SPT.Incidence.Boundary.Base where

-- Boundary spaces over a fixed ambient displayed space U: a displayed space
-- X of boundaries and fillers with a total map realizing each filled cell as
-- a complete point of U,
--
--   realization : Π (b : Base X). Fiber X b → Σ (a : Base U). Fiber U a.
--
-- * Boundaries, fillers and filled cells are the base, the fibers and the
--   total points of `space X`, written so, with no second names.
-- * A split realization fixes the ambient base from the boundary before the
--   filler is read (`Is-Split`; `present-split` is split by
--   `present-split-is-split`).
-- * `𝒰 ℓ` is the displayed space of small types and one inhabitant.
-- * Base change along q : B → Base U is the pullback of the fibers of U
--   along q (`base-change`); postcomposition with a total map U → V changes
--   only the realized point (`postcompose`).
-- * A family R over Total U is the split boundary space with boundaries the
--   complete ambient points and realization forgetting the filler
--   (`family-boundary-space`); fiberwise isomorphisms R u ≅ Q u give an
--   isomorphism of filled cells that keeps the boundary and commutes with
--   realization by refl (`family-filled-cell-isomorphism`).
--
-- No section, reconstruction, uniqueness or generated incidence is asserted.

open import SPT.Base
open import SPT.Foundation.Isomorphisms using (_≅_; forward; backward)
open import SPT.Foundation.Spaces using (DΣ; Base; Fiber; Total)
open import SPT.Foundation.Spaces.Maps using
  ( project-base; project-fiber; Total-Map; Total-Map-Pointwise-Cell
  ; apply-total-map; compose-total-map; Split-Map; on-base; on-fiber
  ; split-to-total
  )
open import SPT.Foundation.Spaces.Vertical using
  (family-displayed-space; fiberwise-total-isomorphism)
open import SPT.Incidence.Displayed.Graph using (pullback-space)

------------------------------------------------------------------------
-- Boundary spaces over a fixed ambient space

-- The complete filled cell may determine both components of its realized
-- point. Sections, reconstruction, uniqueness and generated incidence are
-- separate.

record ∂-Space {ℓb ℓf : Level} (U : DΣ ℓb ℓf) (ℓ∂ ℓ∂′ : Level)
  : Set (lsuc (ℓb ⊔ ℓf ⊔ ℓ∂ ⊔ ℓ∂′)) where
  constructor present
  field
    space : DΣ ℓ∂ ℓ∂′
    realization : Total-Map space U

open ∂-Space public

------------------------------------------------------------------------
-- The displayed space of small types

-- A total point is one small type together with one inhabitant of that
-- type. This is an ambient displayed space, not a generated boundary space,
-- a small classifier or a closure theorem; no displayed space is claimed to
-- be a universe.

𝒰 : (ℓ : Level) → DΣ (lsuc ℓ) ℓ
𝒰 ℓ = record
  { Base = Set ℓ
  ; Fiber = λ A → A
  }

------------------------------------------------------------------------
-- Presentation and realization

module _ {ℓb ℓf ℓ∂ ℓ∂′ : Level} (U : DΣ ℓb ℓf) where

  space-β : (X : DΣ ℓ∂ ℓ∂′) (r : Total-Map X U) → space (present X r) ＝ X
  space-β X r = refl

  realization-β : (X : DΣ ℓ∂ ℓ∂′) (r : Total-Map X U) →
    realization (present X r) ＝ r
  realization-β X r = refl

module _ {ℓb ℓf ℓ∂ ℓ∂′ : Level} {U : DΣ ℓb ℓf} where

  present-split : (X : DΣ ℓ∂ ℓ∂′) → Split-Map X U → ∂-Space U ℓ∂ ℓ∂′
  present-split X q = present X (split-to-total q)

  present-split-space-β : (X : DΣ ℓ∂ ℓ∂′) (q : Split-Map X U) →
    space (present-split X q) ＝ X
  present-split-space-β X q = refl

  present-split-realization-β : (X : DΣ ℓ∂ ℓ∂′) (q : Split-Map X U) →
    realization (present-split X q) ＝ split-to-total q
  present-split-realization-β X q = refl

  realize : (X : ∂-Space U ℓ∂ ℓ∂′) → Total (space X) → Total U
  realize X = apply-total-map (space X) U (realization X)

  realize-β : (X : ∂-Space U ℓ∂ ℓ∂′) (b : Base (space X))
    (f : Fiber (space X) b) → realize X (b , f) ＝ realization X b f
  realize-β X b f = refl

  realize-base-β : (X : ∂-Space U ℓ∂ ℓ∂′) (b : Base (space X))
    (f : Fiber (space X) b) →
    project-base U (realize X (b , f))
      ＝ project-base U (realization X b f)
  realize-base-β X b f = refl

  realize-fiber-β : (X : ∂-Space U ℓ∂ ℓ∂′) (b : Base (space X))
    (f : Fiber (space X) b) →
    project-fiber U (realize X (b , f))
      ＝ project-fiber U (realization X b f)
  realize-fiber-β X b f = refl

------------------------------------------------------------------------
-- Split realizations

-- The pointwise agreement keeps the split presentation without an
-- identification of maps. A boundary space need not admit this stronger
-- witness.

record Is-Split {ℓb ℓf ℓ∂ ℓ∂′ : Level} {U : DΣ ℓb ℓf}
  (X : ∂-Space U ℓ∂ ℓ∂′) : Set (ℓb ⊔ ℓf ⊔ ℓ∂ ⊔ ℓ∂′) where
  constructor split-witness
  field
    splitting : Split-Map (space X) U
    split-agrees :
      Total-Map-Pointwise-Cell (space X) U (realization X)
        (split-to-total splitting)

open Is-Split public

module _ {ℓb ℓf ℓ∂ ℓ∂′ : Level} {U : DΣ ℓb ℓf} where

  present-split-is-split : (X : DΣ ℓ∂ ℓ∂′) (q : Split-Map X U) →
    Is-Split (present-split X q)
  present-split-is-split X q = record
    { splitting = q
    ; split-agrees = λ cell → refl
    }

  split-realize-β : (X : ∂-Space U ℓ∂ ℓ∂′) (split : Is-Split X)
    (b : Base (space X)) (f : Fiber (space X) b) →
    realize X (b , f)
      ＝ (on-base (splitting split) b , on-fiber (splitting split) b f)
  split-realize-β X split b f = split-agrees split (b , f)

------------------------------------------------------------------------
-- Base change

-- Along q : B → Base U the boundaries are the points of B, the fillers over
-- b the fiber of U over q b, and the realization is (b , f) ↦ (q b , f).
-- Base change does not characterize every boundary space.

module _ {ℓb ℓf ℓ∂ : Level} (U : DΣ ℓb ℓf) (B : Set ℓ∂) (q : B → Base U)
  where

  base-change : ∂-Space U ℓ∂ ℓf
  base-change = present-split (pullback-space (Fiber U) q)
    (record
      { on-base = q
      ; on-fiber = λ b f → f
      })

  base-change-base : Base (space base-change) ＝ B
  base-change-base = refl

  base-change-fiber : (b : B) → Fiber (space base-change) b ＝ Fiber U (q b)
  base-change-fiber b = refl

  base-change-β : (b : B) (f : Fiber U (q b)) →
    realize base-change (b , f) ＝ (q b , f)
  base-change-β b f = refl

------------------------------------------------------------------------
-- Realization into another ambient space

-- Postcomposition keeps the exact boundary and filler family; only the
-- realized point changes, through the supplied total map.

module _ {ℓu ℓu′ ℓv ℓv′ ℓ∂ ℓ∂′ : Level} {U : DΣ ℓu ℓu′} (V : DΣ ℓv ℓv′)
  where

  postcompose : Total-Map U V → ∂-Space U ℓ∂ ℓ∂′ → ∂-Space V ℓ∂ ℓ∂′
  postcompose r X =
    present (space X) (compose-total-map (space X) U V r (realization X))

  postcompose-space : (r : Total-Map U V) (X : ∂-Space U ℓ∂ ℓ∂′) →
    space (postcompose r X) ＝ space X
  postcompose-space r X = refl

  postcompose-β : (r : Total-Map U V) (X : ∂-Space U ℓ∂ ℓ∂′)
    (cell : Total (space X)) →
    realize (postcompose r X) cell ＝ apply-total-map U V r (realize X cell)
  postcompose-β r X (b , f) = refl

------------------------------------------------------------------------
-- Families over the ambient total space

-- The boundaries are the complete ambient points, the fillers over u are
-- R u, and the realization forgets the filler; it is split, with the two
-- projections of U as its splitting.

module _ {ℓb ℓf ℓ : Level} (U : DΣ ℓb ℓf) where

  family-boundary-splitting : (R : Total U → Set ℓ) →
    Split-Map (family-displayed-space (Total U) R) U
  family-boundary-splitting R = record
    { on-base = project-base U
    ; on-fiber = λ u r → project-fiber U u
    }

  family-boundary-space : (Total U → Set ℓ) → ∂-Space U (ℓb ⊔ ℓf) ℓ
  family-boundary-space R =
    present-split (family-displayed-space (Total U) R)
      (family-boundary-splitting R)

  family-boundary-space-is-split : (R : Total U → Set ℓ) →
    Is-Split (family-boundary-space R)
  family-boundary-space-is-split R =
    present-split-is-split (family-displayed-space (Total U) R)
      (family-boundary-splitting R)

  family-boundary-space-β : (R : Total U → Set ℓ) (u : Total U) (r : R u) →
    realize (family-boundary-space R) (u , r) ＝ u
  family-boundary-space-β R u r = refl

-- Isomorphisms of the fibers over each ambient point give an isomorphism of
-- the filled cells; the boundary is kept, and realization commutes with both
-- maps by refl.

module _ {ℓb ℓf ℓ κ : Level} (U : DΣ ℓb ℓf) {R : Total U → Set ℓ}
  {Q : Total U → Set κ} (fibers : (u : Total U) → R u ≅ Q u) where

  family-filled-cell-isomorphism :
    Total (space (family-boundary-space U R))
      ≅ Total (space (family-boundary-space U Q))
  family-filled-cell-isomorphism = fiberwise-total-isomorphism fibers

  family-filled-cell-isomorphism-forward-realize :
    (cell : Total (space (family-boundary-space U R))) →
    realize (family-boundary-space U Q)
      (forward family-filled-cell-isomorphism cell)
      ＝ realize (family-boundary-space U R) cell
  family-filled-cell-isomorphism-forward-realize (u , r) = refl

  family-filled-cell-isomorphism-backward-realize :
    (cell : Total (space (family-boundary-space U Q))) →
    realize (family-boundary-space U R)
      (backward family-filled-cell-isomorphism cell)
      ＝ realize (family-boundary-space U Q) cell
  family-filled-cell-isomorphism-backward-realize (u , s) = refl
