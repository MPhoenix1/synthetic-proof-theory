{-# OPTIONS --safe --without-K #-}

module SPT.OrdinalGeometry.Height.Relabeling where

-- Heights keep their shape under relabeling. A label map from L to L′ with
-- the positions of each image read back as those of its label is a
-- relabeling of branching signatures, every boundary being the one
-- judgment (`branching-relabeling`, a Foundation.Signature.Relabeling).
-- Its tree action (Foundation.Tree.Relabeling.relabel-tree) sends closed
-- trees over (L , R) to closed trees over (L′ , R′) with the same branching
-- (`relabel`). When the read-back has a section, the simulation order is
-- kept (`relabel-⊑`, `relabel-⊏`, `relabel-∼`):
--
--   relabel (node a f) = node (label a) (λ y′. relabel (f (back a y′))),
--   back a (forth a y) ＝ y   ⊢   x ⊑ y → relabel x ⊑ relabel y.
--
-- Height.Ordinals reads its lift of a height one level up and its reading of
-- a tree over decoded labels as relabelings (`lift-height`, `decoded`).

open import SPT.Base
import SPT.Foundation.Tree as Tree
import SPT.Foundation.Tree.W as TreeW
open import SPT.Foundation.Signature.Sum using (from-signature)
open import SPT.Foundation.Signature.Relabeling using (Signature-Relabeling)
open import SPT.Foundation.Tree.Relabeling using (relabel-tree)
open import SPT.OrdinalGeometry.Height.Simulation using
  (Closed; _⊑_; _⊏_; _∼_; below; under)

------------------------------------------------------------------------
-- Relabelings of branching signatures

module _ {ℓa ℓb ℓa′ ℓb′ : Level} {L : Set ℓa} {R : L → Set ℓb}
  {L′ : Set ℓa′} {R′ : L′ → Set ℓb′}
  where

  -- Labels go forward, the positions of an image are read back as those of
  -- its label, and every boundary is the one judgment.
  branching-relabeling : (label : L → L′)
    (back : (a : L) → R′ (label a) → R a) →
    Signature-Relabeling (from-signature (TreeW.Branching.signature L R))
      (from-signature (TreeW.Branching.signature L′ R′))
  branching-relabeling label back = record
    { operation-map = label
    ; target-position-projection = back
    ; boundary-coherence = λ o p → refl
    }

------------------------------------------------------------------------
-- The simulation order along a relabeling

module _ {ℓa ℓb ℓa′ ℓb′ : Level} {L : Set ℓa} {R : L → Set ℓb}
  {L′ : Set ℓa′} {R′ : L′ → Set ℓb′} (label : L → L′)
  (back : (a : L) → R′ (label a) → R a)
  where

  -- Mathematical shape:
  -- relabel (node a f) = node (label a) (λ y′. relabel (f (back a y′))).
  relabel : Closed L R → Closed L′ R′
  relabel = relabel-tree (branching-relabeling label back)

  module _ (forth : (a : L) → R a → R′ (label a))
    (back-forth : (a : L) (y : R a) → back a (forth a y) ＝ y)
    where

    -- A child below a node goes under the image of its position, which
    -- reads back to it.
    mutual
      relabel-⊑ : {x y : Closed L R} → x ⊑ y → relabel x ⊑ relabel y
      relabel-⊑ (below {a} {f} {t} p) =
        below (λ y′ → relabel-⊏ (p (back a y′)))

      relabel-⊏ : {x y : Closed L R} → x ⊏ y → relabel x ⊏ relabel y
      relabel-⊏ (under {x} {b} {h} z p) =
        under (forth b z)
          (transport (λ w → relabel x ⊑ relabel (h w))
            (back-forth b z ⁻¹) (relabel-⊑ p))

    relabel-∼ : {x y : Closed L R} → x ∼ y → relabel x ∼ relabel y
    relabel-∼ e = relabel-⊑ (pr₁ e) , relabel-⊑ (pr₂ e)
