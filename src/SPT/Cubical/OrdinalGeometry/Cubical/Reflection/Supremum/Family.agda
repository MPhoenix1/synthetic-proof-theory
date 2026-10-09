{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Supremum.Family
  where

-- Suprema of small families of well-orders: the cubical library's
-- quotient (Σ i. |F i|)/∼ of HoTT book Lemma 10.3.22, sealed.  It bounds
-- every member (upper), it is least among well-orders of the members'
-- level (least), and each of its principal segments is, merely, a
-- principal segment of a member (covered), so each of its points is the
-- image of a point of a member (upper-surjective).  For a family G, the
-- supremum of the successors G i + 1 lies strictly above every G i
-- (strict-upper), and below every well-order, of any level, that lies
-- strictly above every G i (strict-least).

open import Agda.Primitive using (Level; _⊔_)

import Cubical.Data.Sum as Sum
import Cubical.Foundations.Equiv as Equiv
import Cubical.Functions.Embedding as Embedding
open Sum using (_⊎_; inl; inr)
import Cubical.Foundations.Prelude as Cubical
import Cubical.HITs.PropositionalTruncation as Truncation
import Cubical.HITs.SetQuotients as Quotient
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Ordinals using
  (successor; successor-strict; successor-segments; segments→simulation)

private
  variable
    ℓ ℓ′ c d : Level

-- Mathematical shape:
--
--   sup F : Woset(ℓ′ ⊔ ℓ, ℓ),
--   F i ≼ sup F,
--   (∀ i. F i ≼ W) → sup F ≼ W   for W : Woset(ℓ, ℓ).
abstract
  supremum : {I : Set ℓ′} (F : I → Woset.Woset ℓ ℓ) → Woset.Woset (ℓ′ ⊔ ℓ) ℓ
  supremum F = Cubical.fst (Simulation.sup F)

  upper : {I : Set ℓ′} (F : I → Woset.Woset ℓ ℓ) (i : I)
    → Simulation._≼_ (F i) (supremum F)
  upper F = Cubical.fst (Cubical.snd (Simulation.sup F))

  least : {I : Set ℓ′} (F : I → Woset.Woset ℓ ℓ) (W : Woset.Woset ℓ ℓ)
    → ((i : I) → Simulation._≼_ (F i) W)
    → Simulation._≼_ (supremum F) W
  least F = Cubical.snd (Cubical.snd (Simulation.sup F))

  -- Every principal segment of sup F is a principal segment of a member:
  -- a point of the quotient is merely the class of a point x of some F i,
  -- and the upper map of F i carries the segment below x.
  covered : {I : Set ℓ′} (F : I → Woset.Woset ℓ ℓ)
    (point : Cubical.fst (supremum F))
    → Truncation.∥
        Cubical.Σ I (λ i →
          Cubical.Σ (Cubical.fst (F i)) λ x →
            Woset.WosetEquiv
              (Simulation._↓_ (supremum F) point)
              (Simulation._↓_ (F i) x))
      ∥₁
  covered F point =
    Truncation.map
      (λ represented →
        let i = Cubical.fst (Cubical.fst represented)
            x = Cubical.snd (Cubical.fst represented)
            strict =
              Simulation.≺Trans≼
                (Simulation._↓_ (F i) x)
                (F i)
                (supremum F)
                (Simulation.↓Decreasing (F i) x)
                (upper F i)
        in
        Cubical._,_ i
          (Cubical._,_ x
            (Cubical.subst
              (λ bound →
                Woset.WosetEquiv
                  (Simulation._↓_ (supremum F) bound)
                  (Simulation._↓_ (F i) x))
              (Cubical.snd represented)
              (Cubical.snd strict))))
      (Quotient.[]surjective point)

-- Every point of sup F is, merely, the image of a point of a member: it
-- has the principal segment of such a point (covered), as that point's
-- image does, and ↓ is an embedding.
upper-surjective : {I : Set ℓ′} (F : I → Woset.Woset ℓ ℓ)
  (point : Cubical.fst (supremum F))
  → Truncation.∥
      Cubical.Σ I (λ i →
        Cubical.Σ (Cubical.fst (F i)) λ x →
          Cubical.fst (upper F i) x Cubical.≡ point)
    ∥₁
upper-surjective F point =
  Truncation.map
    (λ represented →
      let i = Cubical.fst represented
          x = Cubical.fst (Cubical.snd represented)
          image =
            Simulation.≺Trans≼ (Simulation._↓_ (F i) x) (F i)
              (supremum F) (Simulation.↓Decreasing (F i) x) (upper F i)
      in
      Cubical._,_ i
        (Cubical._,_ x
          (Embedding.isEmbedding→Inj (Simulation.isEmbedding↓ (supremum F))
            (Cubical.fst (upper F i) x) point
            (Equiv.equivFun (Woset.WosetPath _ _)
              (Woset.compWosetEquiv (Cubical.snd image)
                (Woset.invWosetEquiv
                  (Cubical.snd (Cubical.snd represented))))))))
    (covered F point)

------------------------------------------------------------------------
-- Suprema of successors

-- Mathematical shape: G i ≺ sup_j (G j + 1).
strict-upper : {I : Set ℓ′} (G : I → Woset.Woset ℓ ℓ) (i : I)
  → Simulation._≺_ (G i) (supremum (λ j → successor (G j)))
strict-upper G i =
  Simulation.≺Trans≼ (G i) (successor (G i))
    (supremum (λ j → successor (G j)))
    (successor-strict (G i))
    (upper (λ j → successor (G j)) i)

private
  -- A principal segment of the supremum that is G i + 1 or one of its
  -- segments lies below every strict upper bound B of G i.
  segment-below : {I : Set ℓ′} (G : I → Woset.Woset ℓ ℓ)
    (B : Woset.Woset c d) (i : I) → Simulation._≺_ (G i) B
    → (X : Woset.Woset (ℓ′ ⊔ ℓ) ℓ) (z : Cubical.fst (successor (G i)))
    → Woset.WosetEquiv X (Simulation._↓_ (successor (G i)) z)
    → Woset.WosetEquiv (Simulation._↓_ (successor (G i)) z) (G i)
      ⊎ Cubical.Σ (Cubical.fst (G i)) (λ x →
          Woset.WosetEquiv (Simulation._↓_ (successor (G i)) z)
            (Simulation._↓_ (G i) x))
    → Simulation._≺_ X B
  segment-below G B i strict X z e (inl e′) =
    Simulation.≺RespectsEquivL B
      (Woset.invWosetEquiv (Woset.compWosetEquiv e e′))
      strict
  segment-below G B i strict X z e (inr (Cubical._,_ x e′)) =
    Simulation.≺RespectsEquivL B
      (Woset.invWosetEquiv (Woset.compWosetEquiv e e′))
      (Simulation.isTrans≺ (Simulation._↓_ (G i) x) (G i) B
        (Simulation.↓Decreasing (G i) x) strict)

-- Mathematical shape: (∀ i. G i ≺ B) → sup_i (G i + 1) ≼ B, for B of any
-- level: every principal segment of the supremum is G i or one of its
-- segments, and these lie below B.
strict-least : {I : Set ℓ′} (G : I → Woset.Woset ℓ ℓ)
  (B : Woset.Woset c d)
  → ((i : I) → Simulation._≺_ (G i) B)
  → Simulation._≼_ (supremum (λ i → successor (G i))) B
strict-least G B below =
  segments→simulation {H = supremum (λ i → successor (G i))} {K = B}
    λ point →
      Truncation.rec
        (Simulation.isPropValued≺
          (Simulation._↓_ (supremum (λ i → successor (G i))) point) B)
        (λ represented →
          let i = Cubical.fst represented
              z = Cubical.fst (Cubical.snd represented)
          in
          segment-below G B i (below i)
            (Simulation._↓_ (supremum (λ i → successor (G i))) point) z
            (Cubical.snd (Cubical.snd represented))
            (successor-segments (G i) z))
        (covered (λ i → successor (G i)) point)
