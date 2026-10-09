{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Height.Ordinals where

-- The rank of the ordinal of ordinals.  Ord(ℓ) of Height.Ordinals is the
-- height of level ℓ + 1 whose children are the heights of level ℓ.  Its
-- rank is Cubical's Ord(ℓ), the well-order of the well-orders of level ℓ
-- (ordinals): the rank of every child is a small well-order, below Ord(ℓ)
-- at its own point, and every small well-order is the rank of a child, its
-- canonical height.  Through TypeTopology.OrdinalOfOrdinals, the rank of
-- Ord(ℓ) is TypeTopology's OO ℓ (identity).

open import Agda.Primitive using (Level; lsuc)
open import Level using (lift; lower)

import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.Prelude as Cubical
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

import SPT.Cubical.TypeTopology.MLTT.Identity-Type as Identity
import SPT.Cubical.TypeTopology.MLTT.Sigma-Type as Sigma
open import SPT.Cubical.TypeTopology.UF.Equiv using (qinvs-are-equivs)
open import SPT.Cubical.TypeTopology.Ordinals.Equivalence using
  (_≃ₒ_; eqtoidₒ)

import SPT.Cubical.OrdinalGeometry.Height.Ordinals as Heights
open Heights using (Height; lift-height)
open import SPT.Cubical.OrdinalGeometry.Cubical.Height.Rank using
  (rank; child; least; canonical-height; canonical; lifted)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Ordinals using
  (Ord; lowerset; segments→simulation)
open import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Bridge using
  (toOrdinal; smallToOrdinal; path→＝; ＝→path)
open import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.FunExt using
  (funext)
open import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Univalence
  using (univalence)
import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.OrdinalOfOrdinals
  as TypeTopologyOrdinals
open import SPT.Cubical.TypeTopology.Ordinals.OrdinalOfOrdinals univalence
  using (OO)

private
  variable
    ℓ : Level

-- Mathematical shape: rank Ord(ℓ) ≃ Ord(ℓ).
--   ≼: the rank of the child lift t is rank t, the point of Ord(ℓ) whose
--      segment it is (lowerset);
--   ≽: the segment of Ord(ℓ) at W is W, the rank of the child at the
--      canonical height of W.
ordinals : Woset.WosetEquiv (rank (Heights.Ord ℓ)) (Ord ℓ)
ordinals {ℓ} =
  Simulation.isAntisym≼Equiv (rank (Heights.Ord ℓ)) (Ord ℓ)
    (least (Height ℓ) lift-height (Ord ℓ) λ t →
      Cubical._,_ (rank t)
        (Woset.compWosetEquiv (Woset.invWosetEquiv (lowerset (rank t)))
          (lifted t)))
    (segments→simulation {H = Ord ℓ} {K = rank (Heights.Ord ℓ)} λ W →
      Simulation.≺RespectsEquivL (rank (Heights.Ord ℓ))
        (Woset.compWosetEquiv
          (Woset.invWosetEquiv (lifted (canonical-height W)))
          (Woset.compWosetEquiv (canonical W) (lowerset W)))
        (child (Height ℓ) lift-height (canonical-height W)))

private
  -- An equivalence of well-orders, the second with a small relation, is
  -- an order equivalence of their TypeTopology ordinals.
  ordinal-equivalence : (A : Woset.Woset (lsuc ℓ) (lsuc ℓ))
    (B : Woset.Woset (lsuc ℓ) ℓ)
    → Woset.WosetEquiv A B → toOrdinal A ≃ₒ smallToOrdinal B
  ordinal-equivalence A B e =
    Sigma._,_ forth
      (Sigma._,_
        (λ x y r →
          lift (Equiv.equivFun (Woset.IsWosetEquiv.pres≺ (Cubical.snd e) x y)
            r))
        (Sigma._,_
          (qinvs-are-equivs forth
            (Sigma._,_ back
              (Sigma._,_ (λ x → path→＝ (Equiv.retEq (Cubical.fst e) x))
                (λ y → path→＝ (Equiv.secEq (Cubical.fst e) y)))))
          (λ u v r →
            Equiv.equivFun
              (Woset.IsWosetEquiv.pres≺
                (Cubical.snd (Woset.invWosetEquiv e)) u v)
              (lower r))))
    where
      forth = Equiv.equivFun (Cubical.fst e)
      back = Equiv.invEq (Cubical.fst e)

-- Mathematical shape: rank Ord(ℓ) = OO ℓ, as TypeTopology ordinals.
identity : Identity._＝_ (toOrdinal (rank (Heights.Ord ℓ))) (OO ℓ)
identity {ℓ} =
  path→＝
    (＝→path
      (eqtoidₒ (univalence (lsuc ℓ)) (λ {𝓤} {𝓥} → funext 𝓤 𝓥)
        (toOrdinal (rank (Heights.Ord ℓ))) (smallToOrdinal (Ord ℓ))
        (ordinal-equivalence (rank (Heights.Ord ℓ)) (Ord ℓ) ordinals))
      Cubical.∙ ＝→path TypeTopologyOrdinals.identity)
