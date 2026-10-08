{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Specification where

-- The ℕ-Hartogs specification of a well-order H with carrier one universe
-- up: small principal segments, and a cut α ≺ H ⇔ ‖|α| ↪ ℕ‖ (IsHartogsCut);
-- with a carrier that does not embed into ℕ (IsHartogs).  H_ℕ meets the
-- cut constructively, the presented ω₁ meets it under excluded middle, and
-- any two well-orders meeting it are equivalent.

open import Agda.Primitive using (Level; lsuc)

import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Countability
  as NatCountability
import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Base as Hartogs
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType as Reflection
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Base as Omega
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Countability
  as CountabilityCut
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Cut
  as PresentationCut

import Cubical.Data.Empty as Empty
import Cubical.Data.Sigma.Base as Sigma
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.Isomorphism as Iso
import Cubical.Foundations.Prelude as Cubical
import Cubical.Functions.Embedding as Embedding
import Cubical.HITs.PropositionalTruncation as Truncation
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- Small principal segments

-- A principal segment H ↓ h is merely small:
--
--   MerelySmall(H,h) = ‖Σ(α : Woset ℓ ℓ). α ≃ H ↓ h‖.

MerelySmall :
    (H : Woset.Woset (lsuc ℓ) ℓ)
  → Cubical.fst H
  → Set (lsuc ℓ)
MerelySmall {ℓ} H point =
  Truncation.∥
    Cubical.Σ
      (Woset.Woset ℓ ℓ)
      (λ ordinal → Woset.WosetEquiv ordinal (Simulation._↓_ H point))
  ∥₁

------------------------------------------------------------------------
-- The specifications

-- IsHartogsCut(H) = (Π h. MerelySmall(H,h))
--                × Π(α : Woset ℓ ℓ). (α ≺ H ⇔ ‖|α| ↪ ℕ‖).
--
-- It does not say that |H| fails to embed into ℕ; IsHartogs adds that.

record IsHartogsCut
    (H : Woset.Woset (lsuc ℓ) ℓ)
    : Set (lsuc ℓ) where
  field
    principal-segment-small :
        (point : Cubical.fst H)
      → MerelySmall H point

    small-strict-cut :
        (ordinal : Woset.Woset ℓ ℓ)
      → (Simulation._≺_ ordinal H
          → NatCountability.MerelyEmbedsInNat (Cubical.fst ordinal))
        Sigma.×
        (NatCountability.MerelyEmbedsInNat (Cubical.fst ordinal)
          → Simulation._≺_ ordinal H)

open IsHartogsCut public

-- IsHartogs(H) = IsHartogsCut(H) × ¬ ‖|H| ↪ ℕ‖.  Proving the second field
-- needs a hypothesis such as resizing (see Uncountability).

record IsHartogs
    (H : Woset.Woset (lsuc ℓ) ℓ)
    : Set (lsuc ℓ) where
  field
    cut-characterization : IsHartogsCut H

    carrier-not-merely-embeds-in-nat :
      NatCountability.MerelyEmbedsInNat (Cubical.fst H) → Empty.⊥

open IsHartogs public

isHartogs :
    {H : Woset.Woset (lsuc ℓ) ℓ}
  → IsHartogsCut H
  → (NatCountability.MerelyEmbedsInNat (Cubical.fst H) → Empty.⊥)
  → IsHartogs H
isHartogs
    cut not-embeddable =
  record
    { cut-characterization = cut
    ; carrier-not-merely-embeds-in-nat = not-embeddable
    }

------------------------------------------------------------------------
-- Inhabitants of the cut

-- H_ℕ meets the cut: each point (α , c) gives α as the small
-- representative of its segment, and the cut is `Hartogs.strict-cut`.

segment-small :
    (point : Hartogs.Carrier ℓ)
  → MerelySmall (Hartogs.NatHartogs ℓ) point
segment-small point =
  Truncation.∣
    ( Cubical.fst point
    Cubical.,
      Woset.invWosetEquiv (Hartogs.principalEquiv point)
    )
  ∣₁

natHartogs-isHartogsCut :
  IsHartogsCut (Hartogs.NatHartogs ℓ)
natHartogs-isHartogsCut =
  record
    { principal-segment-small = segment-small
    ; small-strict-cut = Hartogs.strict-cut
    }

-- Under excluded middle at ℓ the presented ω₁ meets the cut.  Small
-- segments are constructive (every segment is presented); excluded middle
-- enters only through the comparison of countability with ‖· ↪ ℕ‖.

omegaOne-segment-small :
    (point : Cubical.fst (Omega.ω₁ ℓ))
  → MerelySmall
      (Omega.ω₁ ℓ) point
omegaOne-segment-small point =
  Truncation.map
    (λ represented →
      Reflection.orderType (Cubical.fst represented)
      Cubical., Cubical.snd represented)
    (PresentationCut.segment-presented point)

omegaOne-isHartogsCut :
    CountabilityCut.ExcludedMiddle ℓ
  → IsHartogsCut (Omega.ω₁ ℓ)
omegaOne-isHartogsCut excluded-middle =
  record
    { principal-segment-small = omegaOne-segment-small
    ; small-strict-cut =
        CountabilityCut.classical-embedding-cut
          excluded-middle
    }

------------------------------------------------------------------------
-- Uniqueness

-- Cut(H) → Cut(K) → Π h. (H ↓ h) ≺ K: a small representative of H ↓ h
-- lies below H, so it embeds into ℕ, so it lies below K.  The conclusion
-- is a proposition, so the truncated representative can be used.

abstract
  principalSegment-strict-other :
      {H K : Woset.Woset (lsuc ℓ) ℓ}
    → IsHartogsCut H
    → IsHartogsCut K
    → (point : Cubical.fst H)
    → Simulation._≺_ (Simulation._↓_ H point) K
  principalSegment-strict-other {H = H} {K = K} H-cut K-cut point =
    Truncation.rec
      (Simulation.isPropValued≺ (Simulation._↓_ H point) K)
      (λ represented →
        let
          ordinal = Cubical.fst represented
          ordinal≃segment = Cubical.snd represented

          ordinal<H : Simulation._≺_ ordinal H
          ordinal<H =
            Simulation.≺RespectsEquivL H
              (Woset.invWosetEquiv ordinal≃segment)
              (Simulation.↓Decreasing H point)

          ordinal-countable =
            Cubical.fst (small-strict-cut H-cut ordinal) ordinal<H

          ordinal<K =
            Cubical.snd (small-strict-cut K-cut ordinal) ordinal-countable
        in
        Simulation.≺RespectsEquivL K ordinal≃segment ordinal<K)
      (principal-segment-small H-cut point)

  principalSegment-point-other :
      {H K : Woset.Woset (lsuc ℓ) ℓ}
    → IsHartogsCut H
    → IsHartogsCut K
    → Cubical.fst H
    → Cubical.fst K
  principalSegment-point-other H-cut K-cut point =
    Cubical.fst (principalSegment-strict-other H-cut K-cut point)

  principalSegment-equivalence-other :
      {H K : Woset.Woset (lsuc ℓ) ℓ}
    → (H-cut : IsHartogsCut H)
    → (K-cut : IsHartogsCut K)
    → (point : Cubical.fst H)
    → Woset.WosetEquiv
        (Simulation._↓_ K
          (principalSegment-point-other H-cut K-cut point))
        (Simulation._↓_ H point)
  principalSegment-equivalence-other H-cut K-cut point =
    Cubical.snd (principalSegment-strict-other H-cut K-cut point)

-- Cut(H) → Cut(K) → H ≃ K: h goes to the point of K whose principal
-- segment is H ↓ h, and back.  No further hypothesis is needed.

hartogsCut-equivalence :
    {H K : Woset.Woset (lsuc ℓ) ℓ}
  → IsHartogsCut H
  → IsHartogsCut K
  → Woset.WosetEquiv H K
hartogsCut-equivalence {H = H} {K = K} H-cut K-cut =
  carrier-equivalence
  Cubical., Woset.makeIsWosetEquiv
      carrier-equivalence
      relation-forward
      relation-backward
  where
    H-to-K-point : Cubical.fst H → Cubical.fst K
    H-to-K-point = principalSegment-point-other H-cut K-cut

    K-to-H-point : Cubical.fst K → Cubical.fst H
    K-to-H-point = principalSegment-point-other K-cut H-cut

    H-segment-in-K :
        (point : Cubical.fst H)
      → Woset.WosetEquiv
          (Simulation._↓_ K (H-to-K-point point))
          (Simulation._↓_ H point)
    H-segment-in-K = principalSegment-equivalence-other H-cut K-cut

    K-segment-in-H :
        (point : Cubical.fst K)
      → Woset.WosetEquiv
          (Simulation._↓_ H (K-to-H-point point))
          (Simulation._↓_ K point)
    K-segment-in-H = principalSegment-equivalence-other K-cut H-cut

    carrier-iso : Iso.Iso (Cubical.fst H) (Cubical.fst K)
    carrier-iso = record
      { fun = H-to-K-point
      ; inv = K-to-H-point
      ; rightInv = λ point →
          let
            inverse-point = K-to-H-point point
            roundtrip-point = H-to-K-point inverse-point
          in
          Embedding.isEmbedding→Inj
            (Simulation.isEmbedding↓ K)
            roundtrip-point point
            (Equiv.equivFun
              (Woset.WosetPath
                (Simulation._↓_ K roundtrip-point)
                (Simulation._↓_ K point))
              (Woset.compWosetEquiv
                (H-segment-in-K inverse-point)
                (K-segment-in-H point)))
      ; leftInv = λ point →
          let
            forward-point = H-to-K-point point
            roundtrip-point = K-to-H-point forward-point
          in
          Embedding.isEmbedding→Inj
            (Simulation.isEmbedding↓ H)
            roundtrip-point point
            (Equiv.equivFun
              (Woset.WosetPath
                (Simulation._↓_ H roundtrip-point)
                (Simulation._↓_ H point))
              (Woset.compWosetEquiv
                (K-segment-in-H forward-point)
                (H-segment-in-K point)))
      }

    carrier-equivalence : Equiv._≃_ (Cubical.fst H) (Cubical.fst K)
    carrier-equivalence = Iso.isoToEquiv carrier-iso

    relation-forward :
        (left right : Cubical.fst H)
      → Woset.WosetStr._≺_ (Cubical.snd H) left right
      → Woset.WosetStr._≺_ (Cubical.snd K)
          (Equiv.equivFun carrier-equivalence left)
          (Equiv.equivFun carrier-equivalence right)
    relation-forward left right left<right =
      Simulation.↓Respects≺⁻ K
        (Equiv.equivFun carrier-equivalence left)
        (Equiv.equivFun carrier-equivalence right)
        (Simulation.≺RespectsEquiv
          (Woset.invWosetEquiv (H-segment-in-K left))
          (Woset.invWosetEquiv (H-segment-in-K right))
          (Simulation.↓Respects≺ H left right left<right))

    relation-backward :
        (left right : Cubical.fst K)
      → Woset.WosetStr._≺_ (Cubical.snd K) left right
      → Woset.WosetStr._≺_ (Cubical.snd H)
          (Equiv.invEq carrier-equivalence left)
          (Equiv.invEq carrier-equivalence right)
    relation-backward left right left<right =
      Simulation.↓Respects≺⁻ H
        (Equiv.invEq carrier-equivalence left)
        (Equiv.invEq carrier-equivalence right)
        (Simulation.≺RespectsEquiv
          (Woset.invWosetEquiv (K-segment-in-H left))
          (Woset.invWosetEquiv (K-segment-in-H right))
          (Simulation.↓Respects≺ K left right left<right))

hartogsCut-path :
    {H K : Woset.Woset (lsuc ℓ) ℓ}
  → IsHartogsCut H
  → IsHartogsCut K
  → H Cubical.≡ K
hartogsCut-path {H = H} {K = K} H-cut K-cut =
  Equiv.equivFun (Woset.WosetPath H K)
    (hartogsCut-equivalence H-cut K-cut)

-- Under excluded middle at ℓ, the presented ω₁ equals H_ℕ, by uniqueness.

omegaOne≡natHartogs :
    CountabilityCut.ExcludedMiddle ℓ
  → Omega.ω₁ ℓ Cubical.≡ Hartogs.NatHartogs ℓ
omegaOne≡natHartogs excluded-middle =
  hartogsCut-path
    (omegaOne-isHartogsCut excluded-middle)
    natHartogs-isHartogsCut
