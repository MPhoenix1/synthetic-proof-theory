{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Specification
  where

-- The specification of ω₁ by its cut, constructively: every principal
-- segment of H is merely presented and every ord(P) lies below H.  Every
-- geometry meets it.  It determines H up to a unique equivalence, so the
-- type of well-orders meeting it is contractible, and the cut, leastness
-- among well-orders of any level, and unpresentability follow from it.

open import Agda.Primitive using (Level; lsuc)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType as Reflection
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Base as Omega
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Cut as Cut

import Cubical.Data.Empty as Empty
import Cubical.Data.Sigma.Base as Sigma
import Cubical.Data.Sigma.Properties as SigmaProperties
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.Isomorphism as Iso
import Cubical.Foundations.Prelude as Cubical
import Cubical.Functions.Embedding as Embedding
import Cubical.HITs.PropositionalTruncation as Truncation
import Cubical.Induction.WellFounded as WellFounded
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

private
  variable
    ℓ source-level target-level : Level

------------------------------------------------------------------------
-- The cut specification

-- IsOmegaOneCut(H) = (Π h. MerelyPresented(H ↓ h)) × (Π P. ord(P) ≺ H).
--
-- It says nothing about embeddings into ℕ, choice or resizing.

record IsOmegaOneCut
    (H : Woset.Woset (lsuc ℓ) ℓ)
    : Set (lsuc ℓ) where
  constructor presented-omega-one-cut
  field
    principal-segment-presented :
        (point : Cubical.fst H)
      → Cut.MerelyPresented (Simulation._↓_ H point)

    all-presentations-strict :
        (presentation : Presented.CountableOrdinal𝒫 ℓ)
      → Simulation._≺_
          (Reflection.orderType presentation)
          H

open IsOmegaOneCut public

isPropIsOmegaOneCut :
    (H : Woset.Woset (lsuc ℓ) ℓ)
  → Cubical.isProp (IsOmegaOneCut H)
isPropIsOmegaOneCut H
    (presented-omega-one-cut left-principal left-strict)
    (presented-omega-one-cut right-principal right-strict) =
  Cubical.cong₂
    presented-omega-one-cut
    (Cubical.funExt λ point →
      Cut.isPropMerelyPresented (Simulation._↓_ H point)
        (left-principal point)
        (right-principal point))
    (Cubical.funExt λ presentation →
      Simulation.isPropValued≺
        (Reflection.orderType presentation)
        H
        (left-strict presentation)
        (right-strict presentation))

------------------------------------------------------------------------
-- The cut at every carrier level

-- IsOmegaOneCut(H) → (α ≺ H ⇔ MerelyPresented(α)), for well-orders α at
-- any carrier level, so H has no large predecessors.

cut-strict :
    {H : Woset.Woset (lsuc ℓ) ℓ}
  → IsOmegaOneCut H
  → (ordinal : Woset.Woset target-level ℓ)
  → (Simulation._≺_ ordinal H → Cut.MerelyPresented ordinal)
    Sigma.×
    (Cut.MerelyPresented ordinal → Simulation._≺_ ordinal H)
cut-strict {H = H} H-cut ordinal =
  Sigma._,_
    (λ strict →
      Truncation.map
        (λ represented →
          Cubical._,_
            (Cubical.fst represented)
            (Woset.compWosetEquiv
              (Cubical.snd represented)
              (Cubical.snd strict)))
        (principal-segment-presented H-cut (Cubical.fst strict)))
    (Truncation.rec
      (Simulation.isPropValued≺ ordinal H)
      (λ represented →
        Simulation.≺RespectsEquivL H
          (Cubical.snd represented)
          (all-presentations-strict H-cut
            (Cubical.fst represented))))

cut-strict-equivalence :
    {H : Woset.Woset (lsuc ℓ) ℓ}
  → IsOmegaOneCut H
  → (ordinal : Woset.Woset target-level ℓ)
  → Simulation._≺_ ordinal H
      Equiv.≃ Cut.MerelyPresented ordinal
cut-strict-equivalence
    {H = H} H-cut ordinal =
  Equiv.propBiimpl→Equiv
    (Simulation.isPropValued≺ ordinal H)
    (Cut.isPropMerelyPresented ordinal)
    (Cubical.fst
      (cut-strict H-cut ordinal))
    (Cubical.snd
      (cut-strict H-cut ordinal))

------------------------------------------------------------------------
-- Leastness among well-orders of any level

-- (Π h. (H ↓ h) ≺ K) → H ≼ K: send h to the point of K bounding H ↓ h.
-- H and K may have different carrier levels.

segments→simulation :
    {H : Woset.Woset source-level ℓ}
    {K : Woset.Woset target-level ℓ}
  → ((point : Cubical.fst H) →
      Simulation._≺_ (Simulation._↓_ H point) K)
  → Simulation._≼_ H K
segments→simulation {H = H} {K = K} strict =
  point-map Cubical., (point-map-monotone Cubical., point-map-lifting)
  where
    point-map : Cubical.fst H → Cubical.fst K
    point-map point = Cubical.fst (strict point)

    principal-equivalence :
        (point : Cubical.fst H)
      → Woset.WosetEquiv
          (Simulation._↓_ K (point-map point))
          (Simulation._↓_ H point)
    principal-equivalence point = Cubical.snd (strict point)

    point-map-monotone :
        (left right : Cubical.fst H)
      → Woset.WosetStr._≺_ (Cubical.snd H) left right
      → Woset.WosetStr._≺_ (Cubical.snd K)
          (point-map left)
          (point-map right)
    point-map-monotone left right left<right =
      Simulation.↓Respects≺⁻ K
        (point-map left)
        (point-map right)
        (Simulation.≺RespectsEquiv
          (Woset.invWosetEquiv (principal-equivalence left))
          (Woset.invWosetEquiv (principal-equivalence right))
          (Simulation.↓Respects≺ H left right left<right))

    point-map-lifting :
        (point : Cubical.fst H)
        (below : Cubical.fst K)
      → Woset.WosetStr._≺_ (Cubical.snd K) below (point-map point)
      → Cubical.Σ
          (Cubical.Σ (Cubical.fst H) λ predecessor →
            Woset.WosetStr._≺_ (Cubical.snd H) predecessor point)
          (λ predecessor → point-map (Cubical.fst predecessor) Cubical.≡ below)
    point-map-lifting point below below<image =
      (predecessor Cubical., predecessor<point)
      Cubical., image-predecessor≡below
      where
        below-segment-strict-point-segment :
          Simulation._≺_
            (Simulation._↓_ K below)
            (Simulation._↓_ H point)
        below-segment-strict-point-segment =
          Simulation.≺RespectsEquivR
            (Simulation._↓_ K below)
            (principal-equivalence point)
            (Simulation.↓Respects≺ K below (point-map point) below<image)

        predecessor-with-strict-witness :
          Cubical.fst (Simulation._↓_ H point)
        predecessor-with-strict-witness =
          Cubical.fst below-segment-strict-point-segment

        predecessor : Cubical.fst H
        predecessor = Cubical.fst predecessor-with-strict-witness

        predecessor<point :
          Woset.WosetStr._≺_ (Cubical.snd H) predecessor point
        predecessor<point = Cubical.snd predecessor-with-strict-witness

        predecessor-segment-to-nested-segment :
          Woset.WosetEquiv
            (Simulation._↓_ H predecessor)
            (Simulation._↓_ (Simulation._↓_ H point)
              predecessor-with-strict-witness)
        predecessor-segment-to-nested-segment =
          Equiv.invEq
            (Woset.WosetPath
              (Simulation._↓_ H predecessor)
              (Simulation._↓_ (Simulation._↓_ H point)
                predecessor-with-strict-witness))
            (Cubical.sym
              (Simulation.↓Absorb H point predecessor predecessor<point))

        image-segment→below :
          Woset.WosetEquiv
            (Simulation._↓_ K (point-map predecessor))
            (Simulation._↓_ K below)
        image-segment→below =
          Woset.compWosetEquiv
            (principal-equivalence predecessor)
            (Woset.compWosetEquiv
              predecessor-segment-to-nested-segment
              (Cubical.snd below-segment-strict-point-segment))

        image-predecessor≡below : point-map predecessor Cubical.≡ below
        image-predecessor≡below =
          Embedding.isEmbedding→Inj
            (Simulation.isEmbedding↓ K)
            (point-map predecessor)
            below
            (Equiv.equivFun
              (Woset.WosetPath
                (Simulation._↓_ K (point-map predecessor))
                (Simulation._↓_ K below))
              image-segment→below)

-- IsOmegaOneCut(H) → (Π P. ord(P) ≺ K) → H ≼ K, for K at any carrier
-- level: each segment of H is presented, so lies below K.

cut-least :
    {H : Woset.Woset (lsuc ℓ) ℓ}
  → IsOmegaOneCut H
  → (K : Woset.Woset target-level ℓ)
  → ((presentation : Presented.CountableOrdinal𝒫 ℓ) →
      Simulation._≺_
        (Reflection.orderType presentation)
        K)
  → Simulation._≼_ H K
cut-least
    {ℓ = ℓ} {target-level = target-level} {H = H}
    H-cut K presented<K =
  segments→simulation
    {ℓ = ℓ}
    {target-level = target-level}
    {H = H}
    {K = K}
    (strict-principal-in-K H-cut)
  where
    strict-principal-in-K :
        IsOmegaOneCut H
      → (point : Cubical.fst H)
      → Simulation._≺_ (Simulation._↓_ H point) K
    strict-principal-in-K cut point =
      Truncation.rec
        (Simulation.isPropValued≺ (Simulation._↓_ H point) K)
        (λ represented →
          Simulation.≺RespectsEquivL K
            (Cubical.snd represented)
            (presented<K (Cubical.fst represented)))
        (principal-segment-presented cut point)

-- IsOmegaOneCut(H) → ¬ MerelyPresented(H): a presentation P of H would give
-- ord(P) ≺ ord(P).

cut-not-presented :
    {H : Woset.Woset (lsuc ℓ) ℓ}
  → IsOmegaOneCut H
  → Cut.MerelyPresented H
  → Empty.⊥
cut-not-presented H-cut =
  Truncation.rec
    Empty.isProp⊥
    (λ represented →
      WellFounded.wf→x≮x
        Simulation.isWellFounded≺
        (Simulation.≺RespectsEquivR
          (Reflection.orderType (Cubical.fst represented))
          (Woset.invWosetEquiv (Cubical.snd represented))
          (all-presentations-strict H-cut
            (Cubical.fst represented))))

------------------------------------------------------------------------
-- Every geometry meets the specification

-- IsOmegaOneCut(ω₁ᴳ(G)) for every geometry G: segments are presented by
-- lower cones (Cut), and ord(P) ≺ ω₁ᴳ(G) through P + 1 (Base).

isOmegaOneCutᴳ :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → IsOmegaOneCut
      (Omega.ω₁ᴳ geometry)
isOmegaOneCutᴳ
    geometry =
  record
    { principal-segment-presented =
        Cut.segment-presentedᴳ geometry
    ; all-presentations-strict =
        Omega.orderType-strictᴳ geometry
    }

isOmegaOneCut :
  IsOmegaOneCut (Omega.ω₁ ℓ)
isOmegaOneCut {ℓ} =
  Cubical.subst
    IsOmegaOneCut
    Omega.ω₁-canonical
    (isOmegaOneCutᴳ
      (Presented.ω₁.Geometry.canonical {ℓ}))

-- Hence leastness among targets of any level, and unpresentability, for
-- ω₁ᴳ(G) and for ω₁.

large-leastᴳ :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (K : Woset.Woset target-level ℓ)
  → ((presentation : Presented.CountableOrdinal𝒫 ℓ) →
      Simulation._≺_ (Reflection.orderType presentation) K)
  → Simulation._≼_ (Omega.ω₁ᴳ geometry) K
large-leastᴳ geometry =
  cut-least
    (isOmegaOneCutᴳ
      geometry)

large-least :
    (K : Woset.Woset target-level ℓ)
  → ((presentation : Presented.CountableOrdinal𝒫 ℓ) →
      Simulation._≺_ (Reflection.orderType presentation) K)
  → Simulation._≼_ (Omega.ω₁ ℓ) K
large-least =
  cut-least
    isOmegaOneCut

not-presentedᴳ :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → Cut.MerelyPresented (Omega.ω₁ᴳ geometry)
  → Empty.⊥
not-presentedᴳ geometry =
  cut-not-presented
    (isOmegaOneCutᴳ
      geometry)

not-presented :
  Cut.MerelyPresented (Omega.ω₁ ℓ) → Empty.⊥
not-presented =
  cut-not-presented
    isOmegaOneCut

------------------------------------------------------------------------
-- Uniqueness

-- IsOmegaOneCut(H) → IsOmegaOneCut(K) → Π h. (H ↓ h) ≺ K.

abstract
  segment-strict-other :
      {H K : Woset.Woset (lsuc ℓ) ℓ}
    → IsOmegaOneCut H
    → IsOmegaOneCut K
    → (point : Cubical.fst H)
    → Simulation._≺_ (Simulation._↓_ H point) K
  segment-strict-other
      {H = H} {K = K} H-cut K-cut point =
    Truncation.rec
      (Simulation.isPropValued≺ (Simulation._↓_ H point) K)
      (λ represented →
        Simulation.≺RespectsEquivL K
          (Cubical.snd represented)
          (all-presentations-strict K-cut
            (Cubical.fst represented)))
      (principal-segment-presented H-cut point)

  segment-point-other :
      {H K : Woset.Woset (lsuc ℓ) ℓ}
    → IsOmegaOneCut H
    → IsOmegaOneCut K
    → Cubical.fst H
    → Cubical.fst K
  segment-point-other H-cut K-cut point =
    Cubical.fst
      (segment-strict-other H-cut K-cut point)

  segment-equivalence-other :
      {H K : Woset.Woset (lsuc ℓ) ℓ}
    → (H-cut : IsOmegaOneCut H)
    → (K-cut : IsOmegaOneCut K)
    → (point : Cubical.fst H)
    → Woset.WosetEquiv
        (Simulation._↓_ K
          (segment-point-other H-cut K-cut point))
        (Simulation._↓_ H point)
  segment-equivalence-other H-cut K-cut point =
    Cubical.snd
      (segment-strict-other H-cut K-cut point)

-- IsOmegaOneCut(H) → IsOmegaOneCut(K) → H ≃ K: h goes to the point of K
-- with the same principal segment.  No excluded middle, choice or resizing
-- is used.

abstract
  cut-equivalence :
      {H K : Woset.Woset (lsuc ℓ) ℓ}
    → IsOmegaOneCut H
    → IsOmegaOneCut K
    → Woset.WosetEquiv H K
  cut-equivalence
      {H = H} {K = K} H-cut K-cut =
    carrier-equivalence
    Cubical., Woset.makeIsWosetEquiv
        carrier-equivalence
        relation-forward
        relation-backward
    where
      H-to-K-point : Cubical.fst H → Cubical.fst K
      H-to-K-point =
        segment-point-other H-cut K-cut

      K-to-H-point : Cubical.fst K → Cubical.fst H
      K-to-H-point =
        segment-point-other K-cut H-cut

      H-segment-in-K :
          (point : Cubical.fst H)
        → Woset.WosetEquiv
            (Simulation._↓_ K (H-to-K-point point))
            (Simulation._↓_ H point)
      H-segment-in-K =
        segment-equivalence-other H-cut K-cut

      K-segment-in-H :
          (point : Cubical.fst K)
        → Woset.WosetEquiv
            (Simulation._↓_ H (K-to-H-point point))
            (Simulation._↓_ K point)
      K-segment-in-H =
        segment-equivalence-other K-cut H-cut

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

  cut-path :
      {H K : Woset.Woset (lsuc ℓ) ℓ}
    → IsOmegaOneCut H
    → IsOmegaOneCut K
    → H Cubical.≡ K
  cut-path
      {H = H} {K = K} H-cut K-cut =
    Equiv.equivFun (Woset.WosetPath H K)
      (cut-equivalence H-cut K-cut)

-- The equivalence is unique, since equivalences of well-orders form a
-- proposition.

cut-equivalence-isContr :
    {H K : Woset.Woset (lsuc ℓ) ℓ}
  → IsOmegaOneCut H
  → IsOmegaOneCut K
  → Cubical.isContr (Woset.WosetEquiv H K)
cut-equivalence-isContr H-cut K-cut =
  let
    comparison =
      cut-equivalence H-cut K-cut
  in
  comparison
  Cubical., Simulation.isPropValuedWosetEquiv comparison

------------------------------------------------------------------------
-- Independence of the geometry

-- Any two geometries give equivalent, hence path-equal, well-orders, and so
-- does every geometry and the canonical one.  The geometries themselves
-- need not be equal (see Fiber.Geometry).

equivalenceᴳ :
    (left right : Presented.𝒫ω₁𝒢 ℓ)
  → Woset.WosetEquiv
      (Omega.ω₁ᴳ left)
      (Omega.ω₁ᴳ right)
equivalenceᴳ left right =
  cut-equivalence
    (isOmegaOneCutᴳ
      left)
    (isOmegaOneCutᴳ
      right)

pathᴳ :
    (left right : Presented.𝒫ω₁𝒢 ℓ)
  → Omega.ω₁ᴳ left
    Cubical.≡ Omega.ω₁ᴳ right
pathᴳ left right =
  cut-path
    (isOmegaOneCutᴳ
      left)
    (isOmegaOneCutᴳ
      right)

canonical-equivalenceᴳ :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → Woset.WosetEquiv
      (Omega.ω₁ᴳ geometry)
      (Omega.ω₁ ℓ)
canonical-equivalenceᴳ geometry =
  cut-equivalence
    (isOmegaOneCutᴳ
      geometry)
    isOmegaOneCut

canonical-pathᴳ :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → Omega.ω₁ᴳ geometry
    Cubical.≡ Omega.ω₁ ℓ
canonical-pathᴳ geometry =
  cut-path
    (isOmegaOneCutᴳ
      geometry)
    isOmegaOneCut

-- IsOmegaOneCut(H) ≃ (H = ω₁ᴳ(G)); both sides are propositions.

isOmegaOneCut≃path :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (H : Woset.Woset (lsuc ℓ) ℓ)
  → IsOmegaOneCut H
    Equiv.≃
    (H Cubical.≡ Omega.ω₁ᴳ geometry)
isOmegaOneCut≃path geometry H =
  Equiv.propBiimpl→Equiv
    (isPropIsOmegaOneCut H)
    (Woset.isSetWoset H
      (Omega.ω₁ᴳ geometry))
    (λ H-cut →
      cut-path
        H-cut
        (isOmegaOneCutᴳ
          geometry))
    (λ equality →
      Cubical.subst
        IsOmegaOneCut
        (Cubical.sym equality)
        (isOmegaOneCutᴳ
          geometry))

-- The type Σ(H : Woset (lsuc ℓ) ℓ). IsOmegaOneCut(H) is contractible.

CutObject :
  (level : Level) → Set (lsuc (lsuc level))
CutObject level =
  Cubical.Σ
    (Woset.Woset (lsuc level) level)
    IsOmegaOneCut

cutObjectᴳ :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → CutObject ℓ
cutObjectᴳ geometry =
  Omega.ω₁ᴳ geometry
  Cubical.,
  isOmegaOneCutᴳ
    geometry

cutObject-isContr :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → Cubical.isContr (CutObject ℓ)
cutObject-isContr geometry =
  cutObjectᴳ geometry
  Cubical., λ candidate →
    SigmaProperties.Σ≡Prop
      isPropIsOmegaOneCut
      (cut-path
        (isOmegaOneCutᴳ
          geometry)
        (Cubical.snd candidate))

ω₁-cutObject-isContr :
  Cubical.isContr (CutObject ℓ)
ω₁-cutObject-isContr {ℓ} =
  cutObject-isContr
    (Presented.ω₁.Geometry.canonical {ℓ})
