{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Hartogs where

-- ω₁ compared with H_ℕ.  Under excluded middle at ℓ the two are
-- equivalent well-orders, for every geometry, by uniqueness of the ℕ-Hartogs
-- cut.  With resizing (or excluded middle at lsuc ℓ) the carrier of ω₁ does
-- not embed into ℕ, so ω₁ meets the full Hartogs specification.

open import Agda.Primitive using (Level; lsuc)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Countability
  as NatCountability
import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Base as Hartogs
import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Specification
  as Specification
import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Uncountability
  as Uncountability
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Base as Omega
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Specification
  as PresentedSpecification
open import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Hartogs.Carrier
  public

import Cubical.Data.Empty as Empty
import Cubical.Foundations.Prelude as Cubical
import Cubical.Relation.Binary.Order.Woset.Base as Woset

private
  variable
    ℓ : Level

-- ExcludedMiddle(ℓ) → ω₁(ℓ) ≃ H_ℕ(ℓ): both meet the ℕ-Hartogs cut, so the
-- uniqueness theorem applies.  No choice or resizing is used.

abstract
  equivalence :
      NatCountability.ExcludedMiddle ℓ
    → Woset.WosetEquiv
        (Omega.ω₁ ℓ)
        (Hartogs.NatHartogs ℓ)
  equivalence {ℓ} excluded-middle =
    Specification.hartogsCut-equivalence
      (Specification.omegaOne-isHartogsCut
        excluded-middle)
      Specification.natHartogs-isHartogsCut

-- The corresponding path ω₁(ℓ) = H_ℕ(ℓ).

path :
    NatCountability.ExcludedMiddle ℓ
  → Omega.ω₁ ℓ Cubical.≡ Hartogs.NatHartogs ℓ
path {ℓ} excluded-middle =
  Specification.omegaOne≡natHartogs
    excluded-middle

------------------------------------------------------------------------
-- For every geometry

-- ExcludedMiddle(ℓ) → ω₁ᴳ(G) ≃ H_ℕ(ℓ), and the path, by composing with the
-- equivalence ω₁ᴳ(G) ≃ ω₁(ℓ) of Specification.

abstract
  equivalenceᴳ :
      (geometry : Presented.𝒫ω₁𝒢 ℓ)
    → NatCountability.ExcludedMiddle ℓ
    → Woset.WosetEquiv
        (Omega.ω₁ᴳ geometry)
        (Hartogs.NatHartogs ℓ)
  equivalenceᴳ
      geometry excluded-middle =
    Woset.compWosetEquiv
      (PresentedSpecification.canonical-equivalenceᴳ
        geometry)
      (equivalence excluded-middle)

pathᴳ :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → NatCountability.ExcludedMiddle ℓ
  → Omega.ω₁ᴳ geometry
      Cubical.≡ Hartogs.NatHartogs ℓ
pathᴳ
    geometry excluded-middle =
  Cubical._∙_
    (PresentedSpecification.canonical-pathᴳ
      geometry)
    (path excluded-middle)

isHartogsCutᴳ :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → NatCountability.ExcludedMiddle ℓ
  → Specification.IsHartogsCut
      (Omega.ω₁ᴳ geometry)
isHartogsCutᴳ
    geometry excluded-middle =
  Cubical.subst
    Specification.IsHartogsCut
    (Cubical.sym
      (PresentedSpecification.canonical-pathᴳ
        geometry))
    (Specification.omegaOne-isHartogsCut
      excluded-middle)

------------------------------------------------------------------------
-- The carrier does not embed into ℕ

-- ExcludedMiddle(ℓ) → PropositionalResizing(lsuc ℓ,ℓ) → ¬ ‖|ω₁(ℓ)| ↪ ℕ‖:
-- transport an embedding along ω₁(ℓ) ≃ H_ℕ(ℓ) and use Hartogs.Uncountability.

abstract
  not-embeds :
      NatCountability.ExcludedMiddle ℓ
    → Uncountability.PropositionalResizing (lsuc ℓ) ℓ
    → NatCountability.MerelyEmbedsInNat
        (Cubical.fst (Omega.ω₁ ℓ))
    → Empty.⊥
  not-embeds
      excluded-middle resize omega-countable =
    let
      comparison =
        equivalence excluded-middle
    in
    Uncountability.not-embeds resize
      (Hartogs.embeds-≃
        (Cubical.fst comparison)
        omega-countable)

-- Under the same hypotheses, ω₁(ℓ) meets the full Hartogs specification.

isHartogs :
    NatCountability.ExcludedMiddle ℓ
  → Uncountability.PropositionalResizing (lsuc ℓ) ℓ
  → Specification.IsHartogs
      (Omega.ω₁ ℓ)
isHartogs excluded-middle resize =
  Specification.isHartogs
    (Specification.omegaOne-isHartogsCut
      excluded-middle)
    (not-embeds excluded-middle resize)

-- The same two results for ω₁ᴳ(G).

abstract
  not-embedsᴳ :
      (geometry : Presented.𝒫ω₁𝒢 ℓ)
    → NatCountability.ExcludedMiddle ℓ
    → Uncountability.PropositionalResizing (lsuc ℓ) ℓ
    → NatCountability.MerelyEmbedsInNat
        (Cubical.fst (Omega.ω₁ᴳ geometry))
    → Empty.⊥
  not-embedsᴳ
      geometry excluded-middle resize omega-countable =
    Uncountability.not-embeds resize
      (Hartogs.embeds-≃
        (Cubical.fst
          (equivalenceᴳ
            geometry excluded-middle))
        omega-countable)

isHartogsᴳ :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → NatCountability.ExcludedMiddle ℓ
  → Uncountability.PropositionalResizing (lsuc ℓ) ℓ
  → Specification.IsHartogs
      (Omega.ω₁ᴳ geometry)
isHartogsᴳ
    geometry excluded-middle resize =
  Specification.isHartogs
    (isHartogsCutᴳ
      geometry excluded-middle)
    (not-embedsᴳ
      geometry excluded-middle resize)

------------------------------------------------------------------------
-- Under excluded middle at lsuc ℓ

-- ExcludedMiddle(lsuc ℓ) → ¬ ‖|ω₁(ℓ)| ↪ ℕ‖: excluded middle at lsuc ℓ
-- gives both excluded middle at ℓ and the resizing used above.

classical-not-embeds :
    NatCountability.ExcludedMiddle (lsuc ℓ)
  → NatCountability.MerelyEmbedsInNat
      (Cubical.fst (Omega.ω₁ ℓ))
  → Empty.⊥
classical-not-embeds excluded-middle =
  not-embeds
    (Uncountability.excludedMiddle-lower excluded-middle)
    (Uncountability.excludedMiddle→resizing
      excluded-middle)

-- ExcludedMiddle(lsuc ℓ) → IsHartogs(ω₁(ℓ)).

classical-isHartogs :
    NatCountability.ExcludedMiddle (lsuc ℓ)
  → Specification.IsHartogs
      (Omega.ω₁ ℓ)
classical-isHartogs excluded-middle =
  isHartogs
    (Uncountability.excludedMiddle-lower excluded-middle)
    (Uncountability.excludedMiddle→resizing
      excluded-middle)

classical-not-embedsᴳ :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → NatCountability.ExcludedMiddle (lsuc ℓ)
  → NatCountability.MerelyEmbedsInNat
      (Cubical.fst (Omega.ω₁ᴳ geometry))
  → Empty.⊥
classical-not-embedsᴳ
    geometry excluded-middle =
  not-embedsᴳ
    geometry
    (Uncountability.excludedMiddle-lower excluded-middle)
    (Uncountability.excludedMiddle→resizing
      excluded-middle)

classical-isHartogsᴳ :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → NatCountability.ExcludedMiddle (lsuc ℓ)
  → Specification.IsHartogs
      (Omega.ω₁ᴳ geometry)
classical-isHartogsᴳ
    geometry excluded-middle =
  isHartogsᴳ
    geometry
    (Uncountability.excludedMiddle-lower excluded-middle)
    (Uncountability.excludedMiddle→resizing
      excluded-middle)
