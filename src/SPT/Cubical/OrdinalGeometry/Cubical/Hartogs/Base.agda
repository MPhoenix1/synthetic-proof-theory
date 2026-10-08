{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Base where

-- The ℕ-Hartogs well-order H_ℕ: small well-orders whose carrier merely
-- embeds into ℕ, ordered by bounded simulation,
--
--   H_ℕ(ℓ) = Σ(α : Woset ℓ ℓ). ‖|α| ↪ ℕ‖,
--
-- and its cut α ≺ H_ℕ ⇔ ‖|α| ↪ ℕ‖ (`strict-cut`), all constructive.

open import Agda.Primitive using (Level; lsuc)

import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Countability
  as NatCountability

import Cubical.Data.Sigma.Base as Sigma
import Cubical.Data.Sigma.Properties as SigmaProperties
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Isomorphism as Iso
import Cubical.Foundations.Prelude as Cubical
import Cubical.Functions.Embedding as Embedding
import Cubical.HITs.PropositionalTruncation as Truncation
import Cubical.Induction.WellFounded as WellFounded
import Cubical.Relation.Binary.Extensionality as Extensionality
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- Embeddability into ℕ is closed downward

embeds-≃ :
    ∀ {left-level right-level}
      {A : Set left-level}
      {B : Set right-level}
  → Equiv._≃_ A B
  → NatCountability.MerelyEmbedsInNat A
  → NatCountability.MerelyEmbedsInNat B
embeds-≃ equivalence =
  Truncation.map
    (λ embedding →
      Embedding.compEmbedding
        embedding
        (Embedding.Equiv→Embedding (Equiv.invEquiv equivalence)))

-- α ≺ β → ‖|β| ↪ ℕ‖ → ‖|α| ↪ ℕ‖: α is a principal segment of β, which
-- includes into |β|.

principal-embeds :
    (smaller larger : Woset.Woset ℓ ℓ)
  → Simulation._≺_ smaller larger
  → NatCountability.MerelyEmbedsInNat (Cubical.fst larger)
  → NatCountability.MerelyEmbedsInNat (Cubical.fst smaller)
principal-embeds smaller larger strict =
  Truncation.map
    (λ larger-embedding →
      let
        point = Cubical.fst strict
        segment-equivalence = Cubical.fst (Cubical.snd strict)
        segment-inclusion =
          Embedding.EmbeddingΣProp
            (λ x →
              Woset.IsWoset.is-prop-valued
                (Woset.WosetStr.isWoset (Cubical.snd larger))
                x point)
      in
      Embedding.compEmbedding
        larger-embedding
        (Embedding.compEmbedding
          segment-inclusion
          (Embedding.Equiv→Embedding
            (Equiv.invEquiv segment-equivalence))))

------------------------------------------------------------------------
-- The carrier and the order

-- Carrier(ℓ) = Σ(α : Woset ℓ ℓ). ‖|α| ↪ ℕ‖.  It lives one universe up.

Carrier : (level : Level) → Set (lsuc level)
Carrier level =
  Cubical.Σ
    (Woset.Woset level level)
    (λ ordinal → NatCountability.MerelyEmbedsInNat (Cubical.fst ordinal))

-- (α , _) < (β , _) when α ≺ β; the embedding witnesses play no part.

Strict :
  Carrier ℓ → Carrier ℓ → Set ℓ
Strict smaller larger =
  Simulation._≺_ (Cubical.fst smaller) (Cubical.fst larger)

Carrier-isSet : Cubical.isSet (Carrier ℓ)
Carrier-isSet =
  HLevels.isSetΣSndProp
    Woset.isSetWoset
    (λ _ → NatCountability.isPropMerelyEmbedsInNat)

Strict-isProp :
    (smaller larger : Carrier ℓ)
  → Cubical.isProp (Strict smaller larger)
Strict-isProp smaller larger =
  Simulation.isPropValued≺
    (Cubical.fst smaller)
    (Cubical.fst larger)

Strict-wf :
  WellFounded.WellFounded (Strict {ℓ})
Strict-wf (ordinal Cubical., countable) =
  WellFounded.WFI.induction
    Simulation.isWellFounded≺
    {P = λ current →
      (current-countable :
        NatCountability.MerelyEmbedsInNat (Cubical.fst current)) →
      WellFounded.Acc
        Strict (current Cubical., current-countable)}
    (λ current smaller current-countable →
      WellFounded.acc
        (λ (predecessor Cubical., predecessor-countable)
            predecessor<current →
          smaller predecessor predecessor<current predecessor-countable))
    ordinal countable

Strict-trans :
    (smaller middle larger : Carrier ℓ)
  → Strict smaller middle
  → Strict middle larger
  → Strict smaller larger
Strict-trans smaller middle larger =
  Simulation.isTrans≺
    (Cubical.fst smaller)
    (Cubical.fst middle)
    (Cubical.fst larger)

private
  lower-equivalence :
      (left right : Carrier ℓ)
    → ((candidate : Carrier ℓ) →
        Strict candidate left Equiv.≃
        Strict candidate right)
    → (candidate : Woset.Woset ℓ ℓ)
    → Simulation._≺_ candidate (Cubical.fst left) Equiv.≃
      Simulation._≺_ candidate (Cubical.fst right)
  lower-equivalence left right lower candidate =
    Equiv.propBiimpl→Equiv
      (Simulation.isPropValued≺ candidate (Cubical.fst left))
      (Simulation.isPropValued≺ candidate (Cubical.fst right))
      (λ candidate<left →
        Equiv.equivFun
          (lower
            (candidate
              Cubical.,
              principal-embeds
                candidate (Cubical.fst left)
                candidate<left (Cubical.snd left)))
          candidate<left)
      (λ candidate<right →
        Equiv.invEq
          (lower
            (candidate
              Cubical.,
              principal-embeds
                candidate (Cubical.fst right)
                candidate<right (Cubical.snd right)))
          candidate<right)

  extensional-path :
      (left right : Carrier ℓ)
    → ((candidate : Carrier ℓ) →
        Strict candidate left Equiv.≃
        Strict candidate right)
    → left Cubical.≡ right
  extensional-path left right lower =
    SigmaProperties.Σ≡Prop
      (λ _ → NatCountability.isPropMerelyEmbedsInNat)
      (Extensionality.isWeaklyExtensional→≺Equiv→≡
        Simulation._≺_
        Simulation.isWeaklyExtensional≺
        (Cubical.fst left)
        (Cubical.fst right)
        (lower-equivalence left right lower))

Strict-extensional :
  Extensionality.isWeaklyExtensional (Strict {ℓ})
Strict-extensional =
  Extensionality.≺Equiv→≡→isWeaklyExtensional
    Strict
    Carrier-isSet
    Strict-isProp
    extensional-path

isWoset : Woset.IsWoset (Strict {ℓ})
isWoset =
  Woset.iswoset
    Carrier-isSet
    Strict-isProp
    Strict-wf
    Strict-extensional
    Strict-trans

-- H_ℕ(ℓ) as a Cubical well-order: carrier at lsuc ℓ, relation at ℓ.  It
-- uses no excluded middle and no choice.

NatHartogs : (level : Level) → Woset.Woset (lsuc level) level
NatHartogs level =
  Carrier level
  Cubical.,
  Woset.wosetstr Strict isWoset

------------------------------------------------------------------------
-- Principal segments

principalCarrierIso :
    (position : Carrier ℓ)
  → Iso.Iso
      (Cubical.fst
        (Simulation._↓_ (NatHartogs ℓ) position))
      (Cubical.fst (Cubical.fst position))
principalCarrierIso position = record
  { fun = λ entry →
      Cubical.fst (Cubical.snd entry)
  ; inv = λ point →
      ( ( Simulation._↓_ (Cubical.fst position) point
        Cubical.,
          principal-embeds
            (Simulation._↓_ (Cubical.fst position) point)
            (Cubical.fst position)
            (Simulation.↓Decreasing (Cubical.fst position) point)
            (Cubical.snd position)
        )
      Cubical.,
        Simulation.↓Decreasing (Cubical.fst position) point
      )
  ; rightInv = λ _ → Cubical.refl
  ; leftInv = λ entry →
      SigmaProperties.Σ≡Prop
        (λ candidate →
          Simulation.isPropValued≺
            (Cubical.fst candidate)
            (Cubical.fst position))
        (SigmaProperties.Σ≡Prop
          (λ _ → NatCountability.isPropMerelyEmbedsInNat)
          (Equiv.equivFun
            (Woset.WosetPath
              (Simulation._↓_ (Cubical.fst position)
                (Cubical.fst (Cubical.snd entry)))
              (Cubical.fst (Cubical.fst entry)))
            (Cubical.snd (Cubical.snd entry))))
  }

principalCarrierEquiv :
    (position : Carrier ℓ)
  → Equiv._≃_
      (Cubical.fst
        (Simulation._↓_ (NatHartogs ℓ) position))
      (Cubical.fst (Cubical.fst position))
principalCarrierEquiv position =
  Iso.isoToEquiv (principalCarrierIso position)

-- H_ℕ(ℓ) ↓ (α , c) ≃ α: a predecessor (β , _) with β ≺ α goes to the point
-- bounding β, and x : |α| goes to α ↓ x, which embeds into ℕ by downward
-- closure.

principalEquiv :
    (position : Carrier ℓ)
  → Woset.WosetEquiv
      (Simulation._↓_ (NatHartogs ℓ) position)
      (Cubical.fst position)
principalEquiv {ℓ} position =
  carrier-equivalence
  Cubical.,
  Woset.iswosetequiv
    (λ left right →
      Equiv.propBiimpl→Equiv
        (Woset.IsWoset.is-prop-valued
          (Woset.WosetStr.isWoset
            (Cubical.snd (Simulation._↓_ (NatHartogs ℓ) position)))
          left right)
        (Woset.IsWoset.is-prop-valued
          (Woset.WosetStr.isWoset (Cubical.snd (Cubical.fst position)))
          (Equiv.equivFun carrier-equivalence left)
          (Equiv.equivFun carrier-equivalence right))
        (relation-forward left right)
        (relation-backward left right))
  where
    ordinal : Woset.Woset ℓ ℓ
    ordinal = Cubical.fst position

    carrier-equivalence =
      principalCarrierEquiv position

    relation-forward :
        (left right : Cubical.fst
          (Simulation._↓_ (NatHartogs ℓ) position))
      → Woset.WosetStr._≺_
          (Cubical.snd (Simulation._↓_ (NatHartogs ℓ) position))
          left right
      → Woset.WosetStr._≺_ (Cubical.snd ordinal)
          (Equiv.equivFun carrier-equivalence left)
          (Equiv.equivFun carrier-equivalence right)
    relation-forward left right left<right =
      Simulation.↓Respects≺⁻ ordinal
        (Cubical.fst (Cubical.snd left))
        (Cubical.fst (Cubical.snd right))
        (Simulation.≺RespectsEquiv
          (Woset.invWosetEquiv (Cubical.snd (Cubical.snd left)))
          (Woset.invWosetEquiv (Cubical.snd (Cubical.snd right)))
          left<right)

    relation-backward :
        (left right : Cubical.fst
          (Simulation._↓_ (NatHartogs ℓ) position))
      → Woset.WosetStr._≺_ (Cubical.snd ordinal)
          (Equiv.equivFun carrier-equivalence left)
          (Equiv.equivFun carrier-equivalence right)
      → Woset.WosetStr._≺_
          (Cubical.snd (Simulation._↓_ (NatHartogs ℓ) position))
          left right
    relation-backward left right left<right =
      Simulation.≺RespectsEquiv
        (Cubical.snd (Cubical.snd left))
        (Cubical.snd (Cubical.snd right))
        (Simulation.↓Respects≺ ordinal
          (Cubical.fst (Cubical.snd left))
          (Cubical.fst (Cubical.snd right))
          left<right)

------------------------------------------------------------------------
-- The cut

strict→embeds :
    (ordinal : Woset.Woset ℓ ℓ)
  → Simulation._≺_ ordinal (NatHartogs ℓ)
  → NatCountability.MerelyEmbedsInNat (Cubical.fst ordinal)
strict→embeds ordinal strict =
  embeds-≃
    (Cubical.fst
      (Woset.compWosetEquiv
        (Woset.invWosetEquiv
          (principalEquiv (Cubical.fst strict)))
        (Cubical.snd strict)))
    (Cubical.snd (Cubical.fst strict))

embeds→strict :
    (ordinal : Woset.Woset ℓ ℓ)
  → NatCountability.MerelyEmbedsInNat (Cubical.fst ordinal)
  → Simulation._≺_ ordinal (NatHartogs ℓ)
embeds→strict ordinal countable =
  (ordinal Cubical., countable)
  Cubical.,
  principalEquiv (ordinal Cubical., countable)

-- α ≺ H_ℕ(ℓ) ⇔ ‖|α| ↪ ℕ‖, for every small well-order α.

strict-cut :
    (ordinal : Woset.Woset ℓ ℓ)
  → (Simulation._≺_ ordinal (NatHartogs ℓ)
      → NatCountability.MerelyEmbedsInNat (Cubical.fst ordinal))
    Sigma.×
    (NatCountability.MerelyEmbedsInNat (Cubical.fst ordinal)
      → Simulation._≺_ ordinal (NatHartogs ℓ))
strict-cut ordinal =
  strict→embeds ordinal
  Cubical.,
  embeds→strict ordinal
