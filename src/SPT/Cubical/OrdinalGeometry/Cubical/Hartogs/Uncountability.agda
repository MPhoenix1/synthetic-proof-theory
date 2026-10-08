{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Uncountability where

-- The carrier of H_ℕ(ℓ) lies one universe above the small well-orders it
-- collects, and the construction and its cut need no resizing.  Refuting an
-- embedding of that carrier into ℕ does: one-step propositional resizing
-- suffices, and excluded middle at lsuc ℓ provides it.

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Data.Nat using (ℕ)

import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Countability
  as NatCountability
import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Base as Hartogs
import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Specification
  as Specification

import Cubical.Data.Empty as Empty
import Cubical.Data.Sigma as Sigma
import Cubical.Data.Unit as Unit
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Prelude as Cubical
import Cubical.Foundations.Transport as Transport
import Cubical.Functions.Embedding as Embedding
import Cubical.Functions.Fibration as Fibration
import Cubical.HITs.PropositionalTruncation as Truncation
import Cubical.Induction.WellFounded as WellFounded
import Cubical.Relation.Binary.Extensionality as Extensionality
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation
import Cubical.Relation.Nullary as Nullary

------------------------------------------------------------------------
-- Propositional resizing

-- Resizing from level s to level t, as a hypothesis:
--
--   PropositionalResizing(s,t) = Π(P : Set s). isProp(P) → Σ(Q : Set t). Q ≃ P.

PropositionalResizing :
  (source target : Level) → Set (lsuc source ⊔ lsuc target)
PropositionalResizing source target =
  (proposition : Set source)
  → Cubical.isProp proposition
  → Cubical.Σ (Set target) (λ small → Equiv._≃_ small proposition)

------------------------------------------------------------------------
-- Well-foundedness of ≺ on Woset (lsuc ℓ) ℓ

-- Bounded simulation is well founded on Woset (lsuc ℓ) ℓ: a predecessor of
-- A is a principal segment A ↓ a, and recursion follows the order of A.

strict-wf-step :
    {level : Level}
  → WellFounded.WellFounded
      (Simulation._≺_
        {ℓa = lsuc level}
        {ℓa' = level})
strict-wf-step ordinal =
  WellFounded.acc
    (λ smaller (point Cubical., principal-equivalence) →
      Cubical.subst
        (WellFounded.Acc Simulation._≺_)
        (Equiv.equivFun
          (Woset.WosetPath
            (Simulation._↓_ ordinal point)
            smaller)
          principal-equivalence)
        (principal-accessible ordinal point))
  where
    principal-accessible :
        {level : Level}
      → (current : Woset.Woset (lsuc level) level)
      → (point : Cubical.fst current)
      → WellFounded.Acc
          Simulation._≺_
          (Simulation._↓_ current point)
    principal-accessible current =
      WellFounded.WFI.induction
        (Woset.IsWoset.is-well-founded
          (Woset.WosetStr.isWoset (Cubical.snd current)))
        (λ point smaller →
          WellFounded.acc
            (λ ordinal
              ((predecessor Cubical., predecessor<point)
                Cubical., principal-equivalence) →
              Cubical.subst
                (WellFounded.Acc Simulation._≺_)
                (Cubical._∙_
                  (Cubical.sym
                    (Simulation.↓Absorb current point predecessor
                      predecessor<point))
                  (Equiv.equivFun
                    (Woset.WosetPath _ ordinal)
                    principal-equivalence))
                (smaller predecessor predecessor<point)))

private
  abstract
    strict-wf-step-opaque :
        {level : Level}
      → WellFounded.WellFounded
          (Simulation._≺_
            {ℓa = lsuc level}
            {ℓa' = level})
    strict-wf-step-opaque =
      strict-wf-step

-- Hence no well-order A satisfies A ≺ A.

abstract
  strict-irrefl-step :
      {level : Level}
    → (ordinal : Woset.Woset (lsuc level) level)
    → Simulation._≺_ ordinal ordinal
    → Empty.⊥
  strict-irrefl-step {level} ordinal =
    descend ordinal
      (strict-wf-step-opaque ordinal)
    where
      descend :
          (current : Woset.Woset (lsuc level) level)
        → WellFounded.Acc
            (Simulation._≺_
              {ℓa = lsuc level}
              {ℓa' = level})
            current
        → Simulation._≺_ current current
        → Empty.⊥
      descend current (WellFounded.acc smaller) strict-self =
        descend current (smaller current strict-self) strict-self

------------------------------------------------------------------------
-- The resized image of an embedding

module _
  {level : Level}
  (resize : PropositionalResizing (lsuc level) level)
  (carrier-embedding :
    Embedding._↪_ (Hartogs.Carrier level) ℕ)
  where

  private
    embedding-function : Hartogs.Carrier level → ℕ
    embedding-function = Cubical.fst carrier-embedding

    abstract
      resized-fiber :
          (index : ℕ)
        → Cubical.Σ
            (Set level)
            (λ small →
              Equiv._≃_
                small
                (Equiv.fiber embedding-function index))
      resized-fiber index =
        resize
          (Equiv.fiber embedding-function index)
          (Embedding.isEmbedding→hasPropFibers
            (Cubical.snd carrier-embedding)
            index)

    SmallImage : Set level
    SmallImage =
      Cubical.Σ ℕ (λ index → Cubical.fst (resized-fiber index))

    abstract
      hartogsCarrier-smallImage-equivalence :
        Equiv._≃_ (Hartogs.Carrier level) SmallImage
      hartogsCarrier-smallImage-equivalence =
        Equiv.compEquiv
          (Fibration.totalEquiv embedding-function)
          (Equiv.invEquiv
            (Sigma.Σ-cong-equiv-snd
              (λ index → Cubical.snd (resized-fiber index))))

    SmallImageStrict : SmallImage → SmallImage → Set level
    SmallImageStrict left right =
      Hartogs.Strict
        (Equiv.invEq hartogsCarrier-smallImage-equivalence left)
        (Equiv.invEq hartogsCarrier-smallImage-equivalence right)

    abstract
      hartogs-smallImage-relation-equivalence :
          (left right : Hartogs.Carrier level)
        → Equiv._≃_
            (Hartogs.Strict left right)
            (SmallImageStrict
              (Equiv.equivFun
                hartogsCarrier-smallImage-equivalence left)
              (Equiv.equivFun
                hartogsCarrier-smallImage-equivalence right))
      hartogs-smallImage-relation-equivalence left right =
        Equiv.compEquiv
          (Transport.substEquiv
            (λ candidate → Hartogs.Strict candidate right)
            (Cubical.sym
              (Equiv.retEq hartogsCarrier-smallImage-equivalence left)))
          (Transport.substEquiv
            (Hartogs.Strict
              (Equiv.invEq hartogsCarrier-smallImage-equivalence
                (Equiv.equivFun
                  hartogsCarrier-smallImage-equivalence left)))
            (Cubical.sym
              (Equiv.retEq hartogsCarrier-smallImage-equivalence right)))

    abstract
      smallImage-is-set : Cubical.isSet SmallImage
      smallImage-is-set =
        HLevels.isOfHLevelRespectEquiv
          2
          hartogsCarrier-smallImage-equivalence
          Hartogs.Carrier-isSet

      smallImageStrict-is-prop-valued :
          (left right : SmallImage)
        → Cubical.isProp (SmallImageStrict left right)
      smallImageStrict-is-prop-valued left right =
        Hartogs.Strict-isProp
          (Equiv.invEq hartogsCarrier-smallImage-equivalence left)
          (Equiv.invEq hartogsCarrier-smallImage-equivalence right)

    smallImageAccessibility :
        (point : SmallImage)
      → WellFounded.Acc
          Hartogs.Strict
          (Equiv.invEq hartogsCarrier-smallImage-equivalence point)
      → WellFounded.Acc SmallImageStrict point
    smallImageAccessibility point (WellFounded.acc smaller) =
      WellFounded.acc
        (λ predecessor predecessor<point →
          smallImageAccessibility predecessor
            (smaller
              (Equiv.invEq
                hartogsCarrier-smallImage-equivalence predecessor)
              predecessor<point))

    abstract
      smallImageStrict-well-founded :
        WellFounded.WellFounded SmallImageStrict
      smallImageStrict-well-founded point =
        smallImageAccessibility point
          (Hartogs.Strict-wf
            (Equiv.invEq hartogsCarrier-smallImage-equivalence point))

    abstract
      smallImage-predecessors :
          (source-predecessor : Hartogs.Carrier level)
        → (target : SmallImage)
        → Equiv._≃_
            (Hartogs.Strict
              source-predecessor
              (Equiv.invEq hartogsCarrier-smallImage-equivalence target))
            (SmallImageStrict
              (Equiv.equivFun
                hartogsCarrier-smallImage-equivalence source-predecessor)
              target)
      smallImage-predecessors source-predecessor target =
        Transport.substEquiv
          (λ candidate →
            Hartogs.Strict candidate
              (Equiv.invEq hartogsCarrier-smallImage-equivalence target))
          (Cubical.sym
            (Equiv.retEq
              hartogsCarrier-smallImage-equivalence source-predecessor))

    abstract
      smallImageStrict-weakly-extensional :
        Extensionality.isWeaklyExtensional SmallImageStrict
      smallImageStrict-weakly-extensional =
        Extensionality.≺Equiv→≡→isWeaklyExtensional
          SmallImageStrict
          smallImage-is-set
          smallImageStrict-is-prop-valued
          (λ left right lower-cones →
            Embedding.isEmbedding→Inj
              (Cubical.snd
                (Embedding.Equiv→Embedding
                  (Equiv.invEquiv
                    hartogsCarrier-smallImage-equivalence)))
              left right
              (Extensionality.isWeaklyExtensional→≺Equiv→≡
                Hartogs.Strict
                Hartogs.Strict-extensional
                (Equiv.invEq hartogsCarrier-smallImage-equivalence left)
                (Equiv.invEq hartogsCarrier-smallImage-equivalence right)
                (λ source-predecessor →
                  Equiv.compEquiv
                    (smallImage-predecessors
                      source-predecessor left)
                    (Equiv.compEquiv
                      (lower-cones
                        (Equiv.equivFun
                          hartogsCarrier-smallImage-equivalence
                          source-predecessor))
                      (Equiv.invEquiv
                        (smallImage-predecessors
                          source-predecessor right))))))

      smallImageStrict-transitive :
          (lower middle upper : SmallImage)
        → SmallImageStrict lower middle
        → SmallImageStrict middle upper
        → SmallImageStrict lower upper
      smallImageStrict-transitive lower middle upper =
        Hartogs.Strict-trans
          (Equiv.invEq hartogsCarrier-smallImage-equivalence lower)
          (Equiv.invEq hartogsCarrier-smallImage-equivalence middle)
          (Equiv.invEq hartogsCarrier-smallImage-equivalence upper)

      smallImageStrict-is-woset : Woset.IsWoset SmallImageStrict
      smallImageStrict-is-woset =
        Woset.iswoset
          smallImage-is-set
          smallImageStrict-is-prop-valued
          smallImageStrict-well-founded
          smallImageStrict-weakly-extensional
          smallImageStrict-transitive

    SmallHartogsCopy : Woset.Woset level level
    SmallHartogsCopy =
      SmallImage
      Cubical., Woset.wosetstr
          SmallImageStrict
          smallImageStrict-is-woset

    abstract
      hartogs-small-copy-equivalence :
        Woset.WosetEquiv (Hartogs.NatHartogs level) SmallHartogsCopy
      hartogs-small-copy-equivalence =
        hartogsCarrier-smallImage-equivalence
        Cubical., Woset.iswosetequiv
          hartogs-smallImage-relation-equivalence

    smallImageFiber-is-prop :
        (index : ℕ)
      → Cubical.isProp (Cubical.fst (resized-fiber index))
    smallImageFiber-is-prop index =
      HLevels.isOfHLevelRespectEquiv
        1
        (Equiv.invEquiv (Cubical.snd (resized-fiber index)))
        (Embedding.isEmbedding→hasPropFibers
          (Cubical.snd carrier-embedding)
          index)

    small-copy-merely-embeds-in-nat :
      NatCountability.MerelyEmbedsInNat SmallImage
    small-copy-merely-embeds-in-nat =
      Truncation.∣
        Embedding.EmbeddingΣProp smallImageFiber-is-prop
      ∣₁

    abstract
      small-copy-strict-hartogs :
        Simulation._≺_ SmallHartogsCopy (Hartogs.NatHartogs level)
      small-copy-strict-hartogs =
        Hartogs.embeds→strict
          SmallHartogsCopy
          small-copy-merely-embeds-in-nat

      natHartogs-strict-self :
        Simulation._≺_
          (Hartogs.NatHartogs level)
          (Hartogs.NatHartogs level)
      natHartogs-strict-self =
        Simulation.≺RespectsEquivL
          (Hartogs.NatHartogs level)
          (Woset.invWosetEquiv hartogs-small-copy-equivalence)
          small-copy-strict-hartogs

  abstract
    natHartogs-carrier-not-embed-into-nat : Empty.⊥
    natHartogs-carrier-not-embed-into-nat =
      strict-irrefl-step
        (Hartogs.NatHartogs level)
        natHartogs-strict-self

------------------------------------------------------------------------
-- The carrier of H_ℕ does not embed into ℕ

-- PropositionalResizing(lsuc ℓ,ℓ) → ¬ ‖|H_ℕ(ℓ)| ↪ ℕ‖.  Resizing the fibers
-- of an embedding gives a small copy of H_ℕ(ℓ) that embeds into ℕ; by the
-- cut it lies strictly below H_ℕ(ℓ), and being equivalent to it, gives
-- H_ℕ(ℓ) ≺ H_ℕ(ℓ).

not-embeds :
    {level : Level}
  → PropositionalResizing (lsuc level) level
  → NatCountability.MerelyEmbedsInNat
      (Cubical.fst (Hartogs.NatHartogs level))
  → Empty.⊥
not-embeds resize =
  Truncation.rec
    Empty.isProp⊥
    (λ embedding →
      natHartogs-carrier-not-embed-into-nat resize embedding)

------------------------------------------------------------------------
-- Under excluded middle

-- ExcludedMiddle(lsuc ℓ) → ExcludedMiddle(ℓ), by lifting propositions.

excludedMiddle-lower :
    {level : Level}
  → NatCountability.ExcludedMiddle (lsuc level)
  → NatCountability.ExcludedMiddle level
excludedMiddle-lower {level} excluded-middle
    proposition proposition-is-prop
  with excluded-middle
    (Cubical.Lift {j = lsuc level} proposition)
    (λ left right →
      Cubical.liftExt
        (proposition-is-prop
          (Cubical.lower left)
          (Cubical.lower right)))
... | Nullary.yes lifted-witness =
  Nullary.yes (Cubical.lower lifted-witness)
... | Nullary.no lifted-refutation =
  Nullary.no (λ witness → lifted-refutation (Cubical.lift witness))

-- ExcludedMiddle(lsuc ℓ) → PropositionalResizing(lsuc ℓ,ℓ): a decided
-- proposition is equivalent to the unit or the empty type at ℓ.

excludedMiddle→resizing :
    {level : Level}
  → NatCountability.ExcludedMiddle (lsuc level)
  → PropositionalResizing (lsuc level) level
excludedMiddle→resizing
    {level} excluded-middle proposition proposition-is-prop
  with excluded-middle proposition proposition-is-prop
... | Nullary.yes witness =
  Unit.Unit* {level}
  Cubical., Equiv.propBiimpl→Equiv
    Unit.isPropUnit*
    proposition-is-prop
    (λ _ → witness)
    (λ _ → Unit.tt*)
... | Nullary.no refutation =
  Empty.⊥* {level}
  Cubical., Equiv.propBiimpl→Equiv
    Empty.isProp⊥*
    proposition-is-prop
    Empty.rec*
    (λ witness → Empty.rec (refutation witness))

-- ExcludedMiddle(lsuc ℓ) → ¬ ‖|H_ℕ(ℓ)| ↪ ℕ‖.

classical-not-embeds :
    {level : Level}
  → NatCountability.ExcludedMiddle (lsuc level)
  → NatCountability.MerelyEmbedsInNat
      (Cubical.fst (Hartogs.NatHartogs level))
  → Empty.⊥
classical-not-embeds excluded-middle =
  not-embeds
    (excludedMiddle→resizing excluded-middle)

-- PropositionalResizing(lsuc ℓ,ℓ) → IsHartogs(H_ℕ(ℓ)).

natHartogs-isHartogs :
    {level : Level}
  → PropositionalResizing (lsuc level) level
  → Specification.IsHartogs
      (Hartogs.NatHartogs level)
natHartogs-isHartogs resize =
  Specification.isHartogs
    Specification.natHartogs-isHartogsCut
    (not-embeds resize)

-- ExcludedMiddle(lsuc ℓ) → IsHartogs(H_ℕ(ℓ)).

classical-isHartogs :
    {level : Level}
  → NatCountability.ExcludedMiddle (lsuc level)
  → Specification.IsHartogs
      (Hartogs.NatHartogs level)
classical-isHartogs excluded-middle =
  natHartogs-isHartogs
    (excludedMiddle→resizing excluded-middle)
