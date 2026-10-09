{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Ordinals.Lower where

-- Initial segments of the ordinal of ordinals cut out by a property.  A
-- lower property L of small well-orders is proposition-valued and holds of
-- every well-order below one it holds of.  The well-orders with L, ordered
-- by ≺, form a well-order
--
--   segment L = (Σ (α : Woset ℓ ℓ). L α , ≺),
--
-- whose principal segment at (α , _) is α (principal), so that
--
--   α ≺ segment L ⇔ L α                                  (cut).
--
-- Every small well-order with the same cut is equivalent to it (unique).
-- The ℕ-Hartogs well-order of Hartogs.Base is the case L α = ‖|α| ↪ ℕ‖.

open import Agda.Primitive using (Level; lsuc; _⊔_)

import Cubical.Data.Sigma.Base as Sigma
import Cubical.Data.Sigma.Properties as SigmaProperties
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Isomorphism as Iso
import Cubical.Foundations.Prelude as Cubical
import Cubical.Induction.WellFounded as WellFounded
import Cubical.Relation.Binary.Extensionality as Extensionality
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Ordinals using
  (segments→simulation)

private
  variable
    ℓ ℓ′ : Level

------------------------------------------------------------------------
-- Lower properties

-- A proposition-valued property of small well-orders, closed downward.
record Lower (ℓ ℓ′ : Level) : Set (lsuc ℓ ⊔ lsuc ℓ′) where
  field
    holds : Woset.Woset ℓ ℓ → Set ℓ′
    holds-prop : (α : Woset.Woset ℓ ℓ) → Cubical.isProp (holds α)
    holds-below : (α β : Woset.Woset ℓ ℓ)
      → Simulation._≺_ α β → holds β → holds α

open Lower public

------------------------------------------------------------------------
-- The well-order of the well-orders with the property

module _ (L : Lower ℓ ℓ′) where

  Carrier : Set (lsuc ℓ ⊔ ℓ′)
  Carrier = Cubical.Σ (Woset.Woset ℓ ℓ) (holds L)

  -- (α , _) < (β , _) when α ≺ β; the witnesses play no part.
  Strict : Carrier → Carrier → Set ℓ
  Strict smaller larger =
    Simulation._≺_ (Cubical.fst smaller) (Cubical.fst larger)

  private
    carrier-set : Cubical.isSet Carrier
    carrier-set = HLevels.isSetΣSndProp Woset.isSetWoset (holds-prop L)

    strict-prop : (x y : Carrier) → Cubical.isProp (Strict x y)
    strict-prop x y =
      Simulation.isPropValued≺ (Cubical.fst x) (Cubical.fst y)

    strict-wf : WellFounded.WellFounded Strict
    strict-wf (Cubical._,_ ordinal witness) =
      WellFounded.WFI.induction Simulation.isWellFounded≺
        {P = λ current → (h : holds L current)
          → WellFounded.Acc Strict (current Cubical., h)}
        (λ current smaller h →
          WellFounded.acc λ (Cubical._,_ predecessor h′) p →
            smaller predecessor p h′)
        ordinal witness

    strict-trans : (x y z : Carrier) → Strict x y → Strict y z → Strict x z
    strict-trans x y z =
      Simulation.isTrans≺ (Cubical.fst x) (Cubical.fst y) (Cubical.fst z)

    lower-equivalence : (x y : Carrier)
      → ((candidate : Carrier) →
          Strict candidate x Equiv.≃ Strict candidate y)
      → (candidate : Woset.Woset ℓ ℓ)
      → Simulation._≺_ candidate (Cubical.fst x) Equiv.≃
        Simulation._≺_ candidate (Cubical.fst y)
    lower-equivalence x y lower candidate =
      Equiv.propBiimpl→Equiv
        (Simulation.isPropValued≺ candidate (Cubical.fst x))
        (Simulation.isPropValued≺ candidate (Cubical.fst y))
        (λ below-x →
          Equiv.equivFun
            (lower (candidate Cubical.,
              holds-below L candidate (Cubical.fst x) below-x
                (Cubical.snd x)))
            below-x)
        (λ below-y →
          Equiv.invEq
            (lower (candidate Cubical.,
              holds-below L candidate (Cubical.fst y) below-y
                (Cubical.snd y)))
            below-y)

    extensional-path : (x y : Carrier)
      → ((candidate : Carrier) →
          Strict candidate x Equiv.≃ Strict candidate y)
      → x Cubical.≡ y
    extensional-path x y lower =
      SigmaProperties.Σ≡Prop (holds-prop L)
        (Extensionality.isWeaklyExtensional→≺Equiv→≡
          Simulation._≺_ Simulation.isWeaklyExtensional≺
          (Cubical.fst x) (Cubical.fst y)
          (lower-equivalence x y lower))

    laws : Woset.IsWoset Strict
    laws =
      Woset.iswoset carrier-set strict-prop strict-wf
        (Extensionality.≺Equiv→≡→isWeaklyExtensional Strict carrier-set
          strict-prop extensional-path)
        strict-trans

  -- Mathematical shape: segment L = (Σ (α : Woset ℓ ℓ). L α , ≺).
  segment : Woset.Woset (lsuc ℓ ⊔ ℓ′) ℓ
  segment = Carrier Cubical., Woset.wosetstr Strict laws

  ----------------------------------------------------------------------
  -- Principal segments

  private
    principal-iso : (x : Carrier)
      → Iso.Iso (Cubical.fst (Simulation._↓_ segment x))
          (Cubical.fst (Cubical.fst x))
    principal-iso x = record
      { fun = λ entry → Cubical.fst (Cubical.snd entry)
      ; inv = λ point →
          (Simulation._↓_ (Cubical.fst x) point Cubical.,
            holds-below L (Simulation._↓_ (Cubical.fst x) point)
              (Cubical.fst x) (Simulation.↓Decreasing (Cubical.fst x) point)
              (Cubical.snd x))
          Cubical., Simulation.↓Decreasing (Cubical.fst x) point
      ; rightInv = λ _ → Cubical.refl
      ; leftInv = λ entry →
          SigmaProperties.Σ≡Prop
            (λ candidate →
              Simulation.isPropValued≺ (Cubical.fst candidate)
                (Cubical.fst x))
            (SigmaProperties.Σ≡Prop (holds-prop L)
              (Equiv.equivFun
                (Woset.WosetPath
                  (Simulation._↓_ (Cubical.fst x)
                    (Cubical.fst (Cubical.snd entry)))
                  (Cubical.fst (Cubical.fst entry)))
                (Cubical.snd (Cubical.snd entry))))
      }

  -- Mathematical shape: segment L ↓ (α , _) ≃ α.  A predecessor (β , _)
  -- goes to the point of α bounding β, and x : |α| to α ↓ x.
  principal : (x : Carrier)
    → Woset.WosetEquiv (Simulation._↓_ segment x) (Cubical.fst x)
  principal x =
    carrier
    Cubical., Woset.makeIsWosetEquiv carrier forward backward
    where
      carrier = Iso.isoToEquiv (principal-iso x)

      forward : (u v : Cubical.fst (Simulation._↓_ segment x))
        → Woset.WosetStr._≺_ (Cubical.snd (Simulation._↓_ segment x)) u v
        → Woset.WosetStr._≺_ (Cubical.snd (Cubical.fst x))
            (Equiv.equivFun carrier u) (Equiv.equivFun carrier v)
      forward u v u<v =
        Simulation.↓Respects≺⁻ (Cubical.fst x)
          (Cubical.fst (Cubical.snd u)) (Cubical.fst (Cubical.snd v))
          (Simulation.≺RespectsEquiv
            (Woset.invWosetEquiv (Cubical.snd (Cubical.snd u)))
            (Woset.invWosetEquiv (Cubical.snd (Cubical.snd v)))
            u<v)

      backward : (u v : Cubical.fst (Cubical.fst x))
        → Woset.WosetStr._≺_ (Cubical.snd (Cubical.fst x)) u v
        → Woset.WosetStr._≺_ (Cubical.snd (Simulation._↓_ segment x))
            (Equiv.invEq carrier u) (Equiv.invEq carrier v)
      backward u v u<v =
        Simulation.↓Respects≺ (Cubical.fst x) u v u<v

  ----------------------------------------------------------------------
  -- The cut and uniqueness

  -- Mathematical shape: α ≺ segment L ⇔ L α.
  cut : (α : Woset.Woset ℓ ℓ)
    → (Simulation._≺_ α segment → holds L α)
      Sigma.× (holds L α → Simulation._≺_ α segment)
  cut α =
    (λ strict →
      Cubical.subst (holds L)
        (Equiv.equivFun
          (Woset.WosetPath (Cubical.fst (Cubical.fst strict)) α)
          (Woset.compWosetEquiv
            (Woset.invWosetEquiv (principal (Cubical.fst strict)))
            (Cubical.snd strict)))
        (Cubical.snd (Cubical.fst strict)))
    Cubical., λ h → (α Cubical., h) Cubical., principal (α Cubical., h)

  -- Mathematical shape: (Π α. α ≺ κ ⇔ L α) → κ ≃ segment L.  Each
  -- principal segment of either lies below the other, by the two cuts.
  unique : (κ : Woset.Woset ℓ ℓ)
    → ((α : Woset.Woset ℓ ℓ) →
        (Simulation._≺_ α κ → holds L α)
        Sigma.× (holds L α → Simulation._≺_ α κ))
    → Woset.WosetEquiv κ segment
  unique κ κ-cut =
    Simulation.isAntisym≼Equiv κ segment
      (segments→simulation {H = κ} {K = segment} λ k →
        Cubical.snd (cut (Simulation._↓_ κ k))
          (Cubical.fst (κ-cut (Simulation._↓_ κ k))
            (Simulation.↓Decreasing κ k)))
      (segments→simulation {H = segment} {K = κ} λ x →
        Simulation.≺RespectsEquivL κ (Woset.invWosetEquiv (principal x))
          (Cubical.snd (κ-cut (Cubical.fst x)) (Cubical.snd x)))
