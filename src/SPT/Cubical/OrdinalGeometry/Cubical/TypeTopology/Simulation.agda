{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Simulation where

-- Simulations across the bridge between Cubical well-ordered sets and
-- TypeTopology's ordinals (Ordinals.Type).
--
-- The reverse bridge woset : Ordinal ℓ → Woset ℓ ℓ keeps the carrier and
-- the relation. Its carrier is a set by Hedberg's argument: identity of
-- points maps into agreement of lower cones, a proposition, and back by
-- extensionality, so every identity type is collapsible. Simulations
-- A ≼ woset β correspond to TypeTopology simulations
-- toOrdinal A ⊴ β, in both directions; identities of
-- points are translated, nothing else changes.

open import Agda.Primitive using (Level; _⊔_)

import SPT.Cubical.TypeTopology.MLTT.Sigma-Type as TypeTopologySigma
import SPT.Cubical.TypeTopology.Ordinals.Maps as TypeTopologyMaps
import SPT.Cubical.TypeTopology.Ordinals.Notions as TypeTopologyNotions
open import SPT.Cubical.TypeTopology.Ordinals.Type using (Ordinal)

open import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Bridge using
  ( toOrdinal; path→＝
  ; ＝→path
  )

import Cubical.Data.Sigma.Base as CubicalSigma
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Prelude as Cubical
import Cubical.Induction.WellFounded as CubicalAcc
import Cubical.Relation.Binary.Extensionality as Extensionality
import Cubical.Relation.Nullary as Nullary
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

open TypeTopologySigma.Σ using (pr₁; pr₂)

private
  variable
    ℓ ℓ′ : Level

-- TypeTopology's order of ordinals by simulations. It is the relation
-- _⊴_ of Ordinals.OrdinalOfOrdinals, whose module is parameterized by
-- univalence; the definition does not use the parameter.
_⊴_ : Ordinal ℓ → Ordinal ℓ′ → Set (ℓ ⊔ ℓ′)
α ⊴ β = TypeTopologySigma.Σ λ f → TypeTopologyMaps.is-simulation α β f

private
  accessible : {X : Set ℓ} {R : X → X → Set ℓ} {x : X}
    → TypeTopologyNotions.is-accessible R x → CubicalAcc.Acc R x
  accessible (TypeTopologyNotions.acc σ) =
    CubicalAcc.acc λ y r → accessible (σ y r)

-- Mathematical shape: Ordinal(ℓ) → Woset(ℓ, ℓ), the identity on carrier
-- and relation. Nonclaim: woset is not shown inverse to
-- toOrdinal beyond carrier and relation.
woset : Ordinal ℓ → Woset.Woset ℓ ℓ
woset {ℓ} β =
  Cubical._,_ X
    (Woset.wosetstr _<_
      (Woset.iswoset set prop
        (λ x → accessible (pr₁ (pr₂ well-order) x))
        (Extensionality.≺×→≡→isWeaklyExtensional _<_ set prop
          extensional)
        (pr₂ (pr₂ (pr₂ well-order)))))
  where
  X : Set ℓ
  X = pr₁ β

  _<_ : X → X → Set ℓ
  _<_ = pr₁ (pr₂ β)

  well-order = pr₂ (pr₂ β)

  prop : (x y : X) → Cubical.isProp (x < y)
  prop x y p q = ＝→path (pr₁ well-order x y p q)

  -- Agreement of the lower cones of x and y.
  Agree : X → X → Set ℓ
  Agree x y =
    (z : X) → CubicalSigma._×_ (z < x → z < y) (z < y → z < x)

  extensional : (x y : X) → Agree x y → x Cubical.≡ y
  extensional x y c =
    ＝→path
      (pr₁ (pr₂ (pr₂ well-order)) x y
        (λ z → Cubical.fst (c z)) (λ z → Cubical.snd (c z)))

  agree : {x y : X} → x Cubical.≡ y → Agree x y
  agree p z =
    Cubical._,_ (Cubical.subst (z <_) p)
      (Cubical.subst (z <_) (Cubical.sym p))

  agree-prop : (x y : X) → Cubical.isProp (Agree x y)
  agree-prop x y =
    HLevels.isPropΠ λ z →
      HLevels.isProp× (HLevels.isPropΠ λ _ → prop z y)
        (HLevels.isPropΠ λ _ → prop z x)

  set : Cubical.isSet X
  set =
    Nullary.Collapsible≡→isSet λ x y →
      Cubical._,_ (λ p → extensional x y (agree p))
        (λ p q →
          Cubical.cong (extensional x y)
            (agree-prop x y (agree p) (agree q)))

-- A simulation into woset β is a TypeTopology simulation into β.
to : (A : Woset.Woset ℓ ℓ) (β : Ordinal ℓ)
  → A Simulation.≼ woset β
  → toOrdinal A ⊴ β
to A β g =
  TypeTopologySigma._,_ (Cubical.fst g)
    (TypeTopologySigma._,_
      (λ x y r →
        let fib = Cubical.snd (Cubical.snd g) x y r
        in TypeTopologySigma._,_ (Cubical.fst (Cubical.fst fib))
             (TypeTopologySigma._,_ (Cubical.snd (Cubical.fst fib))
               (path→＝ (Cubical.snd fib))))
      (Cubical.fst (Cubical.snd g)))

-- A TypeTopology simulation into β is a simulation into woset β; its
-- initial-segment witnesses are already exact.
from : (A : Woset.Woset ℓ ℓ) (β : Ordinal ℓ)
  → toOrdinal A ⊴ β
  → A Simulation.≼ woset β
from A β g =
  Cubical._,_ (pr₁ g)
    (Cubical._,_ (pr₂ (pr₂ g))
      (λ x y r →
        let s = pr₁ (pr₂ g) x y r
        in Cubical._,_ (Cubical._,_ (pr₁ s) (pr₁ (pr₂ s)))
             (＝→path (pr₂ (pr₂ s)))))

-- Simulations of Cubical well-ordered sets are TypeTopology simulations
-- of their images: woset (toOrdinal B) has the carrier
-- and the relation of B.
simulation : (A B : Woset.Woset ℓ ℓ)
  → A Simulation.≼ B
  → toOrdinal A ⊴ toOrdinal B
simulation A B = to A (toOrdinal B)

-- woset is a section of toOrdinal: the round trip keeps
-- the carrier and the relation, so the identity is a Woset equivalence.
section : (A : Woset.Woset ℓ ℓ)
  → woset (toOrdinal A) Cubical.≡ A
section A =
  Equiv.equivFun (Woset.WosetPath (woset (toOrdinal A)) A)
    (Cubical._,_ (Equiv.idEquiv (Cubical.fst A))
      (Woset.iswosetequiv λ _ _ → Equiv.idEquiv _))
