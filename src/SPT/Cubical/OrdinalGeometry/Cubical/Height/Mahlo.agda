{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Height.Mahlo where

-- Ord(ℓ) is a Mahlo cardinal in the function form, under excluded middle
-- and choice, given the Mahlo rule: a reflector of the universe of level
-- ℓ.  For f : Ord ℓ → Ord ℓ, the operator Ψ_f lists, for every member of
-- its argument and every Boolean-coded well-order W on a subset of it,
-- the carrier of f W (operator).  Reflect Ψ_f paired with the labels of
-- the canonical height of β (Height.Ordinals.Mahlo); the rank κ of the
-- reflection (Height.Hartogs) lies above β (above), is closed under f,
--
--   α ≺ κ → f α ≺ κ                                         (closed),
--
-- and is inaccessible.  The child names β's carrier and every f W, and
-- under excluded middle every α ≺ κ is some coded W up to equivalence.

open import Agda.Primitive using (Level)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (tt)
import Relation.Binary.PropositionalEquality as Ordinary

import Cubical.Data.Equality.Conversion as EqualityConversion
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.Prelude as Cubical
import Cubical.Foundations.Univalence as Univalence
import Cubical.Functions.Embedding as Embedding
import Cubical.HITs.PropositionalTruncation as Truncation
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

import SPT.Cubical.Core.Mahlo.Specification as Mahlo
import SPT.Cubical.Core.Mahlo.Ambient as Ambient
open import SPT.Cubical.OrdinalGeometry.Height.Ordinals.Mahlo using
  (reflection; child; member)
open import SPT.Cubical.OrdinalGeometry.Cubical.Height.Rank using
  (canonical-height)
open import SPT.Cubical.OrdinalGeometry.Cubical.Height.Reflection using
  (reflection-rank)
open import SPT.Cubical.OrdinalGeometry.Cubical.Height.Hartogs using
  (embeds; strict; inaccessible)
open import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Countability using
  (ExcludedMiddle)
open import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Universe using
  (Embeds)
open import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Coded using
  (Coded; woset-of; encode)
open import SPT.Cubical.OrdinalGeometry.Cubical.Hartogs.Cardinal using
  (Choice; MahloOrdinals)

private
  variable
    ℓ : Level

-- Mathematical shape: Ψ_f (A , B) = (Σ (x : A). Coded (B x) , λ (x , W) →
-- |f W|).
operator : (Woset.Woset ℓ ℓ → Woset.Woset ℓ ℓ) → Ambient.Operator ℓ
operator f P =
  Cubical.Σ (Cubical.fst P) (λ x → Coded (Cubical.snd P x)) Cubical.,
  λ q → Cubical.fst (f (woset-of (Cubical.snd q)))

module _ (lem : ExcludedMiddle ℓ) (M : Mahlo.Mahlo (Ambient.formers ℓ))
  (f : Woset.Woset ℓ ℓ → Woset.Woset ℓ ℓ) (β : Woset.Woset ℓ ℓ) where

  private
    closure = child M (operator f) (canonical-height β)
    Decode = Mahlo.Closure.Decode closure

    -- The unit name, and the point of its decoding.
    unit = Mahlo.Closure.unit closure

    unit-point : Decode (Cubical.fst unit)
    unit-point = Ordinary.subst (λ X → X) (Ordinary.sym (Cubical.snd unit)) tt

    -- A type named in the child embeds into a child type.
    named : {X : Set ℓ} → Mahlo.Closure.Name closure X → Embeds Decode X
    named found =
      Truncation.∣ Cubical.fst found Cubical.,
        Embedding.Equiv→Embedding
          (Equiv.invEquiv
            (Univalence.pathToEquiv
              (EqualityConversion.eqToPath (Cubical.snd found)))) ∣₁

  -- The rank of the reflection of Ψ_f above β.
  point : Woset.Woset ℓ ℓ
  point = reflection-rank (reflection M (operator f) (canonical-height β))

  -- Mathematical shape: β ≺ κ.  The child names |β|, the root label of the
  -- canonical height of β.
  above : Simulation._≺_ β point
  above =
    strict (reflection M (operator f) (canonical-height β)) lem β
      (named
        (member M (operator f) (canonical-height β)
          (Cubical.fst unit Cubical., λ _ → Cubical.fst unit)
          (inj₂ (inj₁ tt))))

  -- Mathematical shape: α ≺ κ → f α ≺ κ.  α embeds into a child type, so
  -- it is a coded well-order W on a subset of it, and the child names
  -- |f W| as a member of Ψ_f at the child family with that one member.
  closed : (α : Woset.Woset ℓ ℓ)
    → Simulation._≺_ α point → Simulation._≺_ (f α) point
  closed α α<κ =
    Truncation.rec (Simulation.isPropValued≺ (f α) point)
      (λ found →
        let i = Cubical.fst found
            coded = encode lem α (Cubical.snd found)
            W = Cubical.fst coded
            fW<κ =
              strict (reflection M (operator f) (canonical-height β)) lem
                (f (woset-of W))
                (named
                  (member M (operator f) (canonical-height β)
                    (Cubical.fst unit Cubical., λ _ → i)
                    (inj₁ (unit-point Cubical., W))))
        in Cubical.subst (λ X → Simulation._≺_ (f X) point)
             (Cubical.sym
               (Equiv.equivFun (Woset.WosetPath α (woset-of W))
                 (Cubical.snd coded)))
             fW<κ)
      (embeds (reflection M (operator f) (canonical-height β)) lem α α<κ)

-- Mathematical shape: excluded middle, choice and a reflector make Ord(ℓ)
-- Mahlo: every f has inaccessible closure points above every β.
mahlo : ExcludedMiddle ℓ → Choice ℓ → Mahlo.Mahlo (Ambient.formers ℓ)
  → MahloOrdinals ℓ
mahlo lem choice M f β =
  point lem M f β Cubical.,
  (above lem M f β Cubical.,
    (inaccessible (reflection M (operator f) (canonical-height β)) lem choice
    Cubical., closed lem M f β))
