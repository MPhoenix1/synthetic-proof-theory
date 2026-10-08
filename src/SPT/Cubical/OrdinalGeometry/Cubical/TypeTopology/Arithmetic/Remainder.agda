{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Arithmetic.Remainder
  where

-- Rows 13 and 14 on the reflected side, with TypeTopology's arithmetic
-- (Kraus, Nordvall Forsberg and Xu, Definition 15 and Lemma 24):
-- - subtraction: along an initial map P → Q with decided image,
--   P′ +ₒ R′ ≃ Q′ for the remainder R (Arithmetic.Subtraction);
-- - division: for a division of P by D, (D′ ×ₒ Q′) +ₒ R′ ≃ P′ with
--   R′ ≺ D′ (Arithmetic.Division).
-- Both are the presented theorems carried by the comparisons of
-- TypeTopology.Arithmetic. For Ord, subtraction is equivalent to
-- LEM (their Theorem 62); here its datum is the decided image.

open import Agda.Primitive using (Level)

import SPT.Cubical.TypeTopology.MLTT.Plus as TypeTopologyPlus
open import SPT.Cubical.TypeTopology.Ordinals.Type using (Ordinal)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Arithmetic.Subtraction as Subtraction
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Division using (Division)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Multiplication using (_·_)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType using
  (orderType; orderType-equivalence)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Simulation using
  (segment)
open import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Bridge using
  (toOrdinal)
open import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Simulation
  using (woset)
open import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Arithmetic
  using (_+ₒ_; _×ₒ_; ordinal; sum; product)

import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.Isomorphism as Isomorphism
import Cubical.Foundations.Prelude as Cubical
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

private
  variable
    ℓ : Level

-- Mathematical shape: A ≃ β → A′ +ₒ γ ≃ β +ₒ γ, the left summand moved
-- along the equivalence.
left : (A : Woset.Woset ℓ ℓ) (β γ : Ordinal ℓ)
  → Woset.WosetEquiv A (woset β)
  → Woset.WosetEquiv (woset (toOrdinal A +ₒ γ))
      (woset (β +ₒ γ))
left A β γ e =
  Cubical._,_
    (Isomorphism.isoToEquiv
      (Isomorphism.iso forth back forth-back back-forth))
    (Woset.iswosetequiv order)
  where
  f = Equiv.equivFun (Cubical.fst e)
  g = Equiv.invEq (Cubical.fst e)

  forth : Cubical.fst (woset (toOrdinal A +ₒ γ))
    → Cubical.fst (woset (β +ₒ γ))
  forth (TypeTopologyPlus.inl a) = TypeTopologyPlus.inl (f a)
  forth (TypeTopologyPlus.inr c) = TypeTopologyPlus.inr c

  back : Cubical.fst (woset (β +ₒ γ))
    → Cubical.fst (woset (toOrdinal A +ₒ γ))
  back (TypeTopologyPlus.inl b) = TypeTopologyPlus.inl (g b)
  back (TypeTopologyPlus.inr c) = TypeTopologyPlus.inr c

  forth-back : (x : Cubical.fst (woset (β +ₒ γ)))
    → forth (back x) Cubical.≡ x
  forth-back (TypeTopologyPlus.inl b) =
    Cubical.cong TypeTopologyPlus.inl (Equiv.secEq (Cubical.fst e) b)
  forth-back (TypeTopologyPlus.inr c) = Cubical.refl

  back-forth : (x : Cubical.fst (woset (toOrdinal A +ₒ γ)))
    → back (forth x) Cubical.≡ x
  back-forth (TypeTopologyPlus.inl a) =
    Cubical.cong TypeTopologyPlus.inl (Equiv.retEq (Cubical.fst e) a)
  back-forth (TypeTopologyPlus.inr c) = Cubical.refl

  order : (x y : Cubical.fst (woset (toOrdinal A +ₒ γ)))
    → Equiv._≃_
        (Woset.WosetStr._≺_
          (Cubical.snd (woset (toOrdinal A +ₒ γ))) x y)
        (Woset.WosetStr._≺_ (Cubical.snd (woset (β +ₒ γ)))
          (forth x) (forth y))
  order (TypeTopologyPlus.inl a) (TypeTopologyPlus.inl a′) =
    Woset.IsWosetEquiv.pres≺ (Cubical.snd e) a a′
  order (TypeTopologyPlus.inl a) (TypeTopologyPlus.inr c) = Equiv.idEquiv _
  order (TypeTopologyPlus.inr c) (TypeTopologyPlus.inl a) = Equiv.idEquiv _
  order (TypeTopologyPlus.inr c) (TypeTopologyPlus.inr c′) =
    Equiv.idEquiv _

-- Mathematical shape: for f : P ≤ Q with decided image and remainder R,
-- P′ +ₒ R′ ≃ Q′.
subtraction : {P Q : 𝒫 ℓ} (f : Maps.Initial P Q)
  (d : Subtraction.Decided f)
  → Woset.WosetEquiv
      (woset (ordinal P +ₒ ordinal (Subtraction.remainder f d)))
      (orderType Q)
subtraction {P = P} f d =
  Woset.compWosetEquiv
    (Woset.invWosetEquiv (sum P (Subtraction.remainder f d)))
    (orderType-equivalence (Subtraction.equation f d))

-- Mathematical shape: for a division of P by D with quotient Q and
-- remainder R, (D′ ×ₒ Q′) +ₒ R′ ≃ P′.
division : {P D : 𝒫 ℓ} (a : Division P D)
  → Woset.WosetEquiv
      (woset ((ordinal D ×ₒ ordinal (Division.quotient a))
        +ₒ ordinal (Division.remainder a)))
      (orderType P)
division {D = D} a =
  Woset.compWosetEquiv
    (Woset.invWosetEquiv
      (left (orderType (D · Q)) (ordinal D ×ₒ ordinal Q)
        (ordinal R) (product D Q)))
    (Woset.compWosetEquiv
      (Woset.invWosetEquiv (sum (D · Q) R))
      (orderType-equivalence (Division.equation a)))
  where
  Q = Division.quotient a
  R = Division.remainder a

-- The remainder of a division lies strictly below the divisor.
remainder-below : {P D : 𝒫 ℓ} (a : Division P D)
  → orderType (Division.remainder a)
      Simulation.≺ orderType D
remainder-below a = segment (Division.below a)
