{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Simulation where

-- Initial maps and proper principal segments of presentations, read on
-- their quotient order types.
--
-- An initial map f : P → Q descends to the class map [x] ↦ [f x]. It is
-- monotone and reflecting, and the lower law of f lifts every predecessor
-- of an image class, so the class map is a simulation
-- ord(P) ≼ ord(Q). A segment P ⊂ Q with
-- ceiling c identifies ord(P) with the principal segment of
-- ord(Q) below [c], so it is a bounded simulation ≺.

open import Agda.Primitive using (Level)
open import Data.Product using (_,_)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType using
  ( Class; Less; orderType
  ; Less-isProp
  ; Less-intro
  ; Less-witness
  )

import Cubical.Data.Sigma.Properties as SigmaProperties
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Prelude as Cubical
import Cubical.Functions.Embedding as Embedding
import Cubical.Functions.Surjection as Surjection
import Cubical.HITs.PropositionalTruncation as Truncation
import Cubical.HITs.SetQuotients as Quotient
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

private
  variable
    ℓ : Level
    P Q : 𝒫 ℓ

------------------------------------------------------------------------
-- Initial maps

-- The class map [x] ↦ [f x] of an initial map f.
map : Maps.Initial P Q → Class P → Class Q
map f =
  Quotient.rec Quotient.squash/
    (λ x → Quotient.[ Maps.Initial.map f x ])
    (λ _ _ x≈y → Quotient.eq/ _ _ (Maps.Initial.resp f x≈y))

monotone : (f : Maps.Initial P Q) (a b : Class P)
  → Less P a b
  → Less Q (map f a) (map f b)
monotone {P = P} {Q = Q} f =
  Quotient.elimProp2
    (λ a b → HLevels.isPropΠ λ _ →
      Less-isProp Q (map f a) (map f b))
    (λ _ _ a<b →
      Less-intro Q
        (Maps.Initial.strict f
          (Less-witness P a<b)))

reflects : (f : Maps.Initial P Q) (a b : Class P)
  → Less Q (map f a) (map f b)
  → Less P a b
reflects {P = P} {Q = Q} f =
  Quotient.elimProp2
    (λ a b → HLevels.isPropΠ λ _ →
      Less-isProp P a b)
    (λ _ _ fa<fb →
      Less-intro P
        (Maps.Initial.reflect f
          (Less-witness Q fa<fb)))

-- Mathematical shape:
--
--   Initial P Q → ord(P) ≼ ord(Q).
--
-- The simulation is the class map. For y < f x, the lower law of f gives
-- z with f z ≈ y; then f z < f x, so z < x by reflection, and
-- [f z] = [y]. The lifting is first given under truncation and made exact
-- by the library, since a simulation is an embedding.
initial : Maps.Initial P Q
  → orderType P Simulation.≼ orderType Q
initial {P = P} {Q = Q} f =
  Cubical._,_ (map f)
    (Simulation.isSimulation∃→isSimulation
      (orderType P) (orderType Q) (map f)
      (Cubical._,_ (monotone f)
        (Quotient.elimProp2
          (λ _ _ → HLevels.isPropΠ λ _ → Truncation.isPropPropTrunc)
          (λ x y y<fx →
            let y<fx′ = Less-witness Q y<fx
                z , fz≈y = Maps.Initial.lower f x y y<fx′
                fz<fx = 𝒫.<-respˡ-≈ Q (𝒫.≈-sym Q fz≈y) y<fx′
            in Truncation.∣
                 Cubical._,_
                   (Cubical._,_ Quotient.[ z ]
                     (Less-intro P
                       (Maps.Initial.reflect f fz<fx)))
                   (Quotient.eq/ _ _ fz≈y)
               ∣₁))))

------------------------------------------------------------------------
-- Segments

-- Mathematical shape: a segment P ⊂ Q with ceiling c gives
--
--   ord(P) ≃ ord(Q) ↓ [c],
--   [x] ↦ ([to x] , [to x] < [c]).
--
-- The map is an embedding because the class map of the inclusion is a
-- simulation, and onto because the segment covers every point below its
-- ceiling. It preserves and reflects strict comparison as the class map
-- does.
principal : (s : Maps.Segment P Q)
  → Woset.WosetEquiv (orderType P)
      (orderType Q Simulation.↓
        Quotient.[ Presented._≺𝒫_.ceiling (Maps.Segment.bound s) ])
principal {P = P} {Q = Q} s =
  Cubical._,_
    (Cubical._,_ cone
      (Surjection.isEmbedding×isSurjection→isEquiv
        (Cubical._,_ embedding onto)))
    (Woset.iswosetequiv λ a b →
      Equiv.propBiimpl→Equiv
        (Less-isProp P a b)
        (Less-isProp Q (map f a) (map f b))
        (monotone f a b)
        (reflects f a b))
  where
  f : Maps.Initial P Q
  f = Maps.inclusion s

  c : 𝒫.X Q
  c = Presented._≺𝒫_.ceiling (Maps.Segment.bound s)

  Below : Class Q → Set _
  Below b = Less Q b Quotient.[ c ]

  inside : (a : Class P) → Below (map f a)
  inside =
    Quotient.elimProp
      (λ a → Less-isProp Q (map f a) Quotient.[ c ])
      (λ x →
        Less-intro Q
          (Presented._≺𝒫_.below (Maps.Segment.bound s) x))

  cone : Class P → Cubical.Σ (Class Q) Below
  cone a = Cubical._,_ (map f a) (inside a)

  embedding : Embedding.isEmbedding cone
  embedding =
    Embedding.injEmbedding {f = cone}
      (HLevels.isSetΣSndProp Quotient.squash/
        (λ b → Less-isProp Q b Quotient.[ c ]))
      (λ {a} {b} p →
        Embedding.isEmbedding→Inj
          (Simulation.isSimulation→isEmbedding
            (orderType P) (orderType Q) (map f)
            (Cubical.snd (initial f)))
          a b (Cubical.cong Cubical.fst p))

  onto : Surjection.isSurjection cone
  onto u =
    Quotient.elimProp
      {P = λ b → (b<c : Below b) →
        Truncation.∥ Equiv.fiber cone (Cubical._,_ b b<c) ∥₁}
      (λ _ → HLevels.isPropΠ λ _ → Truncation.isPropPropTrunc)
      (λ y y<c →
        let x , tx≈y =
              Maps.Segment.covers s y
                (Less-witness Q y<c)
        in Truncation.∣
             Cubical._,_ Quotient.[ x ]
               (SigmaProperties.Σ≡Prop
                 (λ b → Less-isProp Q b
                   Quotient.[ c ])
                 (Quotient.eq/ _ _ tx≈y))
           ∣₁)
      (Cubical.fst u) (Cubical.snd u)

-- Mathematical shape:
--
--   Segment P Q → ord(P) ≺ ord(Q),
--
-- bounded by the class of the ceiling.
segment : (s : Maps.Segment P Q)
  → orderType P Simulation.≺ orderType Q
segment s =
  Cubical._,_
    Quotient.[ Presented._≺𝒫_.ceiling (Maps.Segment.bound s) ]
    (Woset.invWosetEquiv (principal s))
