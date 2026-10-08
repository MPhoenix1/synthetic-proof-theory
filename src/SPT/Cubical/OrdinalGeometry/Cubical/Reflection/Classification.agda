{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Classification where

-- Row 9 on the reflected side. A classification of a presentation as
-- zero, strong successor or limit (Arithmetic.Classification) makes its
-- order type zero, a strong successor or a limit among the Cubical
-- well-ordered sets, in the sense of Kraus, Nordvall Forsberg and Xu,
-- (33)–(40). For Ord itself classification is equivalent to LEM (their
-- Theorem 63); the presentations retain it as data.
-- - Zero: the order type of a pointless presentation lies below every
--   well-ordered set.
-- - Successor: the order type of Q + 1 lies below every X above Q′, the
--   points of Q going through the bound of Q′ in X and the top to the
--   bound. Below P′ every well-ordered set is presented, so the strong
--   successor law of presentations applies there.
-- - Limit: the order type of a limit is the supremum of the order types
--   of its stages (Supremum.Chain).

open import Agda.Primitive using (Level; lsuc)
open import Data.Nat using (ℕ; suc)
import Data.Nat as Nat
open import Data.Product using (_,_)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Successor as Adjoin
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization using
  (Successor; Strong; module Successors; module Suprema; Increasing)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Classification using
  (Classified)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType using
  ( Class; Less; orderType
  ; orderType-equivalence
  ; Less-intro
  ; Less-witness
  )
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Representative
  using
  (representative; class)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Simulation using
  (initial; segment)
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Simulation.Converse
  as Converse
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.LowerCone using
  (segment-presented)
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Supremum as Supremum
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Supremum.Chain as Chain
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Supremum.Enumerated
  using (vacuous)

import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Prelude as Cubical
import Cubical.HITs.PropositionalTruncation as Truncation
import Cubical.HITs.SetQuotients as Quotient
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- Zero, strong successors and limits of well-ordered sets

-- (33): A is below every well-ordered set.
IsZero : Woset.Woset ℓ ℓ → Set (lsuc ℓ)
IsZero {ℓ} A = (B : Woset.Woset ℓ ℓ) → A Simulation.≼ B

-- (34), (35): A is the strong successor of B.
record IsStrongSuccessor {ℓ : Level} (B A : Woset.Woset ℓ ℓ)
  : Set (lsuc ℓ) where
  field
    above : B Simulation.≺ A
    least : (X : Woset.Woset ℓ ℓ) → B Simulation.≺ X → A Simulation.≼ X
    below : (X : Woset.Woset ℓ ℓ) → X Simulation.≺ A → X Simulation.≼ B

-- (37), (38): A is the limit of the strictly increasing F.
record IsLimit {ℓ : Level} (F : ℕ → Woset.Woset ℓ ℓ)
  (A : Woset.Woset ℓ ℓ) : Set (lsuc ℓ) where
  field
    increasing : (n : ℕ) → F n Simulation.≺ F (suc n)
    member : (n : ℕ) → F n Simulation.≼ A
    least : (X : Woset.Woset ℓ ℓ) → ((n : ℕ) → F n Simulation.≼ X)
      → A Simulation.≼ X

-- Classification among well-ordered sets.
data WosetClassified {ℓ : Level} (A : Woset.Woset ℓ ℓ) : Set (lsuc ℓ)
  where
  zero : IsZero A → WosetClassified A
  successor : (B : Woset.Woset ℓ ℓ) → IsStrongSuccessor B A
    → WosetClassified A
  limit : (F : ℕ → Woset.Woset ℓ ℓ) → IsLimit F A → WosetClassified A

------------------------------------------------------------------------
-- The successor of a presentation, among well-ordered sets

-- Mathematical shape: Q′ ≺ X → (Q + 1)′ ≼ X. For the bound x of Q′ in X
-- with e : X ↓ x ≃ Q′, a point q of Q goes to e⁻¹[q] and the top to x.
successor-least : (Q : 𝒫 ℓ) (X : Woset.Woset ℓ ℓ)
  → orderType Q Simulation.≺ X
  → orderType (Maps.Successor.next Q) Simulation.≼ X
successor-least {ℓ} Q X (x , e) =
  Cubical._,_ map
    (Simulation.isSimulation∃→isSimulation
      (orderType N) X map
      (Cubical._,_
        (Quotient.elimProp2
          (λ a b → HLevels.isPropΠ λ _ → prop (map a) (map b))
          (λ u v s →
            strict u v (Less-witness N s)))
        (Quotient.elimProp
          (λ _ → HLevels.isPropΠ2 λ _ _ → Truncation.isPropPropTrunc)
          (λ u b r → Truncation.∣ lift u b r ∣₁))))
  where
  N : 𝒫 ℓ
  N = Maps.Successor.next Q

  module E = Presented.Diagonal.Successor
    (Adjoin.constant Q) Nat.zero

  _<_ : Cubical.fst X → Cubical.fst X → Set ℓ
  _<_ = Woset.WosetStr._≺_ (Cubical.snd X)

  structure = Woset.WosetStr.isWoset (Cubical.snd X)
  prop = Woset.IsWoset.is-prop-valued structure

  back : Class Q → Cubical.fst (X Simulation.↓ x)
  back = Equiv.invEq (Cubical.fst e)

  forth : Cubical.fst (X Simulation.↓ x) → Class Q
  forth = Equiv.equivFun (Cubical.fst e)

  image : E.Entry → Cubical.fst X
  image (E.point q) = Cubical.fst (back Quotient.[ q ])
  image E.top = x

  respect : (u v : E.Entry) → u E.≈ v → image u Cubical.≡ image v
  respect (E.point q) (E.point q′) (E.point≈ p) =
    Cubical.cong (λ a → Cubical.fst (back a)) (Quotient.eq/ q q′ p)
  respect E.top E.top E.top≈ = Cubical.refl

  map : Class N → Cubical.fst X
  map = Quotient.rec (Woset.IsWoset.is-set structure) image respect

  strict : (u v : E.Entry) → u E.< v → image u < image v
  strict (E.point q) (E.point q′) (E.point< p) =
    Equiv.equivFun
      (Woset.IsWosetEquiv.pres≺⁻ (Cubical.snd e) Quotient.[ q ]
        Quotient.[ q′ ])
      (Less-intro Q p)
  strict (E.point q) E.top E.point<top =
    Cubical.snd (back Quotient.[ q ])

  -- A point b below the image of u is the image of the representative
  -- of the class of b in Q′, which lies below u.
  lift : (u : E.Entry) (b : Cubical.fst X) → b < image u
    → Cubical.Σ
        (Cubical.Σ (Class N)
          (λ a → Less N a Quotient.[ u ]))
        (λ a → map (Cubical.fst a) Cubical.≡ b)
  lift u b r =
    Cubical._,_
      (Cubical._,_ Quotient.[ E.point r₀ ] (below u r))
      (Cubical.cong (λ a → Cubical.fst (back a)) (class Q c)
        Cubical.∙ Cubical.cong Cubical.fst (Equiv.retEq (Cubical.fst e) w))
    where
    bound : (u : E.Entry) → b < image u → b < x
    bound (E.point q) r =
      Woset.IsWoset.is-trans structure b (image (E.point q)) x r
        (Cubical.snd (back Quotient.[ q ]))
    bound E.top r = r

    w : Cubical.fst (X Simulation.↓ x)
    w = Cubical._,_ b (bound u r)

    c : Class Q
    c = forth w

    r₀ : 𝒫.X Q
    r₀ = representative Q c

    below : (u : E.Entry) → b < image u
      → Less N Quotient.[ E.point r₀ ] Quotient.[ u ]
    below (E.point q) r =
      Less-intro N
        (E.point<
          (Less-witness Q
            (Cubical.subst2 (Less Q)
              (Cubical.sym (class Q c))
              (Equiv.secEq (Cubical.fst e) Quotient.[ q ])
              (Equiv.equivFun
                (Woset.IsWosetEquiv.pres≺ (Cubical.snd e) w
                  (back Quotient.[ q ]))
                r))))
    below E.top _ = Less-intro N E.point<top

------------------------------------------------------------------------
-- The reflected classification

-- Mathematical shape: Classified P → WosetClassified P′.
classified : {P : 𝒫 ℓ} → Classified P
  → WosetClassified (orderType P)
classified {P = P} (Classified.zero z) =
  zero λ B → vacuous P z B
classified {P = P} (Classified.successor Q st) =
  successor (orderType Q) record
    { above = segment (Successor.above (Strong.successor st))
    ; least = λ X σ →
        Simulation.isTrans≼ (orderType P)
          (orderType (Maps.Successor.next Q)) X
          (Simulation.WosetEquiv→≼
            (orderType-equivalence
              (Successors.equivalent (Strong.successor st))))
          (successor-least Q X σ)
    ; below = λ X σ →
        Truncation.rec
          (Simulation.isPropValued≼ X (orderType Q))
          (λ presented →
            let R = Cubical.fst presented
                e = Cubical.snd presented
            in Simulation.isTrans≼ X (orderType R)
                 (orderType Q)
                 (Simulation.WosetEquiv→≼ (Woset.invWosetEquiv e))
                 (initial (Strong.below st R
                   (Converse.segment
                     (Simulation.≺RespectsEquivL (orderType P)
                       (Woset.invWosetEquiv e) σ)))))
          (segment-presented P X σ)
    }
classified {P = P} (Classified.limit s sup) =
  limit (λ n → orderType (Increasing.stage s n)) record
    { increasing = λ n → segment (Increasing.step s n)
    ; member = λ n →
        Simulation.isTrans≼
          (orderType (Increasing.stage s n))
          (Supremum.supremum (Increasing.stage s)) (orderType P)
          (Supremum.upper (Increasing.stage s) n)
          (Simulation.WosetEquiv→≼ (Woset.invWosetEquiv supremum))
    ; least = λ X g →
        Simulation.isTrans≼ (orderType P)
          (Supremum.supremum (Increasing.stage s)) X
          (Simulation.WosetEquiv→≼ supremum)
          (Supremum.least (Increasing.stage s) X g)
    }
  where
  -- P′ is the supremum of the stages.
  supremum : Woset.WosetEquiv (orderType P)
    (Supremum.supremum (Increasing.stage s))
  supremum =
    Woset.compWosetEquiv
      (orderType-equivalence
        (Suprema.unique sup (Increasing.supremum s)))
      (Woset.invWosetEquiv (Chain.chain (Increasing.chain s)))
