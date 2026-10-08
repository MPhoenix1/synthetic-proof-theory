{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Supremum.Enumerated
  where

-- Presented suprema of countable families of ordinals of one ambient.
--
-- Let W be an ambient, I a type with a partial enumeration e, and
-- f : I → W. The running maxima of the points f (e n) that occur form a
-- chain of cones: the empty presentation until the first entry, then the
-- cone at the current maximum. Its completion presents the supremum of
-- the cones ∂(f i): every ∂(f i) lies below the stage where e lists i,
-- and every stage is a cone at some f i, or empty. In particular the
-- supremum lies strictly below the presented ω₁. Empty and finite index
-- types are included.

open import Agda.Primitive using (Level)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
open import SPT.Cubical.OrdinalGeometry.Presentation.Sum using (∂)
import SPT.Cubical.OrdinalGeometry.Presentation.Limit as Limit
import SPT.Cubical.OrdinalGeometry.Operation.Base as Operation
import SPT.Cubical.OrdinalGeometry.Arithmetic.Ambient as Ambient
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization using
  (Zero; empty) renaming (nothing to vacant)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Countability using
  (PartialEnumeration; sequence; covers)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType using
  (orderType)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Simulation using
  (initial)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Supremum using
  (supremum; upper; least)
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Supremum.Chain as Chain
open import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Base using
  ( ω₁ᴳ
  ; orderType-strictᴳ
  )

import Cubical.Data.Equality.Conversion as EqualityConversion
import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Prelude as Cubical
import Cubical.HITs.PropositionalTruncation as Truncation
import Cubical.HITs.SetQuotients as Quotient
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

private
  variable
    ℓ : Level

-- A presentation without points has an order type below every
-- well-ordered set.
vacuous : (Z : 𝒫 ℓ) → Zero Z → (B : Woset.Woset ℓ ℓ)
  → orderType Z Simulation.≼ B
vacuous Z z B =
  Cubical._,_ map
    (Simulation.isSimulation∃→isSimulation (orderType Z) B map
      (Cubical._,_
        (Quotient.elimProp2
          (λ a b → HLevels.isPropΠ λ _ →
            Woset.IsWoset.is-prop-valued
              (Woset.WosetStr.isWoset (Cubical.snd B)) (map a) (map b))
          (λ x _ _ → ⊥-elim (empty z x)))
        (Quotient.elimProp
          (λ _ → HLevels.isPropΠ2 λ _ _ → Truncation.isPropPropTrunc)
          (λ x _ _ → ⊥-elim (empty z x)))))
  where
  map : Cubical.fst (orderType Z) → Cubical.fst B
  map =
    Quotient.rec
      (Woset.IsWoset.is-set (Woset.WosetStr.isWoset (Cubical.snd B)))
      (λ x → ⊥-elim (empty z x))
      (λ x _ _ → ⊥-elim (empty z x))

module _ (W : 𝒫 ℓ) {I : Set ℓ} (f : I → 𝒫.X W) (e : PartialEnumeration I)
  where

  private
    module W = 𝒫 W

    -- The cone at a running maximum, empty before the first entry.
    cone : Maybe W.X → 𝒫 ℓ
    cone nothing = Operation.empty
    cone (just x) = ∂ W x

    merge : Maybe W.X → Maybe W.X → Maybe W.X
    merge nothing z = z
    merge (just x) nothing = just x
    merge (just x) (just y) = just (proj₁ (Ambient.max W x y))

    step : (a z : Maybe W.X) → Maps.Initial (cone a) (cone (merge a z))
    step nothing z = vacant (cone z)
    step (just x) nothing = Maps.identity (∂ W x)
    step (just x) (just y) =
      Ambient.included W (proj₁ (proj₂ (Ambient.max W x y)))

    enter : (a : Maybe W.X) (y : W.X)
      → Maps.Initial (∂ W y) (cone (merge a (just y)))
    enter nothing y = Maps.identity (∂ W y)
    enter (just x) y =
      Ambient.included W (proj₁ (proj₂ (proj₂ (Ambient.max W x y))))

    -- The running maximum is one of the points f i.
    Attained : Maybe W.X → Set ℓ
    Attained nothing = ⊤
    Attained (just x) = Σ I (λ i → x W.≈ f i)

    attained : (a z : Maybe W.X) → Attained a → Attained z
      → Attained (merge a z)
    attained nothing z _ t = t
    attained (just x) nothing t _ = t
    attained (just x) (just y) (i , p) (j , q)
      with proj₂ (proj₂ (proj₂ (Ambient.max W x y)))
    ... | inj₁ r = i , W.≈-trans r p
    ... | inj₂ r = j , W.≈-trans r q

    entry : ℕ → Maybe W.X
    entry n = Maybe.map f (sequence e n)

    running : ℕ → Maybe W.X
    running zero = merge nothing (entry zero)
    running (suc n) = merge (running n) (entry (suc n))

    entered : (n : ℕ) → Attained (entry n)
    entered n with sequence e n
    ... | nothing = tt
    ... | just i = i , W.≈-refl (f i)

    reached : (n : ℕ) → Attained (running n)
    reached zero = attained nothing (entry zero) tt (entered zero)
    reached (suc n) =
      attained (running n) (entry (suc n)) (reached n) (entered (suc n))

    -- The point listed at n lies below the running maximum at n.
    reach : (n : ℕ) (y : W.X) → entry n ≡ just y
      → Maps.Initial (∂ W y) (cone (running n))
    reach zero y p =
      subst (λ z → Maps.Initial (∂ W y) (cone (merge nothing z)))
        (sym p) (enter nothing y)
    reach (suc n) y p =
      subst (λ z → Maps.Initial (∂ W y) (cone (merge (running n) z)))
        (sym p) (enter (running n) y)

    family : I → 𝒫 ℓ
    family i = ∂ W (f i)

    stages : ℕ → 𝒫 ℓ
    stages n = cone (running n)

    -- Every stage is bounded by the supremum of the family.
    bound : (a : Maybe W.X) → Attained a
      → orderType (cone a) Simulation.≼ supremum family
    bound nothing _ =
      vacuous Operation.empty vacant (supremum family)
    bound (just x) (i , p) =
      Simulation.isTrans≼ (orderType (∂ W x))
        (orderType (family i)) (supremum family)
        (initial (Maps.equivalence (Ambient.same W p)))
        (upper family i)

  -- The chain of cones at the running maxima.
  chain : Limit.Chain ℓ
  chain = record
    { stage = stages
    ; edge = λ n → step (running n) (entry (suc n))
    }

  -- Mathematical shape: for e a partial enumeration of I,
  --
  --   sup_{i ∈ I} ord(∂(f i))
  --     ≃ ord(completion of the running maxima).
  --
  -- Each family member lies below the stage where e lists its index,
  -- found under the truncation of e's coverage; each stage lies below
  -- a family member, or is empty.
  enumerated : Woset.WosetEquiv (supremum λ i → ∂ W (f i))
    (orderType (Limit.completion chain))
  enumerated =
    Woset.compWosetEquiv
      (Simulation.isAntisym≼Equiv (supremum family) (supremum stages)
        forward backward)
      (Chain.chain chain)
    where
    forward : supremum family Simulation.≼ supremum stages
    forward =
      least family (supremum stages) λ i →
        Truncation.rec
          (Simulation.isPropValued≼ (orderType (family i))
            (supremum stages))
          (λ hit →
            Simulation.isTrans≼ (orderType (family i))
              (orderType (stages (proj₁ hit)))
              (supremum stages)
              (initial (reach (proj₁ hit) (f i)
                (EqualityConversion.pathToEq
                  (Cubical.cong (Maybe.map f) (proj₂ hit)))))
              (upper stages (proj₁ hit)))
          (covers e i)

    backward : supremum stages Simulation.≼ supremum family
    backward =
      least stages (supremum family) λ n →
        bound (running n) (reached n)

  -- The supremum lies strictly below the presented ω₁ of every
  -- geometry.
  enumerated-below : (G : Presented.𝒫ω₁𝒢 ℓ)
    → supremum (λ i → ∂ W (f i))
        Simulation.≺ ω₁ᴳ G
  enumerated-below G =
    Simulation.≺RespectsEquivL (ω₁ᴳ G)
      (Woset.invWosetEquiv enumerated)
      (orderType-strictᴳ G
        (Limit.completion chain))
