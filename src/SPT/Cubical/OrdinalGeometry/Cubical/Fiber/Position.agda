{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Position
  where

-- What reflection forgets at positions.  For a geometry G, the projection
-- sending a position (P , route) to ord(P) has a fiber over the one-point
-- order containing the whole pointed small universe Σ T. T as a split
-- retract: a pointed type (T , t) presents the one-point order, and is
-- recovered from its presentation.  Univalence for the swap of 𝟐 × 𝟐 then
-- gives a nontrivial loop, so that fiber is not a set and the projection
-- is not an embedding.  Similarly, T is a retract of a fiber of the map
-- from the points of one presentation on ℕ × T to ω₁ᴳ(G).

open import Agda.Primitive using (Level; lzero)
open import Data.Bool using (Bool; false; true)
open import Data.Empty using (⊥)
open import Data.Empty.Polymorphic as PolyEmpty using ()
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic as PolyUnit using ()
open import Level using (Lift; lift)
import Relation.Binary.PropositionalEquality as Ordinary

open import SPT.Cubical.Core.WellFounded using (acc)
import SPT.Cubical.Core.Equality as CoreEquality
open import SPT.Cubical.Core.Nat.Order using (_<ℕᶜ_; <ℕᶜ-trans; cmpℕᶜ)
open import SPT.Cubical.Core.Nat.WellFounded using (wfℕᶜ)
open import SPT.Cubical.Core.WellFounded.Pullback using (pullback-wf)
open import SPT.Cubical.Core.WellFounded.Subrelation using (subrel-wf)
import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType as Reflection
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Base as Omega

import Cubical.Data.Equality.Conversion as EqualityConversion
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.Isomorphism as Isomorphism
import Cubical.Foundations.Pointed.Base as Pointed
import Cubical.Foundations.Prelude as Cubical
import Cubical.Foundations.Univalence as Univalence
import Cubical.Functions.Embedding as Embedding
import Cubical.HITs.SetQuotients as Quotient
import Cubical.Relation.Binary.Order.Woset.Base as Woset

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- A pointed type at every rank

-- For a pointed type (T , base), the presentation with carrier ℕ × T ordered
-- by the first coordinate:
--
--   (m,x) ≈ (n,y) := m = n,   (m,x) < (n,y) := m < n,   enum(n) = (n,base).
--
-- Reflection identifies all points of the same rank.

rankPresentation :
    (T : Set ℓ)
  → T
  → Presented.CountableOrdinal𝒫 ℓ
rankPresentation {ℓ} T base = record
  { X = ℕ × T
  ; _≈_ = λ left right →
      Lift ℓ (proj₁ left Ordinary.≡ proj₁ right)
  ; _<_ = λ left right →
      Lift ℓ (proj₁ left <ℕᶜ proj₁ right)
  ; ≈-refl = λ point → lift Ordinary.refl
  ; ≈-sym = λ where
      (lift equality) → lift (Ordinary.sym equality)
  ; ≈-trans = λ where
      (lift first) (lift second) →
        lift (Ordinary.trans first second)
  ; <-trans = λ {x} {y} {z} → λ where
      (lift x<y) (lift y<z) →
        lift (<ℕᶜ-trans
          {a = proj₁ x} {b = proj₁ y} {c = proj₁ z} x<y y<z)
  ; <-respˡ-≈ = λ {x} {x′} {y} → λ where
      (lift x=x′) (lift x<y) →
        lift (Ordinary.subst (λ rank → rank <ℕᶜ proj₁ y) x=x′ x<y)
  ; <-respʳ-≈ = λ {x} {y} {y′} → λ where
      (lift y=y′) (lift x<y) →
        lift (Ordinary.subst (λ rank → proj₁ x <ℕᶜ rank) y=y′ x<y)
  ; <-wf =
      subrel-wf
        (λ { (lift strict) → strict })
        (pullback-wf {rank = proj₁} {_<_ = _<ℕᶜ_} wfℕᶜ)
  ; compare = rank-trichotomy
  ; enum = λ rank → just (rank , base)
  ; covers = λ occurrence →
      proj₁ occurrence
      , (proj₁ occurrence , base)
      , Ordinary.refl
      , lift Ordinary.refl
  }
  where
  rank-trichotomy :
      (left right : ℕ × T)
    → Lift ℓ (proj₁ left <ℕᶜ proj₁ right)
      Data.Sum.⊎
      ( Lift ℓ (proj₁ left Ordinary.≡ proj₁ right)
        Data.Sum.⊎
        Lift ℓ (proj₁ right <ℕᶜ proj₁ left)
      )
  rank-trichotomy left right
      with cmpℕᶜ (proj₁ left) (proj₁ right)
  ... | inj₁ left<right = inj₁ (lift left<right)
  ... | inj₂ (inj₁ left=right) = inj₂ (inj₁ (lift left=right))
  ... | inj₂ (inj₂ right<left) = inj₂ (inj₂ (lift right<left))

-- The map from points (n , t) of this presentation to ω₁ᴳ(G), through the
-- class of (n , t).

occurrenceMap :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (T : Set ℓ)
    (base : T)
  → ℕ × T
  → Cubical.fst (Omega.ω₁ᴳ geometry)
occurrenceMap geometry T base occurrence =
  Cubical.fst
    (Omega.upperᴳ
      geometry (rankPresentation T base))
    Quotient.[ occurrence ]

-- Its homotopy fiber over the point (rank , base); every t : T gives the
-- point (rank , t) of it, and t is recovered from the first component.

OccurrenceFiber :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (T : Set ℓ)
    (base : T)
    (rank : ℕ)
  → Set _
OccurrenceFiber geometry T base rank =
  Cubical.Σ (ℕ × T) λ occurrence →
    occurrenceMap geometry T base occurrence
      Cubical.≡
    occurrenceMap geometry T base (rank , base)

retainOccurrence :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (T : Set ℓ)
    (base : T)
    (rank : ℕ)
  → T
  → OccurrenceFiber geometry T base rank
retainOccurrence geometry T base rank point =
  (rank , point)
  Cubical.,
  Cubical.cong
    (Cubical.fst
      (Omega.upperᴳ
        geometry (rankPresentation T base)))
    (Quotient.eq/
      {R = Presented.CountableOrdinal𝒫._≈_ (rankPresentation T base)}
      (rank , point) (rank , base) (lift Ordinary.refl))

recoverOccurrence :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (T : Set ℓ)
    (base : T)
    (rank : ℕ)
  → OccurrenceFiber geometry T base rank
  → T
recoverOccurrence geometry T base rank fiber-point =
  proj₂ (Cubical.fst fiber-point)

-- recoverOccurrence (retainOccurrence t) = t, by refl.

recover-retainOccurrence :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (T : Set ℓ)
    (base : T)
    (rank : ℕ)
    (point : T)
  → recoverOccurrence geometry T base rank
      (retainOccurrence geometry T base rank point)
    Cubical.≡ point
recover-retainOccurrence geometry T base rank point =
  Cubical.refl

-- So an h-level bound on the fiber bounds T.

occurrenceFiber-reflects-hlevel :
    (height : ℕ)
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (T : Set ℓ)
    (base : T)
    (rank : ℕ)
  → HLevels.isOfHLevel height
      (OccurrenceFiber geometry T base rank)
  → HLevels.isOfHLevel height T
occurrenceFiber-reflects-hlevel
    height geometry T base rank =
  HLevels.isOfHLevelRetract height
    (retainOccurrence geometry T base rank)
    (recoverOccurrence geometry T base rank)
    (recover-retainOccurrence geometry T base rank)

occurrenceFiber-obstruction :
    (height : ℕ)
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (T : Set ℓ)
    (base : T)
    (rank : ℕ)
  → (HLevels.isOfHLevel height T → ⊥)
  → HLevels.isOfHLevel height
      (OccurrenceFiber geometry T base rank)
  → ⊥
occurrenceFiber-obstruction
    height geometry T base rank T-not-hlevel fiber-hlevel =
  T-not-hlevel
    (occurrenceFiber-reflects-hlevel
      height geometry T base rank fiber-hlevel)

------------------------------------------------------------------------
-- The pointed universe in one position fiber

-- PointedType(ℓ) = Σ(T : Set ℓ). T.

PointedType : (level : Level) → Set _
PointedType level =
  Cubical.Σ (Set level) (λ T → T)

-- The collapsed presentation of (T , base): carrier T, every two points
-- equivalent, empty order, enum(n) = base.  Its order type is the
-- one-point order.

collapsed :
    (T : Set ℓ)
  → T
  → Presented.CountableOrdinal𝒫 ℓ
collapsed {ℓ} T base = record
  { X = T
  ; _≈_ = λ _ _ → PolyUnit.⊤ {ℓ}
  ; _<_ = λ _ _ → PolyEmpty.⊥ {ℓ}
  ; ≈-refl = λ _ → PolyUnit.tt
  ; ≈-sym = λ _ → PolyUnit.tt
  ; ≈-trans = λ _ _ → PolyUnit.tt
  ; <-trans = λ ()
  ; <-respˡ-≈ = λ _ ()
  ; <-respʳ-≈ = λ _ ()
  ; <-wf = λ point → acc (λ predecessor ())
  ; compare = λ _ _ → inj₂ (inj₁ PolyUnit.tt)
  ; enum = λ _ → just base
  ; covers = λ point →
      zero , base , Ordinary.refl , PolyUnit.tt
  }

unitPresentation :
  Presented.CountableOrdinal𝒫 ℓ
unitPresentation {ℓ} =
  collapsed (PolyUnit.⊤ {ℓ}) PolyUnit.tt

-- collapsed(T , base) ≃𝒫 unitPresentation: the forward map forgets the
-- point, the backward map picks base.

collapsed-unit :
    (T : Set ℓ)
    (base : T)
  → collapsed T base
      Presented.≃𝒫 unitPresentation {ℓ}
collapsed-unit T base = record
  { to = λ _ → PolyUnit.tt
  ; from = λ _ → base
  ; to-≈ = λ _ → PolyUnit.tt
  ; from-≈ = λ _ → PolyUnit.tt
  ; to-< = λ ()
  ; from-< = λ ()
  ; from-to-≈ = λ _ → PolyUnit.tt
  ; to-from-≈ = λ _ → PolyUnit.tt
  }

UnitOrderType :
  (level : Level) → Woset.Woset level level
UnitOrderType level =
  Reflection.orderType (unitPresentation {level})

projection :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → Presented.ω₁.Geometry.Position geometry
  → Woset.Woset ℓ ℓ
projection geometry =
  Omega.𝒫ω₁.positionOrderType geometry

-- The fiber of the projection q_G : Position(G) → Woset over α,
--
--   PositionFiber(G,α) = Σ(u : Position(G)). q_G(u) = α.

PositionFiber :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (ordinal : Woset.Woset ℓ ℓ)
  → Set _
PositionFiber geometry ordinal =
  Cubical.Σ
    (Presented.ω₁.Geometry.Position geometry)
    (λ position →
      projection geometry position
        Cubical.≡ ordinal)

retain :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → PointedType ℓ
  → PositionFiber geometry (UnitOrderType ℓ)
retain geometry (T Cubical., base) =
  Presented.ω₁.Geometry.position geometry
    (collapsed T base)
  Cubical.,
  Reflection.orderType-path
    (collapsed-unit T base)

-- Recovery reads a pointed type off the presentation of a position: its
-- carrier, pointed by the entry at index 0 (or the unit type when there is
-- none).  It ignores the route and the path.

recover :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → PositionFiber geometry (UnitOrderType ℓ)
  → PointedType ℓ
recover geometry fiber-point
    with Presented.CountableOrdinal𝒫.enum
      (Cubical.fst (Cubical.fst fiber-point)) zero
... | nothing = PolyUnit.⊤ Cubical., PolyUnit.tt
... | just point =
  Presented.CountableOrdinal𝒫.X (Cubical.fst (Cubical.fst fiber-point))
  Cubical., point

-- recover (retain (T , base)) = (T , base), by refl: the pointed universe is
-- a retract of PositionFiber(G, UnitOrderType).

recover-retain :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    (pointed : PointedType ℓ)
  → recover geometry
      (retain geometry pointed)
    Cubical.≡ pointed
recover-retain geometry (T Cubical., base) =
  Cubical.refl

positionFiber-reflects-hlevel :
    (height : ℕ)
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
  → HLevels.isOfHLevel height
      (PositionFiber geometry (UnitOrderType ℓ))
  → HLevels.isOfHLevel height (PointedType ℓ)
positionFiber-reflects-hlevel height geometry =
  HLevels.isOfHLevelRetract height
    (retain geometry)
    (recover geometry)
    (recover-retain geometry)

-- Recovery also recovers paths: cong recover (cong retain p) = p.

recover-retain-path :
    (geometry : Presented.𝒫ω₁𝒢 ℓ)
    {left right : PointedType ℓ}
    (path : left Cubical.≡ right)
  → Cubical.cong (recover geometry)
      (Cubical.cong (retain geometry) path)
    Cubical.≡ path
recover-retain-path geometry {left} =
  Cubical.J
    (λ right path →
      Cubical.cong (recover geometry)
        (Cubical.cong (retain geometry) path)
      Cubical.≡ path)
    Cubical.refl

------------------------------------------------------------------------
-- A nontrivial loop

BoolPair : Set
BoolPair = Bool × Bool

swapBoolPair : BoolPair → BoolPair
swapBoolPair pair = proj₂ pair , proj₁ pair

swapBoolPairIso : Isomorphism.Iso BoolPair BoolPair
Isomorphism.Iso.fun swapBoolPairIso = swapBoolPair
Isomorphism.Iso.inv swapBoolPairIso = swapBoolPair
Isomorphism.Iso.rightInv swapBoolPairIso pair = Cubical.refl
Isomorphism.Iso.leftInv swapBoolPairIso pair = Cubical.refl

swapBoolPairEquivalence : Equiv._≃_ BoolPair BoolPair
swapBoolPairEquivalence = Isomorphism.isoToEquiv swapBoolPairIso

pointedBoolPair : PointedType lzero
pointedBoolPair = BoolPair Cubical., (false , false)

-- The pointed loop (𝟐 × 𝟐 , (false,false)) = (𝟐 × 𝟐 , (false,false)) given
-- by univalence for the swap of coordinates, which fixes the base point.

pointedSwapLoop : pointedBoolPair Cubical.≡ pointedBoolPair
pointedSwapLoop = Pointed.ua∙ swapBoolPairEquivalence Cubical.refl

true-not-false : true Cubical.≡ false → ⊥
true-not-false path with EqualityConversion.pathToEq path
... | ()

-- It is not refl: transport along it moves (false,true) to (true,false).

pointedSwapLoop-not-refl : pointedSwapLoop Cubical.≡ Cubical.refl → ⊥
pointedSwapLoop-not-refl loop=refl =
  true-not-false
    (Cubical.cong proj₁ moved-point-fixed)
  where
  type-loop=refl :
    Univalence.ua swapBoolPairEquivalence Cubical.≡ Cubical.refl
  type-loop=refl =
    Cubical.cong (Cubical.cong Cubical.fst) loop=refl

  moved-point-fixed :
    swapBoolPair (false , true) Cubical.≡ (false , true)
  moved-point-fixed =
    Cubical.sym (Univalence.uaβ swapBoolPairEquivalence (false , true))
    Cubical.∙
    Cubical.cong
      (λ type-loop → Cubical.transport type-loop (false , true))
      type-loop=refl

pointedType-not-set : Cubical.isSet (PointedType lzero) → ⊥
pointedType-not-set pointed-is-set =
  pointedSwapLoop-not-refl
    (pointed-is-set pointedBoolPair pointedBoolPair
      pointedSwapLoop Cubical.refl)

-- Its image in PositionFiber(G, UnitOrderType), under retain.

swapLoop :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
  → CoreEquality.Loop
      (PositionFiber geometry (UnitOrderType lzero))
      (retain geometry pointedBoolPair)
swapLoop geometry =
  EqualityConversion.pathToEq
    (Cubical.cong
      (retain geometry)
      pointedSwapLoop)

-- The same loop as a path, used for the non-setness results below.

swapPath :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
  → retain geometry pointedBoolPair
      Cubical.≡
    retain geometry pointedBoolPair
swapPath geometry =
  Cubical.cong
    (retain geometry)
    pointedSwapLoop

swapPath-not-refl :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
  → swapPath geometry Cubical.≡ Cubical.refl
  → ⊥
swapPath-not-refl geometry fiber-loop=refl =
  pointedSwapLoop-not-refl
    (Cubical.sym
      (recover-retain-path geometry pointedSwapLoop)
    Cubical.∙
    Cubical.cong
      (Cubical.cong (recover geometry))
      fiber-loop=refl)

-- PositionFiber(G, UnitOrderType) is not a set: recovery would make the
-- image of swapLoop trivial.

positionFiber-not-set :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
  → Cubical.isSet
      (PositionFiber geometry (UnitOrderType lzero))
  → ⊥
positionFiber-not-set geometry fiber-is-set =
  swapPath-not-refl geometry
    (fiber-is-set
      (retain geometry pointedBoolPair)
      (retain geometry pointedBoolPair)
      (swapPath geometry)
      Cubical.refl)

-- Hence that fiber is not a proposition, and q_G is not an embedding.

positionFiber-not-prop :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
  → Cubical.isProp
      (PositionFiber geometry (UnitOrderType lzero))
  → ⊥
positionFiber-not-prop geometry fiber-is-prop =
  positionFiber-not-set geometry
    (Cubical.isProp→isSet fiber-is-prop)

projection-not-embedding :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
  → Embedding.isEmbedding (projection geometry)
  → ⊥
projection-not-embedding geometry embedding =
  positionFiber-not-prop geometry
    (Embedding.isEmbedding→hasPropFibers embedding
      (UnitOrderType lzero))

-- The same non-setness for the identity type ≡ of Agda (Core.Equality.IsSet),
-- through the conversion between paths and ≡.

swapLoop-not-refl :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
  → swapLoop geometry Ordinary.≡ Ordinary.refl
  → ⊥
swapLoop-not-refl geometry loop=refl =
  swapPath-not-refl geometry
    (Cubical.sym
      (EqualityConversion.eqToPath-pathToEq
        (swapPath geometry))
    Cubical.∙
    Cubical.cong
      EqualityConversion.eqToPath
      (EqualityConversion.eqToPath loop=refl))

positionFiber-not-IsSet :
    (geometry : Presented.𝒫ω₁𝒢 lzero)
  → CoreEquality.IsSet
      (PositionFiber geometry (UnitOrderType lzero))
  → ⊥
positionFiber-not-IsSet geometry fiber-is-set =
  swapLoop-not-refl geometry
    (fiber-is-set
      (retain geometry pointedBoolPair)
      (retain geometry pointedBoolPair)
      (swapLoop geometry)
      Ordinary.refl)
