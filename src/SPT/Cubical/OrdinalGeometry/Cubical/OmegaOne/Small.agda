{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Small where

-- ω₁ is a small well-order, the same at every universe level, and a point
-- of the ordinal of ordinals:
--
--   Ω = sup (O : BooleanOrder), ord(O)   :   Woset(0, 0),
--   ω₁(ℓ) ≃ Ω and ω₁(ℓ) ≃ ω₁(ℓ′),
--   ω₁(ℓ) ≃ Ord(ℓ) ↓ Ω′, where Ω′ is Ω raised to level ℓ.
--
-- Boolean orders form a small type, and every presentation of every level
-- is equivalent to the presentation of one (Normalization.Boolean).  So
-- every presentation of level ℓ lies below Ω′, and every principal segment
-- of Ω′ is presented; leastness and the cut of ω₁ (Specification) then
-- place Ω′ on both sides of ω₁(ℓ).  The carrier of ω₁(ℓ) lies one universe
-- up only because of how ω₁ is constructed.  Below Ω′ in Ord(ℓ) lie
-- exactly the merely presented well-orders, and Ω′ is the only point of
-- Ord(ℓ) with that property (cutPoint-isContr).

open import Agda.Primitive using (Level; lzero; lsuc)
open import Data.Bool.Base using (Bool; true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Level using (lift; lower)
import Relation.Binary.PropositionalEquality as InductiveEquality

import SPT.Cubical.Core.WellFounded as Accessibility
import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order
open import SPT.Cubical.OrdinalGeometry.ExactOrder.Boolean using
  (BooleanOrder; Points; order; point-≡)
import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Successor as Successor
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization.Presentation
  as Normalized
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization.Boolean
  as Boolean
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType using
  (orderType; orderType-equivalence)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Successor using
  (successor-strict)
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Supremum as Supremum
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.LowerCone using
  (segment-presented)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Countability
  using (PartialEnumeration)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Woset using
  (WosetCarrier; StrictTrichotomy; toPresentation; toPresentation-orderType)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Ordinals using
  (raise; raise-equivalence; Ord; lowerset; segments→simulation)
open import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Base using (ω₁)
open import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Cut using
  (MerelyPresented; isPropMerelyPresented)
import SPT.Cubical.OrdinalGeometry.Cubical.OmegaOne.Specification
  as Specification

open import Cubical.Data.Equality.Conversion using (eqToPath; pathToEq)
open import Cubical.Data.Nat using (isSetℕ)
open import Cubical.Data.Sigma.Base using (_×_)
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)
open import Cubical.Foundations.Equiv using
  (_≃_; equivFun; invEq; invEquiv; compEquiv; propBiimpl→Equiv)
open import Cubical.Foundations.HLevels using (isSetΣ; isPropΠ; isOfHLevel≃)
import Cubical.Foundations.Prelude as Cubical
open Cubical using (isProp; isSet; isContr; isProp→isSet)
import Cubical.HITs.PropositionalTruncation as Truncation
import Cubical.Induction.WellFounded as WellFounded
open import Cubical.Relation.Binary.Extensionality using
  (isWeaklyExtensional; ≺×→≡→isWeaklyExtensional;
   isWeaklyExtensional→≺Equiv→≡)
open import Cubical.Relation.Binary.Order.Woset.Base using
  (Woset; woset; iswoset; WosetEquiv; compWosetEquiv; invWosetEquiv;
   WosetPath)
open import Cubical.Relation.Binary.Order.Woset.Simulation using
  (_≺_; _↓_; ≺Trans≼; isTrans≼; WosetEquiv→≼; isAntisym≼Equiv;
   ↓Decreasing; ↓RespectsEquiv; ≺RespectsEquivR; isPropValued≺;
   isWeaklyExtensional≺)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- The well-order of a Boolean order

private
  isPropT : (b : Bool) → isProp (T b)
  isPropT true _ _ = Cubical.refl
  isPropT false ()

  Strict : (O : BooleanOrder) → Points O → Points O → Set
  Strict O x y = T (BooleanOrder.less O (proj₁ x) (proj₁ y))

  pointPath : (O : BooleanOrder) {x y : Points O}
    → proj₁ x InductiveEquality.≡ proj₁ y → x Cubical.≡ y
  pointPath O e = eqToPath (point-≡ O e)

-- Mathematical shape: well-order(O) = (Points O , less_O) : Woset(0, 0).
well-order : BooleanOrder → Woset lzero lzero
well-order O =
  woset (Points O) (Strict O)
    (iswoset set prop well-founded extensional transitive)
  where
    set : isSet (Points O)
    set = isSetΣ isSetℕ
      (λ n → isProp→isSet (isPropT (BooleanOrder.point O n)))

    prop : (x y : Points O) → isProp (Strict O x y)
    prop x y = isPropT (BooleanOrder.less O (proj₁ x) (proj₁ y))

    accessible : (i : ℕ)
      → Accessibility.Acc (λ i j → T (BooleanOrder.less O i j)) i
      → (s : T (BooleanOrder.point O i))
      → WellFounded.Acc (Strict O) (i , s)
    accessible i (Accessibility.acc smaller) s =
      WellFounded.acc λ y p →
        accessible (proj₁ y) (smaller (proj₁ y) p) (proj₂ y)

    well-founded : WellFounded.WellFounded (Strict O)
    well-founded x =
      accessible (proj₁ x) (BooleanOrder.wf O (proj₁ x)) (proj₂ x)

    irreflexive : (x : Points O) → Strict O x x → ⊥
    irreflexive x = Accessibility.acc↛loop (BooleanOrder.wf O (proj₁ x))

    -- Equal predecessors force equal points, through trichotomy.
    same-predecessors : (x y : Points O)
      → ((z : Points O) →
          (Strict O z x → Strict O z y) × (Strict O z y → Strict O z x))
      → x Cubical.≡ y
    same-predecessors x y same
        with BooleanOrder.compare O (proj₁ x) (proj₁ y) (proj₂ x) (proj₂ y)
    ... | inj₁ p = ⊥-elim (irreflexive x (Cubical.snd (same x) p))
    ... | inj₂ (inj₁ e) = pointPath O e
    ... | inj₂ (inj₂ p) = ⊥-elim (irreflexive y (Cubical.fst (same y) p))

    extensional : isWeaklyExtensional (Strict O)
    extensional =
      ≺×→≡→isWeaklyExtensional (Strict O) set prop same-predecessors

    transitive : (x y z : Points O)
      → Strict O x y → Strict O y z → Strict O x z
    transitive x y z = BooleanOrder.trans O {proj₁ x} {proj₁ y} {proj₁ z}

------------------------------------------------------------------------
-- Its presentations at every level

private
  -- The presentation of a Boolean order at level ℓ.
  presentation : (ℓ : Level) → BooleanOrder → 𝒫 ℓ
  presentation ℓ O = Normalized.presentation {ℓ = ℓ} (order O)

  raised : (ℓ : Level) → BooleanOrder → Woset ℓ ℓ
  raised ℓ O = raise ℓ ℓ (well-order O)

  trichotomy : (O : BooleanOrder) → StrictTrichotomy (raised ℓ O)
  trichotomy O x y
      with BooleanOrder.compare O (proj₁ (lower x)) (proj₁ (lower y))
        (proj₂ (lower x)) (proj₂ (lower y))
  ... | inj₁ p = inj₁ (lift p)
  ... | inj₂ (inj₁ e) = inj₂ (inj₁ (Cubical.cong lift (pointPath O e)))
  ... | inj₂ (inj₂ p) = inj₂ (inj₂ (lift p))

  enumeration : (O : BooleanOrder)
    → PartialEnumeration (WosetCarrier (raised ℓ O))
  enumeration O = record
    { sequence = λ n → Maybe.map lift (Order.Order.enum (order O) n)
    ; covers = λ x →
        let found = Order.Order.covers (order O) (lower x)
        in Truncation.∣
             proj₁ found
             , eqToPath
                 (InductiveEquality.cong (Maybe.map lift) (proj₂ found))
           ∣₁
    }

  -- The presentation of O and the presentation of raised ℓ O on its own
  -- carrier have the same points and order; only their equalities differ.
  same : (O : BooleanOrder)
    → presentation ℓ O
        Presented.≃𝒫 toPresentation (raised ℓ O) (trichotomy O)
          (enumeration O)
  same O = record
    { to = λ x → x
    ; from = λ x → x
    ; to-≈ = λ p → Cubical.cong lift (eqToPath (lower p))
    ; from-≈ = λ p → lift (pathToEq (Cubical.cong lower p))
    ; to-< = λ p → p
    ; from-< = λ p → p
    ; from-to-≈ = λ x → lift InductiveEquality.refl
    ; to-from-≈ = λ x → Cubical.refl
    }

  presented : (ℓ : Level) (O : BooleanOrder)
    → WosetEquiv (orderType (presentation ℓ O)) (raised ℓ O)
  presented ℓ O =
    compWosetEquiv
      (orderType-equivalence (same O))
      (invEq (WosetPath _ _)
        (toPresentation-orderType (raised ℓ O) (trichotomy O)
          (enumeration O)))

  -- One Boolean order at two levels.
  levels : (ℓ ℓ′ : Level) (O : BooleanOrder)
    → WosetEquiv
        (orderType (presentation ℓ O))
        (orderType (presentation ℓ′ O))
  levels ℓ ℓ′ O =
    compWosetEquiv (presented ℓ O)
      (compWosetEquiv (invWosetEquiv (raise-equivalence ℓ ℓ (well-order O)))
        (compWosetEquiv (raise-equivalence ℓ′ ℓ′ (well-order O))
          (invWosetEquiv (presented ℓ′ O))))

------------------------------------------------------------------------
-- Ω, and ω₁(ℓ) ≃ Ω

-- Mathematical shape: Ω = sup (O : BooleanOrder), ord(O) : Woset(0, 0).
Ω : Woset lzero lzero
Ω = Supremum.supremum {I = BooleanOrder} (presentation lzero)

private
  Ω′ : (ℓ : Level) → Woset ℓ ℓ
  Ω′ ℓ = raise ℓ ℓ Ω

  -- ord(P) ≺ Ω′(ℓ) for every P : 𝒫 ℓ: P + 1 is equivalent to the
  -- presentation of a Boolean order, whose order type lies below Ω.
  strict : (P : 𝒫 ℓ) → orderType P ≺ Ω′ ℓ
  strict {ℓ} P =
    ≺Trans≼ (orderType P) (orderType next) (Ω′ ℓ)
      (successor-strict P)
      (isTrans≼ (orderType next) (orderType (presentation lzero O)) (Ω′ ℓ)
        (WosetEquiv→≼
          (compWosetEquiv
            (orderType-equivalence (Boolean.equivalence next))
            (levels ℓ lzero O)))
        (isTrans≼ (orderType (presentation lzero O)) Ω (Ω′ ℓ)
          (Supremum.upper (presentation lzero) O)
          (WosetEquiv→≼ (raise-equivalence ℓ ℓ Ω))))
    where
      next = Successor.successor P
      O = Boolean.normal next

  -- Every principal segment of Ω′(ℓ) is merely presented at level ℓ: it is
  -- a segment of the order type of some Boolean order, whose presentation
  -- at level ℓ presents it by a lower cone.
  segment : (k : WosetCarrier (Ω′ ℓ)) → MerelyPresented (Ω′ ℓ ↓ k)
  segment {ℓ} k =
    Truncation.rec (isPropMerelyPresented (Ω′ ℓ ↓ k)) member
      (Supremum.covered (presentation lzero) (lower k))
    where
      member : Σ BooleanOrder (λ O →
          Σ (WosetCarrier (orderType (presentation lzero O))) λ x →
            WosetEquiv (Ω ↓ lower k) (orderType (presentation lzero O) ↓ x))
        → MerelyPresented (Ω′ ℓ ↓ k)
      member (O , x , e) =
        let change = invWosetEquiv (levels ℓ lzero O)
            y = equivFun (Cubical.fst change) x
        in
        Truncation.map
          (λ found →
            proj₁ found
            , compWosetEquiv (proj₂ found)
                (compWosetEquiv (invWosetEquiv (↓RespectsEquiv change x))
                  (compWosetEquiv (invWosetEquiv e)
                    (↓RespectsEquiv (raise-equivalence ℓ ℓ Ω) (lower k)))))
          (segment-presented (presentation ℓ O)
            (orderType (presentation ℓ O) ↓ y)
            (↓Decreasing (orderType (presentation ℓ O)) y))

  -- ω₁(ℓ) ≼ Ω′(ℓ) by leastness, Ω′(ℓ) ≼ ω₁(ℓ) by the cut.  The level of
  -- isOmegaOneCut is given explicitly: inferred, Agda unfolds the
  -- canonical geometry to solve it (OG log, 2026-10-06).
  equivalence : WosetEquiv (ω₁ ℓ) (Ω′ ℓ)
  equivalence {ℓ} =
    isAntisym≼Equiv (ω₁ ℓ) (Ω′ ℓ)
      (Specification.large-least (Ω′ ℓ) strict)
      (segments→simulation {H = Ω′ ℓ} {K = ω₁ ℓ}
        λ k → Cubical.snd
          (Specification.cut-strict {H = ω₁ ℓ}
            (Specification.isOmegaOneCut {ℓ}) (Ω′ ℓ ↓ k))
          (segment k))

-- Mathematical shape: ω₁(ℓ) ≃ Ω, a well-order in the lowest universe.
small : (ℓ : Level) → WosetEquiv (ω₁ ℓ) Ω
small ℓ = compWosetEquiv equivalence (invWosetEquiv (raise-equivalence ℓ ℓ Ω))

-- Mathematical shape: ω₁(ℓ) ≃ ω₁(ℓ′).
level : (ℓ ℓ′ : Level) → WosetEquiv (ω₁ ℓ) (ω₁ ℓ′)
level ℓ ℓ′ = compWosetEquiv (small ℓ) (invWosetEquiv (small ℓ′))

------------------------------------------------------------------------
-- ω₁ in the ordinal of ordinals

-- Mathematical shape: ω₁(ℓ) ≃ Ord(ℓ) ↓ Ω′, so ω₁(ℓ) is a principal
-- segment of Ord(ℓ).
principal : ω₁ ℓ ≺ Ord ℓ
principal {ℓ} =
  Ω′ ℓ
  , compWosetEquiv (invWosetEquiv (lowerset (Ω′ ℓ)))
      (invWosetEquiv equivalence)

-- Mathematical shape: α ≺ Ω′ ≃ MerelyPresented(α) for α in Ord(ℓ).  The
-- well-orders of ≺RespectsEquivR are given: inferred through WosetEquiv,
-- they make Agda evaluate ω₁(ℓ).
below : (α : Woset ℓ ℓ) → (α ≺ raise ℓ ℓ Ω) ≃ MerelyPresented α
below {ℓ} α =
  compEquiv
    (propBiimpl→Equiv
      (isPropValued≺ α (Ω′ ℓ))
      (isPropValued≺ α (ω₁ ℓ))
      (≺RespectsEquivR α {B = Ω′ ℓ} {C = ω₁ ℓ}
        (invWosetEquiv equivalence))
      (≺RespectsEquivR α {B = ω₁ ℓ} {C = Ω′ ℓ} equivalence))
    (Specification.cut-strict-equivalence {H = ω₁ ℓ}
      (Specification.isOmegaOneCut {ℓ}) α)

-- The points of Ord(ℓ) whose predecessors are exactly the merely
-- presented well-orders.
CutPoint : (ℓ : Level) → Set (lsuc ℓ)
CutPoint ℓ =
  Σ (Woset ℓ ℓ) λ K → (α : Woset ℓ ℓ) → (α ≺ K) ≃ MerelyPresented α

-- Mathematical shape: isContr(CutPoint ℓ), with center Ω′ (below), by
-- extensionality of Ord(ℓ).
cutPoint-isContr : isContr (CutPoint ℓ)
cutPoint-isContr {ℓ} =
  (Ω′ ℓ , below)
  , λ other →
      Σ≡Prop
        (λ K → isPropΠ λ α →
          isOfHLevel≃ 1 (isPropValued≺ α K) (isPropMerelyPresented α))
        (isWeaklyExtensional→≺Equiv→≡ _≺_ isWeaklyExtensional≺
          (Ω′ ℓ) (proj₁ other)
          λ α → compEquiv (below α) (invEquiv (proj₂ other α)))
