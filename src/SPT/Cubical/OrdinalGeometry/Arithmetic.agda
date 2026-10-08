{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic where

-- Table 1 of Kraus, Nordvall Forsberg and Xu in ordinal geometry, every
-- row with the datum it uses. The ordinals of one presentation W are its
-- points x, read as their domains ∂x, with x < y the principal cone
-- ∂x ⊂ ∂y (Arithmetic.Ambient). Rows W states the order rows for them,
-- with any further datum (a local shape, an ω-point, a placement) in the
-- type of its field, and rows inhabits it for every W. Rows 10–12 need no
-- datum: +, · and ω^ satisfy their specifications on all presentations
-- and are unique at hereditary arguments. Strength is the other column:
-- each row asked of all presentations without its datum. This module is a
-- stable re-export; modules of the geometry import the defining modules.

open import Agda.Primitive using (Level; lsuc; lzero)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Nullary using (Dec)

open import SPT.Cubical.Core.WellFounded using (WellFounded)
import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
open import SPT.Cubical.OrdinalGeometry.Presentation.Sum using (_+_; ∂)
import SPT.Cubical.OrdinalGeometry.Presentation.Limit as Limit
import SPT.Cubical.OrdinalGeometry.Presentation.Limit.Discriminator as Stream
open import SPT.Cubical.OrdinalGeometry.Operation.Exponential using (exp)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization using
  (Zero; pointless; Strong; module Successors; Supremum; Increasing)
open import
  SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization.Discriminator
  using (WLPO)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization.Strength
  as CharacterizationStrength
import SPT.Cubical.OrdinalGeometry.Arithmetic.Successor as Successor
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Multiplication using (_·_)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Exponential using (omega)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Subtraction as Subtraction
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Division using
  (Division; Placement; divide; place; unique)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Division.Discriminator
  as DivisionDiscriminator
import SPT.Cubical.OrdinalGeometry.Arithmetic.Cone as Cone
import SPT.Cubical.OrdinalGeometry.Arithmetic.Ambient as Ambient
open Ambient using (pair)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Classification using
  (Classified)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Classification.Induction
  using
  (Hereditary)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Classification.Induction
  as Induction
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Classification.Local using
  (Local)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Classification.Local as Shapes
import SPT.Cubical.OrdinalGeometry.Arithmetic.Classification.Discriminator
  as ClassificationDiscriminator
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Uniqueness using
  (IsAddition; IsMultiplication; IsExponential)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Uniqueness as Uniqueness
import SPT.Cubical.OrdinalGeometry.Arithmetic.Comparison.Strength
  as ComparisonStrength

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- The ordinals of one ambient

-- The rows for the ordinals of W, inhabited for every W by `rows`.  With
-- x < y read as Segment (∂x) (∂y) and x ≤ y as Initial (∂x) (∂y), the
-- reading x ↦ ∂x reflects < and ≈, and rows 1–9 and 13–18 hold.  The
-- successor ∂x + 1, limits and suprema are presentations, in general not
-- domains of points of W, so monotonicity of the successor for < is not
-- stated: ∂y + 1 leaves W, and no splitting is available there.
record Rows {ℓ : Level} (W : 𝒫 ℓ) : Set (lsuc ℓ) where
  field
    -- The reading x ↦ ∂x.
    segment : {x y : 𝒫.X W} → 𝒫._<_ W x y
      → Maps.Segment (∂ W x) (∂ W y)
    reflect : {x y : 𝒫.X W} → Maps.Segment (∂ W x) (∂ W y)
      → 𝒫._<_ W x y
    same : {x y : 𝒫.X W} → 𝒫._≈_ W x y → ∂ W x Presented.≃𝒫 ∂ W y
    injective : {x y : 𝒫.X W} → ∂ W x Presented.≃𝒫 ∂ W y → 𝒫._≈_ W x y

    -- 1. x < y ≤ z → x < z.
    <-≤-trans : {x y z : 𝒫.X W} → Maps.Segment (∂ W x) (∂ W y)
      → Maps.Initial (∂ W y) (∂ W z) → Maps.Segment (∂ W x) (∂ W z)

    -- 2. x ≤ y < z → x < z.
    ≤-<-trans : {x y z : 𝒫.X W} → Maps.Initial (∂ W x) (∂ W y)
      → Maps.Segment (∂ W y) (∂ W z) → Maps.Segment (∂ W x) (∂ W z)

    -- 3. Well-founded.
    wf : WellFounded (λ x y → Maps.Segment (∂ W x) (∂ W y))

    -- 4. Extensional: points with the same predecessors.
    extensional : {x y : 𝒫.X W} → Presented.Presentation._≈↓_ W x y
      → ∂ W x Presented.≃𝒫 ∂ W y

    -- 5. Zero and successors. A point with nothing below has a zero
    -- domain; ∂x + 1 is the strong successor, and it is ∂y when y follows
    -- x immediately in W; x < y ⇔ x + 1 ≤ y; the successor is monotone
    -- for ≤.
    zero : (x : 𝒫.X W) → ((z : 𝒫.X W) → 𝒫._<_ W z x → ⊥) → Zero (∂ W x)
    successor : (x : 𝒫.X W)
      → Strong (∂ W x) (Maps.Successor.next (∂ W x))
    immediate : {x y : 𝒫.X W} → 𝒫._<_ W x y
      → ((z : 𝒫.X W) → 𝒫._<_ W z y → 𝒫._<_ W z x ⊎ 𝒫._≈_ W z x)
      → Strong (∂ W x) (∂ W y)
    <⇔suc≤ : {x y : 𝒫.X W}
      → Maps.Segment (∂ W x) (∂ W y)
        ⇔ Maps.Initial (Maps.Successor.next (∂ W x)) (∂ W y)
    successor-initial : {x y : 𝒫.X W} → Maps.Initial (∂ W x) (∂ W y)
      → Maps.Initial (Maps.Successor.next (∂ W x))
          (Maps.Successor.next (∂ W y))

    -- 6. Binary joins: the domain of the larger point.
    join : (x y : 𝒫.X W)
      → Σ (𝒫.X W) (λ z → Supremum (pair (∂ W x) (∂ W y)) (∂ W z))

    -- 7. Limits of strictly ascending points, strictly above each.
    limit : (f : ℕ → 𝒫.X W) → ((n : ℕ) → 𝒫._<_ W (f n) (f (suc n)))
      → Σ (𝒫 ℓ) (λ L → Supremum (λ n → ∂ W (f n)) L
          × ((n : ℕ) → Maps.Segment (∂ W (f n)) L))

    -- 8. Suprema of ℕ-sequences of points.
    supremum : (f : ℕ → 𝒫.X W) → Σ (𝒫 ℓ) (Supremum (λ n → ∂ W (f n)))

    -- 9. Classification, from the local shape at the point.
    classify : (x : 𝒫.X W) → Local W x → Classified (∂ W x)

    -- 13. Subtraction: ∂x ≤ ∂y gives ∂x + R ≃ ∂y.
    subtract : {x y : 𝒫.X W} → Maps.Initial (∂ W x) (∂ W y)
      → Σ (𝒫 ℓ) (λ R → (∂ W x + R) Presented.≃𝒫 ∂ W y)

    -- 14. Division, exactly from a placement, and unique.
    division : (x : 𝒫.X W) (D : 𝒫 ℓ)
      → Placement (∂ W x) D ⇔ Division (∂ W x) D
    quotients : (x : 𝒫.X W) (D : 𝒫 ℓ) (a b : Division (∂ W x) D)
      → (Division.quotient a Presented.≃𝒫 Division.quotient b)
        × (Division.remainder a Presented.≃𝒫 Division.remainder b)

    -- 15. ∂x < ω decided, from a point w with ∂w ≃ ω.
    finite : (w : 𝒫.X W) → ∂ W w Presented.≃𝒫 omega → (x : 𝒫.X W)
      → Maps.Segment (∂ W x) omega ⊎ Maps.Initial omega (∂ W x)

    -- 16. ∂x < ∂y decided.
    decidable : (x y : 𝒫.X W) → Dec (Maps.Segment (∂ W x) (∂ W y))

    -- 17. ≤ splits into < or ≃.
    split : {x y : 𝒫.X W} → Maps.Initial (∂ W x) (∂ W y)
      → Maps.Segment (∂ W x) (∂ W y) ⊎ ∂ W x Presented.≃𝒫 ∂ W y

    -- 18. Trichotomy.
    trichotomy : (x y : 𝒫.X W)
      → Maps.Segment (∂ W x) (∂ W y)
        ⊎ (∂ W x Presented.≃𝒫 ∂ W y ⊎ Maps.Segment (∂ W y) (∂ W x))

private
  -- The limit of the domains of strictly ascending points.
  limit : (W : 𝒫 ℓ) (f : ℕ → 𝒫.X W)
    → ((n : ℕ) → 𝒫._<_ W (f n) (f (suc n)))
    → Σ (𝒫 ℓ) (λ L → Supremum (λ n → ∂ W (f n)) L
        × ((n : ℕ) → Maps.Segment (∂ W (f n)) L))
  limit W f up =
    Increasing.limit s , Increasing.supremum s , Increasing.strict s
    where
    s : Increasing _
    s = Ambient.ascending W f up

rows : (W : 𝒫 ℓ) → Rows W
rows W = record
  { segment = λ {x} {y} → Ambient.segment W {x} {y}
  ; reflect = λ {x} {y} → Ambient.reflect W {x} {y}
  ; same = λ {x} {y} → Ambient.same W {x} {y}
  ; injective = λ {x} {y} → Cone.injective W {x} {y}
  ; <-≤-trans = λ {x} {y} {z} →
      Maps.along {P = ∂ W x} {Q = ∂ W y} {R = ∂ W z}
  ; ≤-<-trans = λ {x} {y} {z} → Ambient.along W {x} {y} {z}
  ; wf = Ambient.wf W
  ; extensional = λ {x} {y} e →
      Ambient.same W {x} {y} (Presented.Presentation.≈↓→≈ W e)
  ; zero = λ x none →
      pointless {Z = ∂ W x} λ u → none (proj₁ u) (proj₂ u)
  ; successor = λ x → Successors.next (∂ W x)
  ; immediate = λ {x} {y} → Induction.immediate W {x} {y}
  ; <⇔suc≤ = λ {x} {y} → mk⇔
      (Maps.Segment.closed {P = ∂ W x} {Q = ∂ W y})
      (Successor.segment {P = ∂ W x} {Q = ∂ W y})
  ; successor-initial = λ {x} {y} → Ambient.successor-initial W {x} {y}
  ; join = λ x y → proj₁ (Ambient.max W x y) , Ambient.join W x y
  ; limit = limit W
  ; supremum = λ f → Limit.completion (Ambient.chain W f) ,
      Ambient.supremum W f
  ; classify = Shapes.classify W
  ; subtract = λ {x} {y} f →
      Subtraction.subtract {P = ∂ W x} {Q = ∂ W y}
        (Ambient.split W {x} {y} f)
  ; division = λ x D →
      mk⇔ (divide {P = ∂ W x} {D = D}) (place {P = ∂ W x} {D = D})
  ; quotients = λ x D → unique {P = ∂ W x} {D = D}
  ; finite = Ambient.finite? W
  ; decidable = Ambient.decidable W
  ; split = λ {x} {y} → Ambient.split W {x} {y}
  ; trichotomy = Ambient.compare W
  }

------------------------------------------------------------------------
-- Rows 10–12: arithmetic of presentations

-- +, · and ω^ satisfy the specifications of Definitions 12–14, read with
-- ≃𝒫, on all presentations; any operation satisfying one agrees with them
-- at hereditary arguments (Theorems 28 and 42).

addition : IsAddition {ℓ} _+_
addition = Uniqueness.addition

multiplication : IsMultiplication {ℓ} _·_
multiplication = Uniqueness.multiplication

exponential : IsExponential {ℓ} exp
exponential = Uniqueness.exponential

unique-addition : {_⊕_ : 𝒫 ℓ → 𝒫 ℓ → 𝒫 ℓ} → IsAddition _⊕_
  → (P : 𝒫 ℓ) {Q : 𝒫 ℓ} → Hereditary Q → (P ⊕ Q) Presented.≃𝒫 (P + Q)
unique-addition = Uniqueness.unique-addition

unique-multiplication : {_⊙_ : 𝒫 ℓ → 𝒫 ℓ → 𝒫 ℓ}
  → IsMultiplication _⊙_
  → (P : 𝒫 ℓ) {Q : 𝒫 ℓ} → Hereditary Q → (P ⊙ Q) Presented.≃𝒫 (P · Q)
unique-multiplication = Uniqueness.unique-multiplication

unique-exponential : {e : 𝒫 ℓ → 𝒫 ℓ} → IsExponential e
  → {P : 𝒫 ℓ} → Hereditary P → e P Presented.≃𝒫 exp P
unique-exponential = Uniqueness.unique-exponential

------------------------------------------------------------------------
-- The rows without their datum

-- The rows without their datum, inhabited by `strength`: each row asked
-- of all presentations at level zero, where the discriminators are.  Rows
-- 2, 5, 6, 8, 13 and 15–18, with comparability, Dec ≤, Dec ≃ and strict
-- bounds of sequences, are each equivalent to LPO; Dec Zero is equivalent
-- to WLPO and Dec (P ≃ ω) to LPO.  Rows 9 and 14 give LPO; their converses
-- are not addressed.
record Strength : Set₁ where
  field
    comparable : Stream.LPO
      ⇔ ((P Q : 𝒫 lzero) → Maps.Initial P Q ⊎ Maps.Segment Q P)
    initial : Stream.LPO ⇔ ((P Q : 𝒫 lzero) → Dec (Maps.Initial P Q))
    equivalent : Stream.LPO
      ⇔ ((P Q : 𝒫 lzero) → Dec (P Presented.≃𝒫 Q))
    bound : Stream.LPO
      ⇔ ((F : ℕ → 𝒫 lzero)
          → Σ (𝒫 lzero) (λ S → (n : ℕ) → Maps.Segment (F n) S))

    -- 2.
    ≤-<-trans : Stream.LPO
      ⇔ ((P Q R : 𝒫 lzero) → Maps.Initial P Q → Maps.Segment Q R
          → Maps.Segment P R)

    -- 5.
    zero : WLPO ⇔ ((P : 𝒫 lzero) → Dec (Zero P))
    successor-initial : Stream.LPO
      ⇔ ((P Q : 𝒫 lzero) → Maps.Initial P Q
          → Maps.Initial (Maps.Successor.next P) (Maps.Successor.next Q))
    successor-segment : Stream.LPO
      ⇔ ((P Q : 𝒫 lzero) → Maps.Segment P Q
          → Maps.Segment (Maps.Successor.next P) (Maps.Successor.next Q))

    -- 6 and 8.
    join : Stream.LPO
      ⇔ ((P Q : 𝒫 lzero) → Σ (𝒫 lzero) (Supremum (pair P Q)))
    supremum : Stream.LPO
      ⇔ ((F : ℕ → 𝒫 lzero) → Σ (𝒫 lzero) (Supremum F))

    -- 9, lower bounds.
    classified : ((P : 𝒫 lzero) → Classified P) → Stream.LPO
    shaped : ((V : 𝒫 lzero) (x : 𝒫.X V) → Local V x) → Stream.LPO

    -- 13.
    subtract : Stream.LPO
      ⇔ ((P Q : 𝒫 lzero) → Maps.Initial P Q
          → Σ (𝒫 lzero) (λ R → (P + R) Presented.≃𝒫 Q))

    -- 14, lower bound.
    division : ((P D : 𝒫 lzero) → 𝒫.X D → Division P D) → Stream.LPO

    -- 15, and equality with ω.
    finite : Stream.LPO
      ⇔ ((P : 𝒫 lzero) → Dec (Maps.Segment P omega))
    omega-equivalent : Stream.LPO
      ⇔ ((P : 𝒫 lzero) → Dec (P Presented.≃𝒫 omega))

    -- 16–18.
    decidable : Stream.LPO
      ⇔ ((P Q : 𝒫 lzero) → Dec (Maps.Segment P Q))
    split : Stream.LPO
      ⇔ ((P Q : 𝒫 lzero) → Maps.Initial P Q
          → Maps.Segment P Q ⊎ P Presented.≃𝒫 Q)
    trichotomy : Stream.LPO
      ⇔ ((P Q : 𝒫 lzero)
          → Maps.Segment P Q ⊎ (P Presented.≃𝒫 Q ⊎ Maps.Segment Q P))

strength : Strength
strength = record
  { comparable = ComparisonStrength.comparable
  ; initial = ComparisonStrength.initial
  ; equivalent = ComparisonStrength.equivalent
  ; bound = ComparisonStrength.bound
  ; ≤-<-trans = ComparisonStrength.along
  ; zero = CharacterizationStrength.zero-strength
  ; successor-initial = ComparisonStrength.successor-initial
  ; successor-segment = ComparisonStrength.successor-segment
  ; join = ComparisonStrength.join
  ; supremum = ComparisonStrength.supremum
  ; classified = ClassificationDiscriminator.classified
  ; shaped = ClassificationDiscriminator.shaped
  ; subtract = ComparisonStrength.remainder
  ; division = DivisionDiscriminator.division
  ; finite = ComparisonStrength.finite
  ; omega-equivalent = CharacterizationStrength.omega-strength
  ; decidable = ComparisonStrength.decidable
  ; split = ComparisonStrength.split
  ; trichotomy = ComparisonStrength.trichotomy
  }
