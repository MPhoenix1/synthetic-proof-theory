{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Ambient where

-- The ordinals of one ambient presentation W, in the von Neumann
-- presentation: a point x of W is the ordinal ∂x, its predecessor domain,
-- and x < y is the principal cone ∂x ⊂ ∂y. Placed in W, the properties
-- that otherwise need supplied data hold outright, because comparison in W
-- supplies the placement:
-- - a proper segment ∂x ⊂ ∂y comes from x < y, so proper segments of
--   domains are well-founded;
-- - the domains are trichotomous, every initial map ∂x → ∂y splits into a
--   proper segment or an equivalence, so ≤ followed by < is <, and the
--   successor is monotone for ≤;
-- - ∂x < ∂y is decided, and x < α for every α = ∂w placed in W; for
--   ∂w ≃ ω this is finiteness;
-- - strictly ascending points have strictly increasing domains;
-- - ∂(max x y) is the join of ∂x and ∂y, and the cones at the running
--   maxima of a sequence of points complete to its supremum;
-- - x ≤ y gives ∂y ≃ ∂x + R;
-- - the domain of a point of a multiple D · V divides by D, and a division
--   of P by D places P as the domain of a point of a multiple.

open import Agda.Primitive using (Level)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Nullary using (Dec; yes; no)

open import SPT.Cubical.Core.WellFounded using (WellFounded)
open import SPT.Cubical.Core.WellFounded.Subrelation using (subrel-wf)
import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Principal as Principal
import SPT.Cubical.OrdinalGeometry.Presentation.Successor as Adjoin
open import SPT.Cubical.OrdinalGeometry.Presentation.Sum using
  (_+_; ∂; ceiling-cone)
import SPT.Cubical.OrdinalGeometry.Presentation.Limit as Limit
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization as Normal
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization using
  (bijection; Supremum; Increasing)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization
  as Characterization
import SPT.Cubical.OrdinalGeometry.Arithmetic.Successor as Successor
import SPT.Cubical.OrdinalGeometry.Arithmetic.Addition as Addition
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Multiplication using
  (_·_; point)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Multiplication as Multiplication
import SPT.Cubical.OrdinalGeometry.Arithmetic.Subtraction as Subtraction
import SPT.Cubical.OrdinalGeometry.Arithmetic.Cone as Cone
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Division using (Division)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Exponential using (omega)

private
  variable
    ℓ : Level

-- Two presentations as a sequence: P first, then Q.
pair : 𝒫 ℓ → 𝒫 ℓ → ℕ → 𝒫 ℓ
pair P Q zero = P
pair P Q (suc _) = Q

module _ {ℓ : Level} (W : 𝒫 ℓ) where

  private
    module W = 𝒫 W
    module Laws = Presented.Presentation W

  ----------------------------------------------------------------------
  -- Order

  -- Mathematical shape: x ≤ y := x < y ⊎ x ≈ y.
  _≤_ : W.X → W.X → Set ℓ
  x ≤ y = x W.< y ⊎ x W.≈ y

  -- Equivalent points have equivalent domains.
  same : {x y : W.X} → x W.≈ y → ∂ W x Presented.≃𝒫 ∂ W y
  same p = record
    { to = λ u → proj₁ u , W.<-respʳ-≈ p (proj₂ u)
    ; from = λ v → proj₁ v , W.<-respʳ-≈ (W.≈-sym p) (proj₂ v)
    ; to-≈ = λ q → q
    ; from-≈ = λ q → q
    ; to-< = λ q → q
    ; from-< = λ q → q
    ; from-to-≈ = λ u → W.≈-refl (proj₁ u)
    ; to-from-≈ = λ v → W.≈-refl (proj₁ v)
    }

  -- Mathematical shape: x < y gives the principal cone ∂x ⊂ ∂y, with
  -- ceiling x.
  segment : {x y : W.X} → x W.< y → Maps.Segment (∂ W x) (∂ W y)
  segment {x} {y} p = record
    { bound = record
        { to = λ u → proj₁ u , W.<-trans (proj₂ u) p
        ; to-≈ = λ q → q
        ; to-< = λ q → q
        ; reflects-< = λ q → q
        ; ceiling = x , p
        ; below = proj₂
        }
    ; covers = λ v q → (proj₁ v , q) , W.≈-refl (proj₁ v)
    }

  -- The inclusion of domains along x ≤ y.
  included : {x y : W.X} → x ≤ y → Maps.Initial (∂ W x) (∂ W y)
  included (inj₁ p) = Maps.inclusion (segment p)
  included (inj₂ q) = Maps.equivalence (same q)

  -- A proper segment ∂x ⊂ ∂y comes from x < y: x ≈ y or y < x would bound
  -- ∂x strictly below itself.
  reflect : {x y : W.X} → Maps.Segment (∂ W x) (∂ W y) → x W.< y
  reflect {x} {y} s with W.compare x y
  ... | inj₁ p = p
  ... | inj₂ (inj₁ q) = ⊥-elim (Presented.Embedding.irrefl (∂ W x)
    (Maps.bounded (Maps.Segment.bound s)
      (Maps.equivalence (same {y} {x} (W.≈-sym q)))))
  ... | inj₂ (inj₂ p) = ⊥-elim (Presented.Embedding.irrefl (∂ W x)
    (Maps.bounded (Maps.Segment.bound s)
      (Maps.inclusion (segment {y} {x} p))))

  -- Proper segments of domains are well-founded, through the order of W.
  wf : WellFounded (λ x y → Maps.Segment (∂ W x) (∂ W y))
  wf = subrel-wf (λ {x} {y} → reflect {x} {y}) W.<-wf

  ----------------------------------------------------------------------
  -- Comparison

  -- The domains of points of W are trichotomous.
  compare : (x y : W.X)
    → Maps.Segment (∂ W x) (∂ W y)
      ⊎ (∂ W x Presented.≃𝒫 ∂ W y ⊎ Maps.Segment (∂ W y) (∂ W x))
  compare x y with W.compare x y
  ... | inj₁ p = inj₁ (segment p)
  ... | inj₂ (inj₁ q) = inj₂ (inj₁ (same q))
  ... | inj₂ (inj₂ p) = inj₂ (inj₂ (segment p))

  -- Every initial map of domains splits into a proper segment or an
  -- equivalence: a reverse proper segment would bound ∂y below itself.
  split : {x y : W.X} → Maps.Initial (∂ W x) (∂ W y)
    → Maps.Segment (∂ W x) (∂ W y) ⊎ ∂ W x Presented.≃𝒫 ∂ W y
  split {x} {y} f with W.compare x y
  ... | inj₁ p = inj₁ (segment p)
  ... | inj₂ (inj₁ q) = inj₂ (same q)
  ... | inj₂ (inj₂ p) = ⊥-elim (Maps.no-reverse
    (Maps.Initial.embedding f) (Maps.Segment.bound (segment p)))

  -- Mathematical shape: ∂x ≤ ∂y < ∂z → ∂x < ∂z; the ≤ splits.
  along : {x y z : W.X} → Maps.Initial (∂ W x) (∂ W y)
    → Maps.Segment (∂ W y) (∂ W z) → Maps.Segment (∂ W x) (∂ W z)
  along {x} {y} {z} f s =
    Characterization.segment {P = ∂ W x} {Q = ∂ W y} {R = ∂ W z}
      (split {x} {y} f) s

  -- Mathematical shape: ∂x ≤ ∂y → ∂x + 1 ≤ ∂y + 1. A proper segment closes
  -- to the successor; an equivalence lifts to it.
  successor-initial : {x y : W.X} → Maps.Initial (∂ W x) (∂ W y)
    → Maps.Initial (Maps.Successor.next (∂ W x))
        (Maps.Successor.next (∂ W y))
  successor-initial {x} {y} f =
    [ (λ s → Maps.compose (Maps.Segment.closed s)
        (Maps.Successor.initial (∂ W y)))
    , (λ e → Maps.equivalence
        (Successor.respect {P = ∂ W x} {P′ = ∂ W y} e))
    ]′ (split {x} {y} f)

  -- ∂x < ∂y is decided, by comparison of x and y in W.
  decidable : (x y : W.X) → Dec (Maps.Segment (∂ W x) (∂ W y))
  decidable x y =
    [ (λ p → yes (segment {x} {y} p))
    , [ (λ q → no λ s → Laws.≈↛< q (reflect {x} {y} s))
      , (λ p → no λ s → Laws.<-asym p (reflect {x} {y} s))
      ]′
    ]′ (W.compare x y)

  -- x < α is decided for α = ∂w placed in W; otherwise α ≤ ∂x.
  below? : (w x : W.X)
    → Maps.Segment (∂ W x) (∂ W w) ⊎ Maps.Initial (∂ W w) (∂ W x)
  below? w x with W.compare x w
  ... | inj₁ p = inj₁ (segment p)
  ... | inj₂ (inj₁ q) = inj₂ (Maps.equivalence (same (W.≈-sym q)))
  ... | inj₂ (inj₂ p) = inj₂ (Maps.inclusion (segment p))

  -- With ∂w ≃ ω, finiteness is decided: ∂x < ω, or ω ≤ ∂x.
  finite? : (w : W.X) → ∂ W w Presented.≃𝒫 omega → (x : W.X)
    → Maps.Segment (∂ W x) omega ⊎ Maps.Initial omega (∂ W x)
  finite? w e x with below? w x
  ... | inj₁ s = inj₁ (Maps.along s (Maps.equivalence e))
  ... | inj₂ f =
    inj₂ (Maps.compose (Maps.equivalence (Presented.≃𝒫-sym e)) f)

  ----------------------------------------------------------------------
  -- Joins and suprema

  -- Mathematical shape: z with x ≤ z and y ≤ z, z being x or y.
  Upper : W.X → W.X → Set ℓ
  Upper x y = Σ W.X (λ z → (x ≤ z) × (y ≤ z) × (z W.≈ x ⊎ z W.≈ y))

  max : (x y : W.X) → Upper x y
  max x y with W.compare x y
  ... | inj₁ p = y , inj₁ p , inj₂ (W.≈-refl y) , inj₂ (W.≈-refl y)
  ... | inj₂ (inj₁ q) =
    x , inj₂ (W.≈-refl x) , inj₂ (W.≈-sym q) , inj₁ (W.≈-refl x)
  ... | inj₂ (inj₂ p) = x , inj₂ (W.≈-refl x) , inj₁ p , inj₁ (W.≈-refl x)

  -- ∂(max x y) is the join of ∂x and ∂y: it is one of them, and each
  -- includes into it.
  join : (x y : W.X)
    → Supremum (pair (∂ W x) (∂ W y)) (∂ W (proj₁ (max x y)))
  join x y with max x y
  ... | z , x≤z , y≤z , which = record { member = member ; least = least }
    where
    member : (n : ℕ) → Maps.Initial (pair (∂ W x) (∂ W y) n) (∂ W z)
    member zero = included x≤z
    member (suc _) = included y≤z

    least : (Q : 𝒫 ℓ)
      → ((n : ℕ) → Maps.Initial (pair (∂ W x) (∂ W y) n) Q)
      → Maps.Initial (∂ W z) Q
    least Q g = choose which
      where
      choose : z W.≈ x ⊎ z W.≈ y → Maps.Initial (∂ W z) Q
      choose (inj₁ q) = Maps.compose (Maps.equivalence (same q)) (g zero)
      choose (inj₂ q) =
        Maps.compose (Maps.equivalence (same q)) (g (suc zero))

  -- The running maximum of a sequence of points.
  peak : (ℕ → W.X) → ℕ → W.X
  peak f zero = f zero
  peak f (suc n) = proj₁ (max (peak f n) (f (suc n)))

  peak-step : (f : ℕ → W.X) (n : ℕ) → peak f n ≤ peak f (suc n)
  peak-step f n = proj₁ (proj₂ (max (peak f n) (f (suc n))))

  peak-above : (f : ℕ → W.X) (n : ℕ) → f n ≤ peak f n
  peak-above f zero = inj₂ (W.≈-refl (f zero))
  peak-above f (suc n) = proj₁ (proj₂ (proj₂ (max (peak f n) (f (suc n)))))

  -- Every running maximum is one of the points.
  peak-from : (f : ℕ → W.X) (n : ℕ) → Σ ℕ (λ k → peak f n W.≈ f k)
  peak-from f zero = zero , W.≈-refl (f zero)
  peak-from f (suc n) with proj₂ (proj₂ (proj₂ (max (peak f n) (f (suc n)))))
  ... | inj₁ q = let k , r = peak-from f n in k , W.≈-trans q r
  ... | inj₂ q = suc n , q

  -- The cones at the running maxima, along their inclusions.
  chain : (ℕ → W.X) → Limit.Chain ℓ
  chain f = record
    { stage = λ n → ∂ W (peak f n)
    ; edge = λ n → included (peak-step f n)
    }

  -- Strictly ascending points have strictly increasing domains; their
  -- limit is a new ambient, which need not be a point of W.
  ascending : (f : ℕ → W.X) → ((n : ℕ) → f n W.< f (suc n)) → Increasing ℓ
  ascending f up = record
    { stage = λ n → ∂ W (f n)
    ; step = λ n → segment {f n} {f (suc n)} (up n)
    }

  -- The completion of the cones at the running maxima is the supremum of
  -- the cones: a new ambient, which need not be a point of W.
  supremum : (f : ℕ → W.X)
    → Supremum (λ n → ∂ W (f n)) (Limit.completion (chain f))
  supremum f = record
    { member = λ n →
        Maps.compose (included (peak-above f n)) (Limit.stage (chain f) n)
    ; least = λ Q g → Limit.least (chain f) Q λ n →
        let k , q = peak-from f n in
        Maps.compose (Maps.equivalence (same q)) (g k)
    }

  ----------------------------------------------------------------------
  -- Subtraction

  -- Mathematical shape: x ≤ y gives ∂y ≃ ∂x + R.
  subtract : {x y : W.X} → x ≤ y
    → Σ (𝒫 ℓ) (λ R → (∂ W x + R) Presented.≃𝒫 ∂ W y)
  subtract (inj₁ p) = Subtraction.subtract (inj₁ (segment p))
  subtract (inj₂ q) = Subtraction.subtract (inj₂ (same q))

------------------------------------------------------------------------
-- Division in a multiple

-- The domain of the point (v, d) of D · V divides by D, with quotient ∂v
-- and remainder ∂d.
divide : (D V : 𝒫 ℓ) (v : Normal.Point V) (d : Normal.Point D)
  → Division (∂ (D · V) (point D V v d)) D
divide D V v d = record
  { quotient = Cone.domain V v
  ; remainder = Cone.domain D d
  ; equation = Cone.product D V v d
  ; below = Cone.inside D d
  }

-- A proper segment R ⊂ D is the domain of its ceiling.
ceiling-domain : {R D : 𝒫 ℓ} (s : Maps.Segment R D)
  → R Presented.≃𝒫
    ∂ D (Presented._≺𝒫_.ceiling (Maps.Segment.bound s))
ceiling-domain s = bijection (ceiling-cone s) λ v →
  Maps.Segment.covers s (proj₁ v) (proj₂ v)

-- A division of P by D places P as the domain of the point (top, c) of
-- D · (Q + 1), where c is the ceiling of the remainder:
--   ∂(top, c) ≃ D · ∂top + ∂c ≃ D · Q + R ≃ P.
place : {P D : 𝒫 ℓ} (a : Division P D)
  → Σ (𝒫 ℓ) (λ V → Σ (Normal.Point V) (λ v → Σ (Normal.Point D) (λ d →
      ∂ (D · V) (point D V v d) Presented.≃𝒫 P)))
place {ℓ} {D = D} a = N , Normal.class N Entry.top ,
  Normal.class D c , Presented.≃𝒫-trans
    (Presented.≃𝒫-sym
      (Cone.product D N (Normal.class N Entry.top) (Normal.class D c)))
    (Presented.≃𝒫-trans
      (Addition.equivalence (Multiplication.equivalence D quotient)
        remainder)
      (Division.equation a))
  where
  Q : 𝒫 ℓ
  Q = Division.quotient a

  N : 𝒫 ℓ
  N = Maps.Successor.next Q

  module Entry = Presented.Diagonal.Successor
    (Adjoin.constant Q) zero

  c : 𝒫.X D
  c = Presented._≺𝒫_.ceiling (Maps.Segment.bound (Division.below a))

  -- The top of Q + 1 has exactly Q below it.
  quotient : Cone.domain N (Normal.class N Entry.top) Presented.≃𝒫 Q
  quotient = Presented.≃𝒫-trans
    (same N (Normal.representative-class N Entry.top))
    (Presented.≃𝒫-sym (Principal.Successor.Top.presentation Q))

  -- The ceiling of R ⊂ D has exactly R below it.
  remainder : Cone.domain D (Normal.class D c)
    Presented.≃𝒫 Division.remainder a
  remainder = Presented.≃𝒫-trans
    (same D (Normal.representative-class D c))
    (Presented.≃𝒫-sym (ceiling-domain (Division.below a)))
