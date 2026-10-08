{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Division where

-- Euclidean division of P by D: P ≃ D · Q + R with R a proper segment of
-- D. A division is exactly a placement: a quotient Q with an initial map
-- D · Q → P whose image is decided and whose remainder is a proper segment
-- of D. Quotient and remainder are unique up to ≃𝒫, by well-founded
-- recursion on P along ≺𝒫. Let c be the ceiling of the remainder of the
-- first division. The point (x, c) has the domain D · ∂x + ∂c, so the two
-- divisions of P give two divisions of that domain, which lies strictly
-- below P. Hence (x, c) lands at (x′, c) for an x′ with ∂x ≃ ∂x′; landing
-- in the other remainder would put P strictly below itself.

open import Agda.Primitive using (Level; lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; sym; trans; subst; subst₂)

open import SPT.Cubical.Core.WellFounded using (Acc; acc)
import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Principal as Principal
open import SPT.Cubical.OrdinalGeometry.Presentation.Sum
  using (_+_; ∂; cone; left)
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization as Normal
open import SPT.Cubical.OrdinalGeometry.Operation.Normal using (precompose)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization using
  (bijection)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Addition as Addition
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Multiplication using
  (_·_; point)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Multiplication as Multiplication
import SPT.Cubical.OrdinalGeometry.Arithmetic.Subtraction as Subtraction
import SPT.Cubical.OrdinalGeometry.Arithmetic.Cone as Cone

private
  variable
    ℓ : Level
    P D : 𝒫 ℓ

------------------------------------------------------------------------
-- Divisions and placements

-- Mathematical shape: P ≃ D · Q + R with R < D.
record Division (P D : 𝒫 ℓ) : Set (lsuc ℓ) where
  field
    quotient : 𝒫 ℓ
    remainder : 𝒫 ℓ
    equation : ((D · quotient) + remainder) Presented.≃𝒫 P
    below : Maps.Segment remainder D

-- A placement of D-blocks in P: a quotient with an initial map D · Q → P
-- whose image is decided and whose remainder is a proper segment of D.
record Placement (P D : 𝒫 ℓ) : Set (lsuc ℓ) where
  field
    quotient : 𝒫 ℓ
    scale : Maps.Initial (D · quotient) P
    decided : Subtraction.Decided scale
    below : Maps.Segment (Subtraction.remainder scale decided) D

-- A placement divides P, with the remainder of the subtraction.
divide : Placement P D → Division P D
divide p = record
  { quotient = Placement.quotient p
  ; remainder =
      Subtraction.remainder (Placement.scale p) (Placement.decided p)
  ; equation =
      Subtraction.equation (Placement.scale p) (Placement.decided p)
  ; below = Placement.below p
  }

-- Every division is a placement: its blocks enter P as the left summand.
place : Division P D → Placement P D
place d = record
  { quotient = Division.quotient d
  ; scale = Subtraction.summand (Division.equation d)
  ; decided = Subtraction.split (Division.equation d)
  ; below = precompose
      (Presented.≃𝒫-sym (Subtraction.complement (Division.equation d)))
      (Division.below d)
  }

------------------------------------------------------------------------
-- Uniqueness of the remainder

-- Divisions with equivalent quotients have equivalent remainders: both
-- are the remainder along the one initial map D · Q → P.
remainders : (a b : Division P D)
  → Division.quotient a Presented.≃𝒫 Division.quotient b
  → Division.remainder a Presented.≃𝒫 Division.remainder b
remainders {P = P} {D = D} a b h = Presented.≃𝒫-trans
  (Subtraction.complement (Division.equation a))
  (Presented.≃𝒫-trans
    (Subtraction.respect f g
      (Subtraction.split (Division.equation a))
      (Subtraction.split (Division.equation b)) fg gf)
    (Presented.≃𝒫-sym (Subtraction.complement (Division.equation b))))
  where
  f : Maps.Initial (D · Division.quotient a) P
  f = Subtraction.summand (Division.equation a)

  g : Maps.Initial (D · Division.quotient b) P
  g = Subtraction.summand (Division.equation b)

  k : (D · Division.quotient a) Presented.≃𝒫 (D · Division.quotient b)
  k = Multiplication.equivalence D h

  module K = Presented._≃𝒫_ k

  -- Initial maps into P agree.
  agree : (u : 𝒫.X (D · Division.quotient a))
    → 𝒫._≈_ P (Maps.Initial.map f u) (Maps.Initial.map g (K.to u))
  agree = Maps.Uniqueness.pointwise f
    (Maps.compose (Maps.equivalence k) g)

  fg : (y : 𝒫.X P) → Subtraction.Above f y → Subtraction.Above g y
  fg y a v = 𝒫.<-respˡ-≈ P
    (𝒫.≈-trans P (agree (K.from v))
      (Maps.Initial.resp g (K.to-from-≈ v)))
    (a (K.from v))

  gf : (y : 𝒫.X P) → Subtraction.Above g y → Subtraction.Above f y
  gf y b u = 𝒫.<-respˡ-≈ P (𝒫.≈-sym P (agree u)) (b (K.to u))

------------------------------------------------------------------------
-- Uniqueness of the quotient

private
  -- A division of P whose quotient is the domain of a point of another
  -- quotient lies strictly below P:
  --   D · ∂x + V < D · ∂x + D ≃ D · (∂x + 1) ≤ D · X ≤ D · X + Y.
  shorter : {X Y W V : 𝒫 ℓ} (x : Normal.Point X)
    → ((D · X) + Y) Presented.≃𝒫 P
    → ((D · W) + V) Presented.≃𝒫 P
    → W Presented.≃𝒫 Cone.domain X x
    → Maps.Segment V D
    → ⊥
  shorter {D = D} {P = P} {X = X} {Y = Y} {W = W} {V = V} x e e′ h s =
    Presented.Embedding.irrefl P (Maps.Segment.bound loop)
    where
    lower : Maps.Segment
      ((D · Cone.domain X x) + V) ((D · Cone.domain X x) + D)
    lower = Addition.segment (D · Cone.domain X x) s

    upper : Maps.Initial ((D · Cone.domain X x) + D) P
    upper = Maps.compose
      (Maps.equivalence (Presented.≃𝒫-sym
        (Multiplication.next D (Cone.domain X x))))
      (Maps.compose
        (Multiplication.initial D (Maps.Segment.closed (Cone.inside X x)))
        (Maps.compose (left (D · X) Y) (Maps.equivalence e)))

    loop : Maps.Segment P P
    loop = precompose
      (Presented.≃𝒫-trans (Presented.≃𝒫-sym e′)
        (Addition.equivalence (Multiplication.equivalence D h)
          (Presented.≃𝒫-refl V)))
      (Maps.along lower upper)

  -- The ceiling of the remainder, as a normalized point of D.
  ceiling : Division P D → Normal.Point D
  ceiling {D = D} a = Normal.class D
    (Presented._≺𝒫_.ceiling (Maps.Segment.bound (Division.below a)))

  -- The equivalence between two decompositions of P.
  across : (a b : Division P D)
    → ((D · Division.quotient a) + Division.remainder a)
      Presented.≃𝒫 ((D · Division.quotient b) + Division.remainder b)
  across a b = Presented.≃𝒫-trans (Division.equation a)
    (Presented.≃𝒫-sym (Division.equation b))

  -- Quotients of divisions of presentations strictly below P agree.
  Smaller : (P D : 𝒫 ℓ) → Set (lsuc ℓ)
  Smaller {ℓ} P D = (P₀ : 𝒫 ℓ) → P₀ Presented.≺𝒫 P
    → (a b : Division P₀ D)
    → Division.quotient a Presented.≃𝒫 Division.quotient b

private
  -- The point (x, c) of the first decomposition is the point (x′, c)
  -- of the second, with ∂x ≃ ∂x′.
  block : {ℓ : Level} {P D : 𝒫 ℓ} → Smaller P D → (a b : Division P D)
    (x : Normal.Point (Division.quotient a))
    → Σ (Normal.Point (Division.quotient b)) (λ x′ →
        (Presented._≃𝒫_.to (across a b)
          (inj₁ (point D (Division.quotient a) x (ceiling a)))
          ≡ inj₁ (point D (Division.quotient b) x′ (ceiling a)))
        × (Cone.domain (Division.quotient a) x
            Presented.≃𝒫 Cone.domain (Division.quotient b) x′))
  block {ℓ} {P} {D} smaller
    a@(record { quotient = X ; remainder = Y ; equation = e ; below = s })
    b@(record { quotient = X′ ; remainder = Y′ ; equation = e′
              ; below = s′ })
    x = answer (Φ.to u₀) refl
    where
    module Φ = Presented._≃𝒫_ (across a b)

    c : Normal.Point D
    c = ceiling a

    u₀ : 𝒫.X ((D · X) + Y)
    u₀ = inj₁ (point D X x c)

    -- The domain of (x, c), strictly below P.
    P₀ : 𝒫 ℓ
    P₀ = ∂ ((D · X) + Y) u₀

    strictly : P₀ Presented.≺𝒫 P
    strictly = Maps.bounded (Principal.Segments.inclusion ((D · X) + Y) u₀)
      (Maps.equivalence e)

    first : Division P₀ D
    first = record
      { quotient = Cone.domain X x
      ; remainder = Cone.domain D c
      ; equation = Presented.≃𝒫-trans (Cone.product D X x c)
          (Presented.≃𝒫-sym (Cone.left (D · X) Y (point D X x c)))
      ; below = Cone.inside D c
      }

    moved : (w : 𝒫.X ((D · X′) + Y′)) → Φ.to u₀ ≡ w
      → P₀ Presented.≃𝒫 ∂ ((D · X′) + Y′) w
    moved w r = subst (λ v → P₀ Presented.≃𝒫 ∂ ((D · X′) + Y′) v) r
      (Cone.transport (across a b) u₀)

    Result : Set ℓ
    Result = Σ (Normal.Point X′) (λ x′ →
      (Φ.to u₀ ≡ inj₁ (point D X′ x′ c))
      × (Cone.domain X x Presented.≃𝒫 Cone.domain X′ x′))

    -- Landing in a block: the domains are two divisions of P₀.
    landed : (v : 𝒫.X (D · X′))
      → Σ (Normal.Point X′) (λ x′ → Σ (Normal.Point D) (λ d′ →
          v ≡ point D X′ x′ d′))
      → Φ.to u₀ ≡ inj₁ v → Result
    landed .(point D X′ x′ d′) (x′ , d′ , refl) r =
      x′ , trans r (cong (λ d → inj₁ (point D X′ x′ d)) same) ,
      quotients
      where
      second : Division P₀ D
      second = record
        { quotient = Cone.domain X′ x′
        ; remainder = Cone.domain D d′
        ; equation = Presented.≃𝒫-trans (Cone.product D X′ x′ d′)
            (Presented.≃𝒫-trans
              (Presented.≃𝒫-sym (Cone.left (D · X′) Y′ (point D X′ x′ d′)))
              (Presented.≃𝒫-sym (moved (inj₁ (point D X′ x′ d′)) r)))
        ; below = Cone.inside D d′
        }

      quotients : Cone.domain X x Presented.≃𝒫 Cone.domain X′ x′
      quotients = smaller P₀ strictly first second

      same : d′ ≡ c
      same = sym (Cone.points D (remainders first second quotients))

    answer : (w : 𝒫.X ((D · X′) + Y′)) → Φ.to u₀ ≡ w → Result
    answer (inj₁ v) r = landed v (Multiplication.view D X′ v) r
    answer (inj₂ y′) r =
      ⊥-elim (shorter x e e′ (Presented.≃𝒫-sym quotients) s′)
      where
      -- Landing in the other remainder: its quotient is ∂x.
      second : Division P₀ D
      second = record
        { quotient = X′
        ; remainder = ∂ Y′ y′
        ; equation = Presented.≃𝒫-trans
            (Presented.≃𝒫-sym (Cone.right (D · X′) Y′ y′))
            (Presented.≃𝒫-sym (moved (inj₂ y′) r))
        ; below = Maps.along (cone Y′ y′) (Maps.inclusion s′)
        }

      quotients : Cone.domain X x Presented.≃𝒫 X′
      quotients = smaller P₀ strictly first second

  quotients : (P : 𝒫 ℓ) → Acc Presented._≺𝒫_ P → (a b : Division P D)
    → Division.quotient a Presented.≃𝒫 Division.quotient b
  quotients {D = D} P (acc smaller)
    a@(record { quotient = X ; remainder = Y ; equation = e ; below = s })
    b@(record { quotient = X′ ; remainder = Y′ ; equation = e′
              ; below = s′ }) =
    bijection embedding covers
    where
    recursion : Smaller P D
    recursion P₀ p = quotients P₀ (smaller P₀ p)

    ψ : Normal.Point X → Normal.Point X′
    ψ x = proj₁ (block recursion a b x)

    ψ′ : Normal.Point X′ → Normal.Point X
    ψ′ x′ = proj₁ (block recursion b a x′)

    -- The points (x, c) ascend with x, and so do their images (ψ x, c).
    ψ-strict : {x₁ x₂ : Normal.Point X} → Normal.Strict X x₁ x₂
      → Normal.Strict X′ (ψ x₁) (ψ x₂)
    ψ-strict {x₁} {x₂} p =
      Multiplication.reflect D X′ {ψ x₁} {ψ x₂} (ceiling a)
        (subst₂ (𝒫._<_ ((D · X′) + Y′))
          (proj₁ (proj₂ (block recursion a b x₁)))
          (proj₁ (proj₂ (block recursion a b x₂)))
          (Presented._≃𝒫_.to-< (across a b)
            {inj₁ (point D X x₁ (ceiling a))}
            {inj₁ (point D X x₂ (ceiling a))}
            (Multiplication.earlier D X {x₁} {x₂}
              (ceiling a) (ceiling a) p)))

    onto : (x′ : Normal.Point X′) → ψ (ψ′ x′) ≡ x′
    onto x′ = sym (Cone.points X′ (Presented.≃𝒫-trans
      (proj₂ (proj₂ (block recursion b a x′)))
      (proj₂ (proj₂ (block recursion a b (ψ′ x′))))))

    embedding : Maps.Embedding X X′
    embedding = record
      { map = λ x → Normal.representative X′ (ψ (Normal.class X x))
      ; resp = λ {x} {y} p → subst
          (λ c → 𝒫._≈_ X′ (Normal.representative X′ (ψ (Normal.class X x)))
            (Normal.representative X′ (ψ c)))
          (Normal.class-resp X p) (𝒫.≈-refl X′ _)
      ; strict = λ {x} {y} p → Normal.representative-strict X′
          {a = ψ (Normal.class X x)} {b = ψ (Normal.class X y)}
          (ψ-strict {Normal.class X x} {Normal.class X y}
            (Normal.class-strict X {x = x} {y = y} p))
      }

    covers : (x′ : 𝒫.X X′) → Σ (𝒫.X X) (λ x →
      𝒫._≈_ X′ (Maps.Embedding.map embedding x) x′)
    covers x′ = Normal.representative X (ψ′ (Normal.class X′ x′)) ,
      subst (λ c → 𝒫._≈_ X′ (Normal.representative X′ c) x′)
        (sym (trans
          (cong ψ (Normal.class-representative X (ψ′ (Normal.class X′ x′))))
          (onto (Normal.class X′ x′))))
        (Normal.representative-class X′ x′)

-- Quotient and remainder of a division are unique up to ≃𝒫.
unique : (a b : Division P D)
  → (Division.quotient a Presented.≃𝒫 Division.quotient b)
    × (Division.remainder a Presented.≃𝒫 Division.remainder b)
unique {P = P} a b = q , remainders a b q
  where
  q : Division.quotient a Presented.≃𝒫 Division.quotient b
  q = quotients P (Presented.Embedding.wf P) a b
