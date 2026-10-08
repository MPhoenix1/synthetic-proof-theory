{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Classification where

-- Classification of presented ordinals as zero, strong successor, or limit
-- of a strictly increasing sequence, as data retained by formation rather
-- than decided. Classified P has one constructor for each case of the
-- classification of Kraus, Nordvall Forsberg and Xu. It respects ≃𝒫, and
-- every former produces it: ∅ is zero, P + 1 is a strong successor and
-- the limit of an increasing sequence is a limit, outright; P + Q, D · Q
-- and ω^P are classified when their inputs are. In an ambient W, an
-- ascending sequence of points with every point below one of them makes W
-- the limit of their domains; this classifies ω, the products D · Q with
-- Q a limit, and ω^P for P a successor.

open import Agda.Primitive using (Level; lsuc)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; suc)
import Data.Nat as Nat
import Data.Nat.Properties as NatProperties
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
open import SPT.Cubical.OrdinalGeometry.Presentation.Sum using (_+_; ∂; cone)
import SPT.Cubical.OrdinalGeometry.Presentation.Limit as Limit
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization as Normal
import SPT.Cubical.OrdinalGeometry.Operation.Base as Operation
import SPT.Cubical.OrdinalGeometry.Operation.Exponential as Power
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization using
  (Zero; empty; pointless; nothing; Successor; Strong; module Successors;
   Supremum; module Suprema; Increasing)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Addition as Addition
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Multiplication using
  (_·_; point)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Multiplication as Multiplication
import SPT.Cubical.OrdinalGeometry.Arithmetic.Exponential as Exponential
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Exponential using (omega)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Ambient as Ambient

private
  variable
    ℓ : Level
    P P′ Q D : 𝒫 ℓ

------------------------------------------------------------------------
-- Classification

-- Mathematical shape: Zero P ⊎ Σ Q. Strong Q P ⊎ Σ s. Supremum s P.
data Classified {ℓ : Level} (P : 𝒫 ℓ) : Set (lsuc ℓ) where
  zero : Zero P → Classified P
  successor : (Q : 𝒫 ℓ) → Strong Q P → Classified P
  limit : (s : Increasing ℓ) → Supremum (Increasing.stage s) P
    → Classified P

-- Zero, strong successors and suprema respect equivalence, and so does the
-- classification.
zero-respect : P Presented.≃𝒫 P′ → Zero P → Zero P′
zero-respect e z Q =
  Maps.compose (Maps.equivalence (Presented.≃𝒫-sym e)) (z Q)

strong-respect : P Presented.≃𝒫 P′ → Strong Q P → Strong Q P′
strong-respect e st = record
  { successor = record
      { above = Maps.along (Successor.above S) (Maps.equivalence e)
      ; least = λ X s → Maps.compose
          (Maps.equivalence (Presented.≃𝒫-sym e)) (Successor.least S X s)
      }
  ; below = λ R s → Strong.below st R
      (Maps.along s (Maps.equivalence (Presented.≃𝒫-sym e)))
  }
  where
  S = Strong.successor st

supremum-respect : {F : ℕ → 𝒫 ℓ} → P Presented.≃𝒫 P′
  → Supremum F P → Supremum F P′
supremum-respect e sup = record
  { member = λ n →
      Maps.compose (Supremum.member sup n) (Maps.equivalence e)
  ; least = λ X g → Maps.compose
      (Maps.equivalence (Presented.≃𝒫-sym e)) (Supremum.least sup X g)
  }

respect : P Presented.≃𝒫 P′ → Classified P → Classified P′
respect e (zero z) = zero (zero-respect e z)
respect e (successor Q st) = successor Q (strong-respect e st)
respect e (limit s sup) = limit s (supremum-respect e sup)

------------------------------------------------------------------------
-- The formers that classify outright

vacant : Classified (Operation.empty {ℓ})
vacant = zero nothing

next : (P : 𝒫 ℓ) → Classified (Maps.Successor.next P)
next P = successor P (Successors.next P)

completed : (s : Increasing ℓ) → Classified (Increasing.limit s)
completed s = limit s (Increasing.supremum s)

------------------------------------------------------------------------
-- Limits from ascending points

-- In an ambient W, an ascending sequence of points with every point below
-- one of them makes W the limit of their domains.
cofinal : (W : 𝒫 ℓ) (x : ℕ → 𝒫.X W)
  → ((n : ℕ) → 𝒫._<_ W (x n) (x (suc n)))
  → ((y : 𝒫.X W) → Σ ℕ (λ n → 𝒫._<_ W y (x n)))
  → Σ (Increasing ℓ) (λ s → Supremum (Increasing.stage s) W)
cofinal {ℓ} W x up every =
  s , supremum-respect exhausted (Increasing.supremum s)
  where
  s : Increasing ℓ
  s = record
    { stage = λ n → ∂ W (x n)
    ; step = λ n → Ambient.segment W (up n)
    }

  covers : (y : 𝒫.X W) → Σ ℕ (λ n → Σ (𝒫.X (∂ W (x n))) (λ u →
    𝒫._≈_ W (Maps.Initial.map (Maps.inclusion (cone W (x n))) u) y))
  covers y = let n , p = every y in n , (y , p) , 𝒫.≈-refl W y

  exhausted : Increasing.limit s Presented.≃𝒫 W
  exhausted = Limit.exhaustion (Increasing.chain s) W
    (λ n → Maps.inclusion (cone W (x n))) covers

-- A limit of a strictly increasing sequence has an ascending sequence of
-- points with every point below one of them: the images of the ceilings.
ascent : (s : Increasing ℓ) → Supremum (Increasing.stage s) Q
  → Σ (ℕ → 𝒫.X Q) (λ c → ((n : ℕ) → 𝒫._<_ Q (c n) (c (suc n)))
      × ((y : 𝒫.X Q) → Σ ℕ (λ n → 𝒫._<_ Q y (c n))))
ascent {Q = Q} s sup = c , up , every
  where
  module S = Increasing s

  member : (n : ℕ) → Maps.Initial (S.stage n) Q
  member = Supremum.member sup

  module Bound (n : ℕ) = Presented._≺𝒫_ (Maps.Segment.bound (S.step n))

  c : ℕ → 𝒫.X Q
  c n = Maps.Initial.map (member (suc n)) (Bound.ceiling n)

  -- The member at n + 1 after the step is the member at n.
  agree : (n : ℕ) (x : 𝒫.X (S.stage n))
    → 𝒫._≈_ Q (Maps.Initial.map (member (suc n)) (Bound.to n x))
        (Maps.Initial.map (member n) x)
  agree n = Maps.Uniqueness.pointwise
    (Maps.compose (Maps.inclusion (S.step n)) (member (suc n))) (member n)

  -- Every point of the stage n lies below c n.
  under : (n : ℕ) (x : 𝒫.X (S.stage n))
    → 𝒫._<_ Q (Maps.Initial.map (member n) x) (c n)
  under n x = 𝒫.<-respˡ-≈ Q (agree n x)
    (Maps.Initial.strict (member (suc n)) (Bound.below n x))

  up : (n : ℕ) → 𝒫._<_ Q (c n) (c (suc n))
  up n = under (suc n) (Bound.ceiling n)

  e : Q Presented.≃𝒫 Increasing.limit s
  e = Suprema.unique sup S.supremum

  module E = Presented._≃𝒫_ e

  -- Every point of Q comes from a stage, through the completion.
  every : (y : 𝒫.X Q) → Σ ℕ (λ n → 𝒫._<_ Q y (c n))
  every y with Limit.coverage S.chain (E.to y)
  ... | k , x , p = k , 𝒫.<-respˡ-≈ Q back (under k x)
    where
    back : 𝒫._≈_ Q (Maps.Initial.map (member k) x) y
    back = 𝒫.≈-trans Q
      (Maps.Uniqueness.pointwise (member k)
        (Maps.compose (Limit.stage S.chain k)
          (Maps.equivalence (Presented.≃𝒫-sym e))) x)
      (subst (λ w → 𝒫._≈_ Q (E.from w) y) (sym p) (E.from-to-≈ y))

-- ω is the limit of the finite ordinals, the domains of its points.
naturals : Σ (Increasing ℓ) (λ s → Supremum (Increasing.stage s) (omega {ℓ}))
naturals = cofinal omega (λ n → lift n) (λ n → lift (NatProperties.n<1+n n))
  (λ y → suc (Level.lower y) , lift (NatProperties.n<1+n (Level.lower y)))

------------------------------------------------------------------------
-- Sums, products and ω^

-- P + Q is classified by Q, and by P when Q is zero.
sum : (P : 𝒫 ℓ) → Classified Q → (Zero Q → Classified P)
  → Classified (P + Q)
sum {Q = Q} P (zero z) cP =
  respect (Presented.≃𝒫-sym (Addition.zero-law {P = P} Q z)) (cP z)
sum P (successor Q₀ st) _ = respect
  (Presented.≃𝒫-sym (Addition.successor-law {P = P} (Strong.successor st)
    (Strong.successor (Successors.next (P + Q₀)))))
  (next (P + Q₀))
sum P (limit s sup) _ = respect
  (Presented.≃𝒫-sym (Addition.limit-law {P = P} s sup
    (Increasing.supremum s′)))
  (completed s′)
  where
  s′ : Increasing _
  s′ = record
    { stage = λ n → P + Increasing.stage s n
    ; step = λ n → Addition.segment P (Increasing.step s n)
    }

-- D · Q with a point d of D and Q a limit is a limit: the points (cₙ, d)
-- ascend, and every point of D · Q lies below one of them.
product-limit : (D : 𝒫 ℓ) → 𝒫.X D → (s : Increasing ℓ)
  → Supremum (Increasing.stage s) Q → Classified (D · Q)
product-limit {Q = Q} D d s sup =
  limit (proj₁ ascending) (proj₂ ascending)
  where
  c : ℕ → 𝒫.X Q
  c = proj₁ (ascent s sup)

  δ : Normal.Point D
  δ = Normal.class D d

  κ : ℕ → Normal.Point Q
  κ n = Normal.class Q (c n)

  x : ℕ → 𝒫.X (D · Q)
  x n = point D Q (κ n) δ

  up : (n : ℕ) → 𝒫._<_ (D · Q) (x n) (x (suc n))
  up n = Multiplication.earlier D Q {κ n} {κ (suc n)} δ δ
    (Normal.class-strict Q {x = c n} {y = c (suc n)}
      (proj₁ (proj₂ (ascent s sup)) n))

  reach : (v : 𝒫.X (D · Q))
    → Σ (Normal.Point Q) (λ q → Σ (Normal.Point D) (λ a →
        v ≡ point D Q q a))
    → Σ ℕ (λ n → 𝒫._<_ (D · Q) v (x n))
  reach .(point D Q q a) (q , a , refl) =
    let n , p = proj₂ (proj₂ (ascent s sup)) (Normal.representative Q q)
    in n , Multiplication.earlier D Q {q} {κ n} a δ
      (subst (λ r → Normal.Strict Q r (κ n))
        (Normal.class-representative Q q)
        (Normal.class-strict Q {x = Normal.representative Q q} {y = c n} p))

  ascending : Σ (Increasing _) (λ t → Supremum (Increasing.stage t) (D · Q))
  ascending = cofinal (D · Q) x up
    (λ v → reach v (Multiplication.view D Q v))

private
  -- With a point of D, the zero, successor and limit laws of D · −.
  inhabited : (D : 𝒫 ℓ) → 𝒫.X D → Classified D → Classified Q
    → Classified (D · Q)
  inhabited {Q = Q} D d cD (zero z) =
    respect (Presented.≃𝒫-sym (Multiplication.zero-law D Q z)) (zero z)
  inhabited D d cD (successor Q₀ st) = respect
    (Presented.≃𝒫-sym (Multiplication.successor-law D (Strong.successor st)))
    (sum (D · Q₀) cD (λ z → ⊥-elim (empty z d)))
  inhabited D d cD (limit s sup) = product-limit D d s sup

-- D · Q is classified when D and Q are: zero when D is, and otherwise
-- by the zero, successor and limit laws of the product, using a point of
-- D: the ceiling of its last segment.
product : Classified D → Classified Q → Classified (D · Q)
product {D = D} {Q = Q} (zero z) cQ = zero (pointless λ v →
  let q , a , _ = Multiplication.view D Q v in
  empty z (Normal.representative D a))
product {D = D} cD@(successor D₀ st) cQ = inhabited D
  (Presented._≺𝒫_.ceiling
    (Maps.Segment.bound (Successor.above (Strong.successor st)))) cD cQ
product {D = D} cD@(limit t sup) cQ = inhabited D
  (Maps.Initial.map (Supremum.member sup (suc Nat.zero))
    (Presented._≺𝒫_.ceiling
      (Maps.Segment.bound (Increasing.step t Nat.zero)))) cD cQ

-- ω^P is classified when P is: a successor when P is zero, the limit of
-- ω^P₀ · n when P is a successor of P₀, and a limit when P is one.
power : Classified P → Classified (Power.exp P)
power {P = P} (zero z) =
  respect (Presented.≃𝒫-sym (Exponential.single P z)) (next P)
power (successor P₀ st) = respect
  (Presented.≃𝒫-sym (Exponential.successor-law (Strong.successor st)))
  (product-limit (Power.exp P₀)
    (Presented._≺𝒫_.ceiling (Maps.Segment.bound (Power.positive P₀)))
    (proj₁ naturals) (proj₂ naturals))
power (limit s sup) = respect
  (Presented.≃𝒫-sym (Exponential.limit-law s sup (Increasing.supremum s′)))
  (completed s′)
  where
  s′ : Increasing _
  s′ = record
    { stage = λ n → Power.exp (Increasing.stage s n)
    ; step = λ n → Power.segment (Increasing.step s n)
    }
