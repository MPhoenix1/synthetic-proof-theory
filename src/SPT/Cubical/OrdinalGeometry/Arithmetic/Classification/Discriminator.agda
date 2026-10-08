{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Classification.Discriminator
  where

-- Classification without formation. The formers retain Classified P and
-- local shapes (Classification, Pointwise, Local). Asked of every
-- inhabited presentation instead, classification decides an arbitrary
-- Boolean stream s, so the obstruction is not only the zero case. A strong
-- successor has a greatest point (topmost); a limit of an increasing
-- sequence has none, since each point comes from a stage and the next
-- ceiling lies above it (unbounded). With possible s, which has a point
-- exactly when s hits true, ω + possible s is ω + 1 when s hits and ω
-- otherwise, so classifying it decides s (inhabited, classified). Locally,
-- the top of (ω + possible s) + 1 always has points below it, and its
-- shape is a greatest point exactly when s hits (shaped). Each gives LPO:
-- formation is the datum classification uses.

open import Agda.Primitive using (Level; lzero)
open import Data.Bool using (Bool)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Properties as NatProperties
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using
  (_≡_; sym; trans; subst)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Limit as Limit
import SPT.Cubical.OrdinalGeometry.Presentation.Limit.Discriminator as Stream
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization using
  (empty; Strong; module Successors; Supremum; module Suprema; Increasing)
open import
  SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization.Discriminator
  using (ascent)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Classification using
  (Classified)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Classification as Classification
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Classification.Local using
  (Local)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Classification.Local as Shapes

private
  variable
    ℓ : Level

  -- The entries of a successor presentation: old points and the top.
  module Entry = Presented.Diagonal.Successor

  -- Nothing lies above the top of Q + 1.
  topless : (Q : 𝒫 ℓ) {y : 𝒫.X (Maps.Successor.next Q)}
    → 𝒫._<_ (Maps.Successor.next Q) Entry.top y → ⊥
  topless Q ()

------------------------------------------------------------------------
-- Successors and limits

-- A strong successor of Q has a greatest point: the image of the top of
-- Q + 1.
topmost : {Q P : 𝒫 ℓ} → Strong Q P
  → Σ (𝒫.X P) (λ t → (y : 𝒫.X P) → 𝒫._<_ P t y → ⊥)
topmost {Q = Q} {P = P} st = E.from Entry.top , λ y p → topless Q
  (𝒫.<-respˡ-≈ (Maps.Successor.next Q) (E.to-from-≈ Entry.top) (E.to-< p))
  where
  module E = Presented._≃𝒫_ (Successors.equivalent (Strong.successor st))

-- A limit of an increasing sequence has no greatest point: a point comes
-- from some stage k, and the ceiling of the step from k to k + 1 lands
-- above it.
unbounded : {P : 𝒫 ℓ} (s : Increasing ℓ)
  → Supremum (Increasing.stage s) P
  → (t : 𝒫.X P) → Σ (𝒫.X P) (λ w → 𝒫._<_ P t w)
unbounded {ℓ} {P = P} s sup t = at (Limit.coverage C (E.to t))
  where
  C : Limit.Chain ℓ
  C = Increasing.chain s

  module E = Presented._≃𝒫_ (Suprema.unique sup (Increasing.supremum s))

  stage : (n : ℕ) → 𝒫.X (Increasing.stage s n) → 𝒫.X (Increasing.limit s)
  stage n = Maps.Initial.map (Limit.stage C n)

  at : Σ ℕ (λ k → Σ (𝒫.X (Increasing.stage s k)) (λ x → stage k x ≡ E.to t))
    → Σ (𝒫.X P) (λ w → 𝒫._<_ P t w)
  at (k , x , p) = E.from (stage (suc k) B.ceiling) ,
    𝒫.<-respˡ-≈ P (E.from-to-≈ t) (E.from-<
      (subst (λ v → 𝒫._<_ (Increasing.limit s) v (stage (suc k) B.ceiling))
        (trans (Limit.compatible C k x) p)
        (Maps.Initial.strict (Limit.stage C (suc k)) (B.below x))))
    where
    module B = Presented._≺𝒫_ (Maps.Segment.bound (Increasing.step s k))

------------------------------------------------------------------------
-- ω + possible s

private
  -- A greatest point of ω + possible s is a point of possible s.
  greatest : (s : ℕ → Bool) (t : 𝒫.X (ascent s))
    → ((y : 𝒫.X (ascent s)) → 𝒫._<_ (ascent s) t y → ⊥) → Stream.Hit s
  greatest s (inj₁ (lift n)) none =
    ⊥-elim (none (inj₁ (lift (suc n))) (lift (NatProperties.n<1+n n)))
  greatest s (inj₂ h) _ = h

  -- A point of possible s is the greatest point of ω + possible s.
  last : (s : ℕ → Bool) (h : Stream.Hit s) (y : 𝒫.X (ascent s))
    → 𝒫._<_ (ascent s) (inj₂ h) y → ⊥
  last s h (inj₁ _) (lift ())
  last s h (inj₂ _) ()

-- Mathematical shape: (Π P. P inhabited → Classified P) → LPO.
inhabited : ((P : 𝒫 lzero) → 𝒫.X P → Classified P) → Stream.LPO
inhabited classify s with classify (ascent s) (inj₁ (lift zero))
... | Classification.zero z = ⊥-elim (empty z (inj₁ (lift zero)))
... | Classification.successor Q st =
  inj₁ (greatest s (proj₁ (topmost st)) (proj₂ (topmost st)))
... | Classification.limit σ sup = inj₂ (Stream.absent s λ h →
  last s h (proj₁ (unbounded σ sup (inj₂ h)))
    (proj₂ (unbounded σ sup (inj₂ h))))

-- Mathematical shape: (Π P. Classified P) → LPO.
classified : ((P : 𝒫 lzero) → Classified P) → Stream.LPO
classified classify = inhabited (λ P _ → classify P)

------------------------------------------------------------------------
-- Local shapes

private
  summit : (ℕ → Bool) → 𝒫 lzero
  summit s = Maps.Successor.next (ascent s)

  -- A greatest point below the top of (ω + possible s) + 1 is a point of
  -- possible s: above n lies n + 1.
  crest : (s : ℕ → Bool) (y : 𝒫.X (summit s))
    → 𝒫._<_ (summit s) y Entry.top
    → ((z : 𝒫.X (summit s)) → 𝒫._<_ (summit s) z Entry.top
        → 𝒫._<_ (summit s) z y ⊎ 𝒫._≈_ (summit s) z y)
    → Stream.Hit s
  crest s (Entry.point (inj₂ h)) _ _ = h
  crest s (Entry.point (inj₁ (lift n))) _ below
    with below (Entry.point (inj₁ (lift (suc n)))) Entry.point<top
  ... | inj₁ (Entry.point< (lift p)) =
    ⊥-elim (NatProperties.<-asym p (NatProperties.n<1+n n))
  ... | inj₂ (Entry.point≈ (lift p)) =
    ⊥-elim (NatProperties.<-irrefl (sym p) (NatProperties.n<1+n n))
  crest s Entry.top () _

  -- Nothing below the top lies above a point of possible s.
  beyond : (s : ℕ → Bool) (h : Stream.Hit s) (u : 𝒫.X (summit s))
    → 𝒫._<_ (summit s) u Entry.top
    → 𝒫._<_ (summit s) (Entry.point (inj₂ h)) u → ⊥
  beyond s h (Entry.point t) _ (Entry.point< p) = last s h t p
  beyond s h Entry.top () _

-- Mathematical shape: (Π W x. Local W x) → LPO.
shaped : ((W : 𝒫 lzero) (x : 𝒫.X W) → Local W x) → Stream.LPO
shaped shape s with shape (summit s) Entry.top
... | Shapes.none nothing =
  ⊥-elim (nothing (Entry.point (inj₁ (lift zero))) Entry.point<top)
... | Shapes.greatest y p below = inj₁ (crest s y p below)
... | Shapes.ascending c _ under cofinal = inj₂ (Stream.absent s λ h →
  beyond s h (c (proj₁ (cofinal (Entry.point (inj₂ h)) Entry.point<top)))
    (under (proj₁ (cofinal (Entry.point (inj₂ h)) Entry.point<top)))
    (proj₂ (cofinal (Entry.point (inj₂ h)) Entry.point<top)))
