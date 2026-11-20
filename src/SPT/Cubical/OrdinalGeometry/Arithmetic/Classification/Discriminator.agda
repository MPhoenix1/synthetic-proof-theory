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

open import SPT.Cubical.Base

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
    → 𝒫._<_ (Maps.Successor.next Q) Entry.top y → 𝟘
  topless Q ()

------------------------------------------------------------------------
-- Successors and limits

-- A strong successor of Q has a greatest point: the image of the top of
-- Q + 1.
topmost : {Q P : 𝒫 ℓ} → Strong Q P
  → Σ (𝒫.X P) (λ t → (y : 𝒫.X P) → 𝒫._<_ P t y → 𝟘)
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

  at : Σ ℕ (λ k → Σ (𝒫.X (Increasing.stage s k)) (λ x → stage k x ＝ E.to t))
    → Σ (𝒫.X P) (λ w → 𝒫._<_ P t w)
  at (k , x , p) = E.from (stage (suc k) B.ceiling) ,
    𝒫.<-respˡ-≈ P (E.from-to-≈ t) (E.from-<
      (transport (λ v → 𝒫._<_ (Increasing.limit s) v (stage (suc k) B.ceiling))
        (Limit.compatible C k x ∙ p)
        (Maps.Initial.strict (Limit.stage C (suc k)) (B.below x))))
    where
    module B = Presented._≺𝒫_ (Maps.Segment.bound (Increasing.step s k))

------------------------------------------------------------------------
-- ω + possible s

private
  -- A greatest point of ω + possible s is a point of possible s.
  greatest : (s : ℕ → 𝟚) (t : 𝒫.X (ascent s))
    → ((y : 𝒫.X (ascent s)) → 𝒫._<_ (ascent s) t y → 𝟘) → Stream.Hit s
  greatest s (inl (lift n)) none =
    𝟘-elim (none (inl (lift (suc n))) (lift (≤ℕˢ-refl (suc n))))
  greatest s (inr h) _ = h

  -- A point of possible s is the greatest point of ω + possible s.
  last : (s : ℕ → 𝟚) (h : Stream.Hit s) (y : 𝒫.X (ascent s))
    → 𝒫._<_ (ascent s) (inr h) y → 𝟘
  last s h (inl _) (lift ())
  last s h (inr _) ()

-- Mathematical shape: (Π P. P inhabited → Classified P) → LPO.
inhabited : ((P : 𝒫 lzero) → 𝒫.X P → Classified P) → Stream.LPO
inhabited classify s with classify (ascent s) (inl (lift zero))
... | Classification.zero z = 𝟘-elim (empty z (inl (lift zero)))
... | Classification.successor Q st =
  inl (greatest s (pr₁ (topmost st)) (pr₂ (topmost st)))
... | Classification.limit σ sup = inr (Stream.absent s λ h →
  last s h (pr₁ (unbounded σ sup (inr h)))
    (pr₂ (unbounded σ sup (inr h))))

-- Mathematical shape: (Π P. Classified P) → LPO.
classified : ((P : 𝒫 lzero) → Classified P) → Stream.LPO
classified classify = inhabited (λ P _ → classify P)

------------------------------------------------------------------------
-- Local shapes

private
  summit : (ℕ → 𝟚) → 𝒫 lzero
  summit s = Maps.Successor.next (ascent s)

  -- A greatest point below the top of (ω + possible s) + 1 is a point of
  -- possible s: above n lies n + 1.
  crest : (s : ℕ → 𝟚) (y : 𝒫.X (summit s))
    → 𝒫._<_ (summit s) y Entry.top
    → ((z : 𝒫.X (summit s)) → 𝒫._<_ (summit s) z Entry.top
        → 𝒫._<_ (summit s) z y ⊎ 𝒫._≈_ (summit s) z y)
    → Stream.Hit s
  crest s (Entry.point (inr h)) _ _ = h
  crest s (Entry.point (inl (lift n))) _ below
    with below (Entry.point (inl (lift (suc n)))) Entry.point<top
  ... | inl (Entry.point< (lift p)) =
    𝟘-elim (<ℕˢ-irrefl n (<ℕˢ-trans (≤ℕˢ-refl (suc n)) p))
  ... | inr (Entry.point≈ (lift p)) =
    𝟘-elim
      (<ℕˢ-irrefl n (transport (λ k → n <ℕˢ k) p (≤ℕˢ-refl (suc n))))
  crest s Entry.top () _

  -- Nothing below the top lies above a point of possible s.
  beyond : (s : ℕ → 𝟚) (h : Stream.Hit s) (u : 𝒫.X (summit s))
    → 𝒫._<_ (summit s) u Entry.top
    → 𝒫._<_ (summit s) (Entry.point (inr h)) u → 𝟘
  beyond s h (Entry.point t) _ (Entry.point< p) = last s h t p
  beyond s h Entry.top () _

-- Mathematical shape: (Π W x. Local W x) → LPO.
shaped : ((W : 𝒫 lzero) (x : 𝒫.X W) → Local W x) → Stream.LPO
shaped shape s with shape (summit s) Entry.top
... | Shapes.none nowhere =
  𝟘-elim (nowhere (Entry.point (inl (lift zero))) Entry.point<top)
... | Shapes.greatest y p below = inl (crest s y p below)
... | Shapes.ascending c _ under cofinal = inr (Stream.absent s λ h →
  beyond s h (c (pr₁ (cofinal (Entry.point (inr h)) Entry.point<top)))
    (under (pr₁ (cofinal (Entry.point (inr h)) Entry.point<top)))
    (pr₂ (cofinal (Entry.point (inr h)) Entry.point<top)))
