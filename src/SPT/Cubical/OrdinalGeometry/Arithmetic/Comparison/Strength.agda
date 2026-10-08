{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Comparison.Strength where

-- The exact strength of the rows whose datum in the geometry is an
-- ambient. Asked of all presentations, each statement below is equivalent
-- to LPO. One
-- direction is Arithmetic.Comparison; the other is the discriminator of
-- the same row (Ambient, Successor, Subtraction and Comparison
-- discriminators). The equivalences are stated at level zero, where the
-- discriminators are; the positive direction holds at every level. Rows 9
-- (classification) and 14 (division) are not covered here.

open import Agda.Primitive using (lzero)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ)
open import Data.Sum using (_⊎_)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Nullary using (Dec)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
open import SPT.Cubical.OrdinalGeometry.Presentation.Sum using (_+_)
import SPT.Cubical.OrdinalGeometry.Presentation.Limit.Discriminator as Stream
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization using
  (Supremum)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Ambient using (pair)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Exponential using (omega)
import SPT.Cubical.OrdinalGeometry.Arithmetic.Comparison as Comparison
import SPT.Cubical.OrdinalGeometry.Arithmetic.Comparison.Discriminator
  as ComparisonDiscriminator
import SPT.Cubical.OrdinalGeometry.Arithmetic.Ambient.Discriminator
  as AmbientDiscriminator
import SPT.Cubical.OrdinalGeometry.Arithmetic.Successor.Discriminator
  as SuccessorDiscriminator
import SPT.Cubical.OrdinalGeometry.Arithmetic.Subtraction.Discriminator
  as SubtractionDiscriminator

-- Mathematical shape: LPO ⇔ Π P Q. P ≤ Q ⊎ Q < P.
comparable : Stream.LPO
  ⇔ ((P Q : 𝒫 lzero) → Maps.Initial P Q ⊎ Maps.Segment Q P)
comparable = mk⇔ (λ lpo → Comparison.comparable lpo)
  ComparisonDiscriminator.comparable

-- Mathematical shape: LPO ⇔ Π P Q. Dec (P ≤ Q).
initial : Stream.LPO ⇔ ((P Q : 𝒫 lzero) → Dec (Maps.Initial P Q))
initial = mk⇔ (λ lpo → Comparison.initial lpo)
  ComparisonDiscriminator.initial

-- Mathematical shape: LPO ⇔ Π P Q. Dec (P ≃ Q).
equivalent : Stream.LPO
  ⇔ ((P Q : 𝒫 lzero) → Dec (P Presented.≃𝒫 Q))
equivalent = mk⇔ (λ lpo → Comparison.equivalent lpo)
  ComparisonDiscriminator.equivalent

-- Mathematical shape: LPO ⇔ Π F : ℕ → 𝒫. Σ S. Π n. F n < S.
bound : Stream.LPO
  ⇔ ((F : ℕ → 𝒫 lzero)
      → Σ (𝒫 lzero) (λ S → (n : ℕ) → Maps.Segment (F n) S))
bound = mk⇔ (λ lpo → Comparison.bound lpo) ComparisonDiscriminator.bound

-- Row 2. Mathematical shape: LPO ⇔ Π P Q R. P ≤ Q → Q < R → P < R.
along : Stream.LPO
  ⇔ ((P Q R : 𝒫 lzero) → Maps.Initial P Q → Maps.Segment Q R
      → Maps.Segment P R)
along = mk⇔ (λ lpo P Q R → Comparison.along lpo)
  AmbientDiscriminator.along

-- Row 5. Mathematical shape: LPO ⇔ Π P Q. P ≤ Q → P + 1 ≤ Q + 1.
successor-initial : Stream.LPO
  ⇔ ((P Q : 𝒫 lzero) → Maps.Initial P Q
      → Maps.Initial (Maps.Successor.next P) (Maps.Successor.next Q))
successor-initial = mk⇔ (λ lpo P Q → Comparison.successor-initial lpo)
  SuccessorDiscriminator.initial

-- Row 5. Mathematical shape: LPO ⇔ Π P Q. P < Q → P + 1 < Q + 1.
successor-segment : Stream.LPO
  ⇔ ((P Q : 𝒫 lzero) → Maps.Segment P Q
      → Maps.Segment (Maps.Successor.next P) (Maps.Successor.next Q))
successor-segment = mk⇔ (λ lpo P Q → Comparison.successor-segment lpo)
  SuccessorDiscriminator.segment

-- Row 6. Mathematical shape: LPO ⇔ Π P Q. Σ S. S = sup (P, Q, Q, …).
join : Stream.LPO
  ⇔ ((P Q : 𝒫 lzero) → Σ (𝒫 lzero) (Supremum (pair P Q)))
join = mk⇔ (λ lpo → Comparison.join lpo) AmbientDiscriminator.join

-- Row 8. Mathematical shape: LPO ⇔ Π F : ℕ → 𝒫. Σ S. S = sup F.
supremum : Stream.LPO
  ⇔ ((F : ℕ → 𝒫 lzero) → Σ (𝒫 lzero) (Supremum F))
supremum = mk⇔ (λ lpo → Comparison.supremum lpo)
  AmbientDiscriminator.supremum

-- Row 13. Mathematical shape: LPO ⇔ Π P Q. P ≤ Q → Σ R. P + R ≃ Q.
remainder : Stream.LPO
  ⇔ ((P Q : 𝒫 lzero) → Maps.Initial P Q
      → Σ (𝒫 lzero) (λ R → (P + R) Presented.≃𝒫 Q))
remainder = mk⇔ (λ lpo P Q → Comparison.subtract lpo)
  SubtractionDiscriminator.remainder

-- Row 15. Mathematical shape: LPO ⇔ Π P. Dec (P < ω).
finite : Stream.LPO ⇔ ((P : 𝒫 lzero) → Dec (Maps.Segment P omega))
finite = mk⇔ (λ lpo → Comparison.finite lpo) AmbientDiscriminator.finite

-- Row 16. Mathematical shape: LPO ⇔ Π P Q. Dec (P < Q).
decidable : Stream.LPO ⇔ ((P Q : 𝒫 lzero) → Dec (Maps.Segment P Q))
decidable = mk⇔ (λ lpo → Comparison.decidable lpo)
  AmbientDiscriminator.decidable

-- Row 17. Mathematical shape: LPO ⇔ Π P Q. P ≤ Q → P < Q ⊎ P ≃ Q.
split : Stream.LPO
  ⇔ ((P Q : 𝒫 lzero) → Maps.Initial P Q
      → Maps.Segment P Q ⊎ P Presented.≃𝒫 Q)
split = mk⇔ (λ lpo P Q → Comparison.split lpo) AmbientDiscriminator.split

-- Row 18. Mathematical shape: LPO ⇔ Π P Q. P < Q ⊎ P ≃ Q ⊎ Q < P.
trichotomy : Stream.LPO
  ⇔ ((P Q : 𝒫 lzero)
      → Maps.Segment P Q ⊎ (P Presented.≃𝒫 Q ⊎ Maps.Segment Q P))
trichotomy = mk⇔ (λ lpo → Comparison.trichotomy lpo)
  AmbientDiscriminator.trichotomy
