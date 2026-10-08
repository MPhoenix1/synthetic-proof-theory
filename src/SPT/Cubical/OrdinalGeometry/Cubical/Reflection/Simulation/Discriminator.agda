{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Simulation.Discriminator
  where

-- Rows 2, 13 and 15–18 of the KNFX table, asked of the reflected order
-- types of all presentations, give LPO. The comparisons of
-- Simulation and its Converse carry each statement back to
-- presentations, where Arithmetic.Ambient.Discriminator and
-- Arithmetic.Subtraction.Discriminator decide a Boolean stream. For all of
-- Ord these rows are equivalent to LEM (Kraus, Nordvall Forsberg and Xu,
-- Lemma 57, Theorems 62–64); on the image of the presentations they are
-- already LPO-hard. Row 13 asks for remainders among presentations, with
-- the sum of presentations.

open import Agda.Primitive using (lzero)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
import Relation.Nullary as Decision

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
open import SPT.Cubical.OrdinalGeometry.Presentation.Sum using (_+_)
import SPT.Cubical.OrdinalGeometry.Presentation.Limit.Discriminator as Stream
import SPT.Cubical.OrdinalGeometry.Arithmetic.Ambient.Discriminator as Ambient
import SPT.Cubical.OrdinalGeometry.Arithmetic.Subtraction.Discriminator
  as Subtraction
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Exponential using (omega)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType using
  (orderType)
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Simulation using
  (initial; segment)
import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Simulation.Converse
  as Converse

import Cubical.Data.Empty as Empty
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation
import Cubical.Relation.Nullary as Nullary

private
  -- A Cubical decision of P′ ≺ Q′ decides Segment P Q.
  decision : {P Q : 𝒫 lzero}
    → Nullary.Dec (orderType P Simulation.≺ orderType Q)
    → Decision.Dec (Maps.Segment P Q)
  decision (Nullary.yes σ) = yes (Converse.segment σ)
  decision (Nullary.no ¬σ) = no λ s → Empty.rec (¬σ (segment s))

-- Row 2. Mathematical shape: (Π P Q R. P′ ≼ Q′ → Q′ ≺ R′ → P′ ≺ R′)
-- → LPO.
along : ((P Q R : 𝒫 lzero)
    → orderType P Simulation.≼ orderType Q
    → orderType Q Simulation.≺ orderType R
    → orderType P Simulation.≺ orderType R)
  → Stream.LPO
along transitive =
  Ambient.along λ P Q R f s →
    Converse.segment (transitive P Q R (initial f) (segment s))

-- Row 13. Mathematical shape: (Π P Q. P′ ≼ Q′ → Σ R. (P + R)′ ≃ Q′)
-- → LPO.
remainder : ((P Q : 𝒫 lzero)
    → orderType P Simulation.≼ orderType Q
    → Σ (𝒫 lzero) (λ R →
        Woset.WosetEquiv (orderType (P + R))
          (orderType Q)))
  → Stream.LPO
remainder subtract =
  Subtraction.remainder λ P Q f →
    let R , e = subtract P Q (initial f)
    in R , Converse.equivalence e

-- Row 15. Mathematical shape: (Π P. Dec (P′ ≺ ω′)) → LPO.
finite : ((P : 𝒫 lzero)
    → Nullary.Dec
        (orderType P Simulation.≺ orderType omega))
  → Stream.LPO
finite decide = Ambient.finite λ P → decision (decide P)

-- Row 16. Mathematical shape: (Π P Q. Dec (P′ ≺ Q′)) → LPO.
decidable : ((P Q : 𝒫 lzero)
    → Nullary.Dec
        (orderType P Simulation.≺ orderType Q))
  → Stream.LPO
decidable decide = Ambient.decidable λ P Q → decision (decide P Q)

-- Row 17. Mathematical shape: (Π P Q. P′ ≼ Q′ → P′ ≺ Q′ ⊎ P′ ≃ Q′)
-- → LPO.
split : ((P Q : 𝒫 lzero)
    → orderType P Simulation.≼ orderType Q
    → orderType P Simulation.≺ orderType Q
      ⊎ Woset.WosetEquiv (orderType P) (orderType Q))
  → Stream.LPO
split splitting =
  Ambient.split λ P Q f → back (splitting P Q (initial f))
  where
  back : {P Q : 𝒫 lzero}
    → orderType P Simulation.≺ orderType Q
      ⊎ Woset.WosetEquiv (orderType P) (orderType Q)
    → Maps.Segment P Q ⊎ P Presented.≃𝒫 Q
  back (inj₁ σ) = inj₁ (Converse.segment σ)
  back (inj₂ e) = inj₂ (Converse.equivalence e)

-- Row 18. Mathematical shape: (Π P Q. P′ ≺ Q′ ⊎ P′ ≃ Q′ ⊎ Q′ ≺ P′)
-- → LPO.
trichotomy : ((P Q : 𝒫 lzero)
    → orderType P Simulation.≺ orderType Q
      ⊎ (Woset.WosetEquiv (orderType P) (orderType Q)
        ⊎ orderType Q Simulation.≺ orderType P))
  → Stream.LPO
trichotomy compare =
  Ambient.trichotomy λ P Q → back (compare P Q)
  where
  back : {P Q : 𝒫 lzero}
    → orderType P Simulation.≺ orderType Q
      ⊎ (Woset.WosetEquiv (orderType P) (orderType Q)
        ⊎ orderType Q Simulation.≺ orderType P)
    → Maps.Segment P Q ⊎ (P Presented.≃𝒫 Q ⊎ Maps.Segment Q P)
  back (inj₁ σ) = inj₁ (Converse.segment σ)
  back (inj₂ (inj₁ e)) = inj₂ (inj₁ (Converse.equivalence e))
  back (inj₂ (inj₂ σ)) = inj₂ (inj₂ (Converse.segment σ))
