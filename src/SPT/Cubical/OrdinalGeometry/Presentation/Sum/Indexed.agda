{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Presentation.Sum.Indexed where

-- Ordered sums of presentations over the points of an exact countable
-- ordinal I. The block at a point i is the normalized presentation of F i,
-- and the blocks follow the order of I: the sum is the exact dependent sum
-- of ExactOrder.Sum, presented. Normalization identifies equivalent points
-- inside one block. The sums serve as bounds, entered through embeddings,
-- and no later construction reads which representative a block keeps.
-- - Every F i embeds into the sum at its block.
-- - An order embedding of the index, with embeddings of the blocks along
--   it, gives an embedding of the sums.
-- - The ω-multiple of S is its sum over the natural numbers, one copy of S
--   for every n.
-- - An order embedding of the normalized points of P into I, with a chosen
--   point in every block, embeds P into the sum.

open import Agda.Primitive using (Level; lzero)
open import Data.Product using (Σ; _,_; proj₂)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (cong)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order
import SPT.Cubical.OrdinalGeometry.ExactOrder.Maps as Orders
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization as Normal
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization.Maps
  as NormalMaps
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization.Presentation
  as Exact
import SPT.Cubical.OrdinalGeometry.ExactOrder.OrderedSum as Index
open Index using (Ordinal; Carrier)

private
  variable
    ℓ : Level

-- The exact order of the sum: the normalized points of each block, the
-- blocks along I.
order : (I : Ordinal lzero) (F : Carrier I → 𝒫 ℓ)
  → Order.Order (Σ (Carrier I) (λ i → Normal.Point (F i)))
order I F = Order.Sum.order (Index.order I) (λ i → Normal.order (F i))

-- Mathematical shape: Σ_{i ∈ I} F i.
sum : (I : Ordinal lzero) → (Carrier I → 𝒫 ℓ) → 𝒫 ℓ
sum I F = Exact.presentation (order I F)

-- F i embeds into the sum at its block.
block : (I : Ordinal lzero) (F : Carrier I → 𝒫 ℓ) (i : Carrier I)
  → Maps.Embedding (F i) (sum I F)
block I F i = record
  { map = λ x → lift (i , Normal.class (F i) x)
  ; resp = λ p → lift (cong (i ,_) (Normal.class-resp (F i) p))
  ; strict = λ p → lift (Blocks.within i (Normal.class-strict (F i) p))
  }
  where
  module Blocks = Order.Sum (Index.order I) (λ i → Normal.order (F i))

-- An order embedding e of the index, and an embedding of each block into
-- the block at its image, embed the sums.
map : {I J : Ordinal lzero} {F : Carrier I → 𝒫 ℓ} {G : Carrier J → 𝒫 ℓ}
  (e : Orders.Embedding (Index.order I) (Index.order J))
  → ((i : Carrier I)
      → Maps.Embedding (F i) (G (Orders.Embedding.map e i)))
  → Maps.Embedding (sum I F) (sum J G)
map {I = I} {J} {F} {G} e φ = Exact.embedding
  (record { map = to ; strict = preserve })
  where
  module Source = Order.Sum (Index.order I) (λ i → Normal.order (F i))
  module Target = Order.Sum (Index.order J) (λ j → Normal.order (G j))
  module E = Orders.Embedding e

  -- The blocks, normalized.
  ψ : (i : Carrier I)
    → Orders.Embedding (Normal.order (F i)) (Normal.order (G (E.map i)))
  ψ i = NormalMaps.embedding (φ i)

  to : Σ (Carrier I) (λ i → Normal.Point (F i))
    → Σ (Carrier J) (λ j → Normal.Point (G j))
  to (i , a) = E.map i , Orders.Embedding.map (ψ i) a

  preserve : ∀ {x y} → Source._<_ x y → Target._<_ (to x) (to y)
  preserve (Source.earlier p) = Target.earlier (E.strict p)
  preserve (Source.within i {a} {b} q) =
    Target.within (E.map i) (Orders.Embedding.strict (ψ i) {a} {b} q)

-- The identity of an index, as an order embedding.
same : (I : Ordinal lzero)
  → Orders.Embedding (Index.order I) (Index.order I)
same I = record { map = λ i → i ; strict = λ p → p }

-- Mathematical shape: S·ω, one copy of S for every natural number.
times : 𝒫 ℓ → 𝒫 ℓ
times S = sum Index.natural (λ _ → S)

-- The ω-multiple acts on embeddings, copy by copy.
times-map : {S S′ : 𝒫 ℓ} → Maps.Embedding S S′
  → Maps.Embedding (times S) (times S′)
times-map f = map (same Index.natural) (λ _ → f)

-- Embeddings of the blocks over one index embed the sums. The type names
-- each block literally, so no image under the identity is unfolded.
pointwise : {I : Ordinal lzero} {F G : Carrier I → 𝒫 ℓ}
  → ((i : Carrier I) → Maps.Embedding (F i) (G i))
  → Maps.Embedding (sum I F) (sum I G)
pointwise {I = I} φ = map (same I) φ

-- Mathematical shape: x ↦ the chosen point of the block at e [x].
choice : {P : 𝒫 ℓ} {I : Ordinal lzero} {F : Carrier I → 𝒫 ℓ}
  (e : Orders.Embedding (Normal.order P) (Index.order I))
  → ((i : Carrier I) → 𝒫.X (F i)) → Maps.Embedding P (sum I F)
choice {P = P} {I} {F} e t = record
  { map = λ x → lift (point (Normal.class P x))
  ; resp = λ p → lift (cong point (Normal.class-resp P p))
  ; strict = λ {x} {y} p → lift (Blocks.earlier
      {a = Orders.Embedding.map e (Normal.class P x)}
      {a′ = Orders.Embedding.map e (Normal.class P y)}
      {x = proj₂ (point (Normal.class P x))}
      {y = proj₂ (point (Normal.class P y))}
      (Orders.Embedding.strict e {Normal.class P x} {Normal.class P y}
        (Normal.class-strict P p)))
  }
  where
  module Blocks = Order.Sum (Index.order I) (λ i → Normal.order (F i))

  point : Normal.Point P → Σ (Carrier I) (λ i → Normal.Point (F i))
  point c = Orders.Embedding.map e c
    , Normal.class (F (Orders.Embedding.map e c))
        (t (Orders.Embedding.map e c))
