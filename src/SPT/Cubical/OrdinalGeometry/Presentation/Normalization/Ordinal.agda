{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Presentation.Normalization.Ordinal where

-- The normalized points of a presentation L as an exact countable
-- ordinal, the cone ∂ L c below each point c, and the normalized points
-- below c, again an exact ordinal. The cone below any point lies in the
-- cone of its class (toClass). An order embedding L ↪ L′ moves all three:
-- - a point goes to the class of its image (points-map);
-- - its cone embeds into the cone at that class (carry);
-- - the points below it go pointwise below the image (descend).

open import Agda.Primitive using (lzero)
open import Data.Product using (_,_; proj₁; proj₂)

open import SPT.Cubical.Core.WellFounded using (Acc)
import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Sum as Sum
open Sum using (∂)
import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order
import SPT.Cubical.OrdinalGeometry.ExactOrder.Maps as Orders
import SPT.Cubical.OrdinalGeometry.ExactOrder.Lower as Lower
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization as Normal
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization.Maps
  as NormalMaps
import SPT.Cubical.OrdinalGeometry.ExactOrder.OrderedSum as Index
open Index using (Ordinal)

------------------------------------------------------------------------
-- Points, cones and lower points

-- The normalized points of a presentation, as an exact ordinal.
points : 𝒫 lzero → Ordinal lzero
points L = Index.ordinal (Normal.Point L) (Normal.order L)

-- The cone below a normalized point.
cone : (L : 𝒫 lzero) → Normal.Point L → 𝒫 lzero
cone L c = ∂ L (Normal.representative L c)

-- The normalized points below c, as an exact ordinal.
below : (L : 𝒫 lzero) → Normal.Point L → Ordinal lzero
below L c = Index.ordinal (Order.Order.Pred (Normal.order L) c)
  (Lower.Segments.Below.order (Normal.order L)
    (λ {a} {b} → Normal.strict-unique L {a} {b}) c)

-- Accessibility of the normalized points.
Accessible : (L : 𝒫 lzero) → Normal.Point L → Set
Accessible L = Acc (Order.Order._<_ (Normal.order L))

accessible : (L : 𝒫 lzero) (c : Normal.Point L) → Accessible L c
accessible L = Order.Order.wf (Normal.order L)

------------------------------------------------------------------------
-- Transport along embeddings

-- An embedding of presentations, on normalized points.
points-map : {L L′ : 𝒫 lzero} → Maps.Embedding L L′
  → Orders.Embedding (Index.order (points L)) (Index.order (points L′))
points-map e = NormalMaps.embedding e

private
  -- Equivalent points have embedded cones.
  shift : (Q : 𝒫 lzero) {y y′ : 𝒫.X Q} → 𝒫._≈_ Q y y′
    → Maps.Embedding (∂ Q y) (∂ Q y′)
  shift Q q = record
    { map = λ u → proj₁ u , 𝒫.<-respʳ-≈ Q q (proj₂ u)
    ; resp = λ p → p
    ; strict = λ p → p
    }

-- Mathematical shape: ∂ L y ↪ cone L [y], the cone of the class of y.
toClass : (L : 𝒫 lzero) (y : 𝒫.X L)
  → Maps.Embedding (∂ L y) (cone L (Normal.class L y))
toClass L y = shift L (𝒫.≈-sym L (Normal.representative-class L y))

-- An embedding moves each cone into the cone at the image.
carry : {L L′ : 𝒫 lzero} (e : Maps.Embedding L L′) (c : Normal.Point L)
  → Maps.Embedding (cone L c)
      (cone L′ (Orders.Embedding.map (points-map e) c))
carry {L} {L′} e c = Maps.composite {P = cone L c}
  {Q = ∂ L′ (Maps.Embedding.map e (Normal.representative L c))}
  {R = cone L′ (Orders.Embedding.map (points-map e) c)}
  (Sum.restrict e (Normal.representative L c))
  (shift L′ (𝒫.≈-sym L′ (Normal.representative-class L′
    (Maps.Embedding.map e (Normal.representative L c)))))

-- The points below c move to the points below its image.
descend : {L L′ : 𝒫 lzero} (e : Maps.Embedding L L′) (c : Normal.Point L)
  → Orders.Embedding (Index.order (below L c))
      (Index.order (below L′ (Orders.Embedding.map (points-map e) c)))
descend e c = record
  { map = λ b → Orders.Embedding.map E (proj₁ b)
      , Orders.Embedding.strict E {proj₁ b} {c} (proj₂ b)
  ; strict = λ {u} {v} q →
      Orders.Embedding.strict E {proj₁ u} {proj₁ v} q
  }
  where E = points-map e
