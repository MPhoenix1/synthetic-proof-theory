{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Presentation.Sum.Indexed.Equivalence
  where

-- Equivalences of the blocks of an ordered sum over one index give an
-- equivalence of the sums (equivalence). Each block equivalence gives an
-- order isomorphism of normalized points (Normalization.Maps.iso); the
-- sum maps a point (i, a) of block i to (i, forward a), keeping its block,
-- and back by the inverse isomorphism. Both laws hold as equalities of
-- points, from the laws of the isomorphisms.

open import Agda.Primitive using (Level; lzero)
open import Data.Product using (Σ; _,_)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; cong)

open import SPT.Cubical.Core.Equality.Isomorphism using (_≅_)
import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order
import SPT.Cubical.OrdinalGeometry.ExactOrder.Maps as Orders
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization as Normal
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization.Maps
  as NormalMaps
import SPT.Cubical.OrdinalGeometry.ExactOrder.OrderedSum as Index
open Index using (Ordinal; Carrier)
open import SPT.Cubical.OrdinalGeometry.Presentation.Sum.Indexed using (sum)

private
  variable
    ℓ : Level

-- Mathematical shape: (Π i. F i ≃ G i) → Σ_{i ∈ I} F i ≃ Σ_{i ∈ I} G i.
equivalence : {I : Ordinal lzero} {F G : Carrier I → 𝒫 ℓ}
  → ((i : Carrier I) → F i Presented.≃𝒫 G i)
  → sum I F Presented.≃𝒫 sum I G
equivalence {I = I} {F} {G} e = record
  { to = λ x → lift (to (lower x))
  ; from = λ y → lift (from (lower y))
  ; to-≈ = λ p → lift (cong to (lower p))
  ; from-≈ = λ p → lift (cong from (lower p))
  ; to-< = λ p → lift (forth (lower p))
  ; from-< = λ p → lift (back (lower p))
  ; from-to-≈ = λ x → lift (from-to (lower x))
  ; to-from-≈ = λ y → lift (to-from (lower y))
  }
  where
  module Source = Order.Sum (Index.order I) (λ i → Normal.order (F i))
  module Target = Order.Sum (Index.order I) (λ i → Normal.order (G i))

  -- The blocks, normalized, in both directions.
  forward : (i : Carrier I)
    → Orders.Iso (Normal.order (F i)) (Normal.order (G i))
  forward i = NormalMaps.iso (e i)

  backward : (i : Carrier I)
    → Orders.Iso (Normal.order (G i)) (Normal.order (F i))
  backward i = NormalMaps.iso (Presented.≃𝒫-sym (e i))

  to : Σ (Carrier I) (λ i → Normal.Point (F i))
    → Σ (Carrier I) (λ i → Normal.Point (G i))
  to (i , a) = i , Orders.Iso.forward (forward i) a

  from : Σ (Carrier I) (λ i → Normal.Point (G i))
    → Σ (Carrier I) (λ i → Normal.Point (F i))
  from (i , b) = i , Orders.Iso.forward (backward i) b

  forth : ∀ {x y} → Source._<_ x y → Target._<_ (to x) (to y)
  forth (Source.earlier p) = Target.earlier p
  forth (Source.within i {a} {b} q) =
    Target.within i (Orders.Iso.strict (forward i) {a} {b} q)

  back : ∀ {x y} → Target._<_ x y → Source._<_ (from x) (from y)
  back (Target.earlier p) = Source.earlier p
  back (Target.within i {a} {b} q) =
    Source.within i (Orders.Iso.strict (backward i) {a} {b} q)

  from-to : (x : Σ (Carrier I) (λ i → Normal.Point (F i))) → from (to x) ≡ x
  from-to (i , a) = cong (i ,_)
    (_≅_.backward-forward (Orders.Iso.equivalence (forward i)) a)

  to-from : (y : Σ (Carrier I) (λ i → Normal.Point (G i))) → to (from y) ≡ y
  to-from (i , b) = cong (i ,_)
    (_≅_.forward-backward (Orders.Iso.equivalence (forward i)) b)
