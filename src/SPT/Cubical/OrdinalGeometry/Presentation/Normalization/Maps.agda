{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Presentation.Normalization.Maps where

-- Embeddings, initial maps, principal segments, and order equivalences
-- descend to normalized ordinal points. The class equations remove
-- representative choices; changing an enumeration gives the corresponding
-- order isomorphism.

open import Agda.Primitive using (Level)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; trans)
import SPT.Cubical.TypeTopology.UF.Equiv as Equiv

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
open import SPT.Cubical.OrdinalGeometry.Presentation.Normalization using
  (Point; Strict; order; class; representative; class-resp;
   representative-class; class-representative; class-strict;
   representative-strict)
import SPT.Cubical.OrdinalGeometry.ExactOrder.Maps as Orders
import SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.Embedding as Segments

private
  variable
    ℓ : Level
    P Q : 𝒫 ℓ

map : Maps.Initial P Q → Point P → Point Q
map {P = P} {Q} f x = class Q (Maps.Initial.map f (representative P x))

map-β : (f : Maps.Initial P Q) (x : 𝒫.X P)
  → map f (class P x) ≡ class Q (Maps.Initial.map f x)
map-β {P = P} {Q} f x =
  class-resp Q (Maps.Initial.resp f (representative-class P x))

private
  strict : (f : Maps.Initial P Q) {x y : Point P}
    → Strict P x y → Strict Q (map f x) (map f y)
  strict {P = P} {Q} f {x} {y} p = class-strict Q
    (Maps.Initial.strict f (representative-strict P {a = x} {b = y} p))

  cover : (f : Maps.Initial P Q) (x : Point P) (y : Point Q)
    → Strict Q y (map f x) → Σ (Point P) (λ z → map f z ≡ y)
  cover {P = P} {Q} f x y p with Maps.Initial.lower f
    (representative P x) (representative Q y)
    (𝒫.<-respʳ-≈ Q
      (representative-class Q (Maps.Initial.map f (representative P x)))
      (representative-strict Q {a = y} {b = map f x} p))
  ... | z , q = class P z , trans (map-β f z)
    (trans (class-resp Q q) (class-representative Q y))

-- An order embedding descends to normalized points by the same formula.
embedding : Maps.Embedding P Q → Orders.Embedding (order P) (order Q)
embedding {P = P} {Q} f = record
  { map = λ x → class Q (Maps.Embedding.map f (representative P x))
  ; strict = λ {x} {y} p → class-strict Q
      (Maps.Embedding.strict f (representative-strict P {a = x} {b = y} p))
  }

embedding-β : (f : Maps.Embedding P Q) (x : 𝒫.X P)
  → Orders.Embedding.map (embedding f) (class P x)
    ≡ class Q (Maps.Embedding.map f x)
embedding-β {P = P} {Q} f x =
  class-resp Q (Maps.Embedding.resp f (representative-class P x))

initial : Maps.Initial P Q → Orders.Initial (order P) (order Q)
initial f = record
  { map = map f
  ; strict = λ {x} {y} → strict f {x} {y}
  ; lower = cover f
  }

private
  underlying : Maps.Segment P Q → Maps.Initial P Q
  underlying {Q = Q} s = record
    { map = Presented._≺𝒫_.to (Maps.Segment.bound s)
    ; resp = Presented._≺𝒫_.to-≈ (Maps.Segment.bound s)
    ; strict = Presented._≺𝒫_.to-< (Maps.Segment.bound s)
    ; lower = λ x y p → Maps.Segment.covers s y
        (𝒫.<-trans Q p (Presented._≺𝒫_.below (Maps.Segment.bound s) x))
    }

  cut-cover : (s : Maps.Segment P Q) (y : Point Q)
    → Strict Q y (class Q (Presented._≺𝒫_.ceiling (Maps.Segment.bound s)))
    → Σ (Point P) (λ x → map (underlying s) x ≡ y)
  cut-cover {P = P} {Q} s y p with Maps.Segment.covers s
    (representative Q y)
    (𝒫.<-respʳ-≈ Q
      (representative-class Q
        (Presented._≺𝒫_.ceiling (Maps.Segment.bound s)))
      (representative-strict Q {a = y}
        {b = class Q (Presented._≺𝒫_.ceiling (Maps.Segment.bound s))} p))
  ... | x , q = class P x , trans (map-β (underlying s) x)
    (trans (class-resp Q q) (class-representative Q y))

segment : Maps.Segment P Q → Segments.Segment (order P) (order Q)
segment {P = P} {Q} s = record
  { embed = map (underlying s)
  ; cut = class Q (Presented._≺𝒫_.ceiling (Maps.Segment.bound s))
  ; below = λ x → class-strict Q
      (Presented._≺𝒫_.below (Maps.Segment.bound s) (representative P x))
  ; preserve = λ {x} {y} → strict (underlying s) {x} {y}
  ; cover = cut-cover s
  }

segment-β : (s : Maps.Segment P Q) (x : 𝒫.X P)
  → Segments.Segment.embed (segment s) (class P x)
    ≡ class Q (Presented._≺𝒫_.to (Maps.Segment.bound s) x)
segment-β s = map-β (underlying s)

iso : P Presented.≃𝒫 Q → Orders.Iso (order P) (order Q)
iso {P = P} {Q} e = record
  { equivalence = Orders.from-inverses
      (map (Maps.equivalence e))
      (map (Maps.equivalence (Presented.≃𝒫-sym e)))
      (λ x → trans (map-β (Maps.equivalence (Presented.≃𝒫-sym e)) _)
        (trans (class-resp P
          (Presented._≃𝒫_.from-to-≈ e (representative P x)))
          (class-representative P x)))
      (λ y → trans (map-β (Maps.equivalence e) _)
        (trans (class-resp Q
          (Presented._≃𝒫_.to-from-≈ e (representative Q y)))
          (class-representative Q y)))
  ; strict = λ {x} {y} → strict (Maps.equivalence e) {x} {y}
  }

-- A presentation comparison becomes a type equivalence after normalization.
equivalence : P Presented.≃𝒫 Q → Point P Equiv.≃ Point Q
equivalence e = Orders.Iso.equivalence (iso e)

iso-β : (e : P Presented.≃𝒫 Q) (x : 𝒫.X P)
  → Orders.Iso.forward (iso e) (class P x)
    ≡ class Q (Presented._≃𝒫_.to e x)
iso-β e = map-β (Maps.equivalence e)
