{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Presentation.Normalization.Presentation
  where

-- An exact small order gives a presentation at any level, and embeddings,
-- initial maps, and proper segments of exact orders give those of their
-- presentations.
-- Initial maps into normalized targets return maps into the original
-- presentations.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Accessibility using (acc; is-accessible)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization as Normalization
import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order
import SPT.Cubical.OrdinalGeometry.ExactOrder.Maps as Orders
import SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.Embedding
  as Segments

private
  variable
    ℓ : Level
    A : Set

  Strict : Order.Order A → Lift ℓ A → Lift ℓ A → Set ℓ
  Strict O x y = Lift _ (Order.Order._<_ O (lower x) (lower y))

  accessible : (O : Order.Order A) (x : Lift ℓ A)
    → is-accessible (Order.Order._<_ O) (lower x) → is-accessible (Strict O) x
  accessible O x (acc smaller) = acc λ y p →
    accessible O y (smaller (lower y) (lower p))

  enumeration : Order.Order A → ℕ → Maybe (Lift ℓ A)
  enumeration O n = maybe-map lift (Order.Order.enum O n)

  coverage : (O : Order.Order A) (x : Lift ℓ A)
    → Σ ℕ (λ n → enumeration O n ＝ just x)
  coverage O (lift x) with Order.Order.covers O x
  ... | n , p = n , ap (maybe-map lift) p

  comparison : (O : Order.Order A) (x y : Lift ℓ A)
    → Strict O x y ⊎ (Lift ℓ (lower x ＝ lower y) ⊎ Strict O y x)
  comparison O x y with Order.Order.compare O (lower x) (lower y)
  ... | inl p = inl (lift p)
  ... | inr (inl p) = inr (inl (lift p))
  ... | inr (inr p) = inr (inr (lift p))

presentation : Order.Order A → 𝒫 ℓ
presentation {A = A} {ℓ = ℓ} O = record
  { X = Lift ℓ A
  ; _≈_ = λ x y → Lift ℓ (lower x ＝ lower y)
  ; _<_ = Strict O
  ; ≈-refl = λ x → lift refl
  ; ≈-sym = λ p → lift (lower p ⁻¹)
  ; ≈-trans = λ p q → lift (lower p ∙ lower q)
  ; <-trans = λ p q → lift (Order.Order.trans O (lower p) (lower q))
  ; <-respˡ-≈ = λ p q → lift
      (transport (λ x → Order.Order._<_ O x _) (lower p) (lower q))
  ; <-respʳ-≈ = λ p q → lift
      (transport (λ y → Order.Order._<_ O _ y) (lower p) (lower q))
  ; <-wf = λ x → accessible O x (Order.Order.wf O (lower x))
  ; compare = comparison O
  ; enum = enumeration O
  ; covers = λ x → let n , p = coverage O x in n , x , p , lift refl
  }

initial : {A B : Set} {O : Order.Order A} {O′ : Order.Order B}
  → Orders.Initial O O′
  → Maps.Initial (presentation {ℓ = ℓ} O) (presentation O′)
initial f = record
  { map = λ x → lift (Orders.Initial.map f (lower x))
  ; resp = λ p → lift (ap (Orders.Initial.map f) (lower p))
  ; strict = λ p → lift (Orders.Initial.strict f (lower p))
  ; lower = λ x y p →
      let z , q = Orders.Initial.lower f (lower x) (lower y) (lower p)
      in lift z , lift q
  }

embedding : {A B : Set} {O : Order.Order A} {O′ : Order.Order B}
  → Orders.Embedding O O′
  → Maps.Embedding (presentation {ℓ = ℓ} O) (presentation O′)
embedding f = record
  { map = λ x → lift (Orders.Embedding.map f (lower x))
  ; resp = λ p → lift (ap (Orders.Embedding.map f) (lower p))
  ; strict = λ p → lift (Orders.Embedding.strict f (lower p))
  }

segment : {A B : Set} {O : Order.Order A} {O′ : Order.Order B}
  → Segments.Segment O O′
  → Maps.Segment (presentation {ℓ = ℓ} O) (presentation O′)
segment e = record
  { bound = record
      { to = λ x → lift (Segments.Segment.embed e (lower x))
      ; to-≈ = λ p → lift (ap (Segments.Segment.embed e) (lower p))
      ; to-< = λ p → lift (Segments.Segment.preserve e (lower p))
      ; reflects-< = λ p → lift (Segments.Segment.reflect e (lower p))
      ; ceiling = lift (Segments.Segment.cut e)
      ; below = λ x → lift (Segments.Segment.below e (lower x))
      }
  ; covers = λ y p →
      let x , q = Segments.Segment.cover e (lower y) (lower p)
      in lift x , lift q
  }

return-map : (O : Order.Order A) (Q : 𝒫 ℓ)
  → Orders.Initial O (Normalization.order Q) → Lift ℓ A → 𝒫.X Q
return-map O Q f x =
  Normalization.representative Q (Orders.Initial.map f (lower x))

private
  cover : (O : Order.Order A) (Q : 𝒫 ℓ)
    → (f : Orders.Initial O (Normalization.order Q))
    → (x : Lift ℓ A) (y : 𝒫.X Q) → 𝒫._<_ Q y (return-map O Q f x)
    → Σ (Lift ℓ A) (λ z → 𝒫._≈_ Q (return-map O Q f z) y)
  cover O Q f x y p with Orders.Initial.lower f (lower x)
    (Normalization.class Q y)
    (transport (Normalization.Strict Q (Normalization.class Q y))
      (Normalization.class-representative Q (Orders.Initial.map f (lower x)))
      (Normalization.class-strict Q p))
  ... | z , q = lift z , transport
    (λ a → 𝒫._≈_ Q (Normalization.representative Q a) y)
    (q ⁻¹) (Normalization.representative-class Q y)

returned : (O : Order.Order A) (Q : 𝒫 ℓ)
  → Orders.Initial O (Normalization.order Q) → Maps.Initial (presentation O) Q
returned O Q f = record
  { map = return-map O Q f
  ; resp = λ {x} {y} p → transport (𝒫._≈_ Q (return-map O Q f x))
      (ap (λ a → Normalization.representative Q (Orders.Initial.map f a))
        (lower p)) (𝒫.≈-refl Q _)
  ; strict = λ {x} {y} p → Normalization.representative-strict Q
      {a = Orders.Initial.map f (lower x)}
      {b = Orders.Initial.map f (lower y)} (Orders.Initial.strict f (lower p))
  ; lower = cover O Q f
  }

normalized : 𝒫 ℓ → 𝒫 ℓ
normalized P = presentation (Normalization.order P)

quotient : (P : 𝒫 ℓ) → Maps.Initial P (normalized P)
quotient P = record
  { map = λ x → lift (Normalization.class P x)
  ; resp = λ p → lift (Normalization.class-resp P p)
  ; strict = λ p → lift (Normalization.class-strict P p)
  ; lower = λ _ y _ → Normalization.representative P (lower y) ,
      lift (Normalization.class-representative P (lower y))
  }

section : (P : 𝒫 ℓ) → Maps.Initial (normalized P) P
section P = returned (Normalization.order P) P
  (Orders.identity (Normalization.order P))
