{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Cone where

-- Predecessor domains ∂x = Σ y. y < x of points of sums and products.
-- An equivalence carries the domain of a point to the domain of its
-- image, and equivalent points have equivalent domains. In P + Q the
-- domain below a left point is its domain in P, and below a right point y
-- it is P + ∂y. In D · X the domain below the point (x, d) is
-- D · ∂x + ∂d. Points with equivalent domains are equivalent.

open import SPT.Cubical.Base hiding (_+_)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Principal as Principal
open import SPT.Cubical.OrdinalGeometry.Presentation.Sum using (_+_; ∂)
import SPT.Cubical.OrdinalGeometry.Presentation.Sum as Sum
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization as Normal
import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization using
  (bijection)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Multiplication using
  (_·_; point)

private
  variable
    ℓ : Level
    P Q : 𝒫 ℓ

------------------------------------------------------------------------
-- Domains of normalized points

-- The predecessor domain of a normalized point, at its representative.
domain : (X : 𝒫 ℓ) → Normal.Point X → 𝒫 ℓ
domain X x = ∂ X (Normal.representative X x)

-- It is a proper segment of X.
inside : (X : 𝒫 ℓ) (x : Normal.Point X) → Maps.Segment (domain X x) X
inside X x = Sum.cone X (Normal.representative X x)

------------------------------------------------------------------------
-- Transport and injectivity

-- An equivalence carries ∂x to ∂(e x).
carried : (e : P Presented.≃𝒫 Q) (x : 𝒫.X P)
  → ∂ P x Presented.≃𝒫 ∂ Q (Presented._≃𝒫_.to e x)
carried {P = P} e x = record
  { to = λ u → E.to (pr₁ u) , E.to-< (pr₂ u)
  ; from = λ v → E.from (pr₁ v) ,
      𝒫.<-respʳ-≈ P (E.from-to-≈ x) (E.from-< (pr₂ v))
  ; to-≈ = E.to-≈
  ; from-≈ = E.from-≈
  ; to-< = E.to-<
  ; from-< = E.from-<
  ; from-to-≈ = λ u → E.from-to-≈ (pr₁ u)
  ; to-from-≈ = λ v → E.to-from-≈ (pr₁ v)
  }
  where
  module E = Presented._≃𝒫_ e

-- Points with equivalent domains are equivalent: a strictly smaller
-- point has a strictly bounded domain.
injective : (P : 𝒫 ℓ) {x y : 𝒫.X P} → ∂ P x Presented.≃𝒫 ∂ P y
  → 𝒫._≈_ P x y
injective P {x} {y} e with 𝒫.compare P x y
... | inl p =
  𝟘-elim (Presented.≃𝒫↛≺𝒫 e (Principal.Segments.Inside.strict P y x p))
... | inr (inl q) = q
... | inr (inr p) = 𝟘-elim
  (Presented.≃𝒫↛≺𝒫 (Presented.≃𝒫-sym e)
    (Principal.Segments.Inside.strict P x y p))

-- Normalized points with equivalent domains are equal.
points : (P : 𝒫 ℓ) {a b : Normal.Point P}
  → domain P a Presented.≃𝒫 domain P b → a ＝ b
points P {a} {b} e = Normal.class-representative P a ⁻¹
  ∙ (Normal.class-resp P (injective P e)
    ∙ Normal.class-representative P b)

------------------------------------------------------------------------
-- Sums

-- Below a left point of P + Q lies its domain in P.
left : (P Q : 𝒫 ℓ) (x : 𝒫.X P)
  → ∂ (P + Q) (inl x) Presented.≃𝒫 ∂ P x
left P Q x = Presented.≃𝒫-sym (bijection embedding covers)
  where
  embedding : Maps.Embedding (∂ P x) (∂ (P + Q) (inl x))
  embedding = record
    { map = λ u → inl (pr₁ u) , pr₂ u
    ; resp = λ p → p
    ; strict = λ p → p
    }

  covers : (v : 𝒫.X (∂ (P + Q) (inl x))) → Σ (𝒫.X (∂ P x)) (λ u →
    𝒫._≈_ (∂ (P + Q) (inl x)) (Maps.Embedding.map embedding u) v)
  covers (inl y , p) = (y , p) , 𝒫.≈-refl P y
  covers (inr y , ())

-- Below a right point y of P + Q lie P and then ∂y.
right : (P Q : 𝒫 ℓ) (y : 𝒫.X Q)
  → ∂ (P + Q) (inr y) Presented.≃𝒫 (P + ∂ Q y)
right P Q y = Presented.≃𝒫-sym (bijection (Sum.below P Q y) covers)
  where
  covers : (v : 𝒫.X (∂ (P + Q) (inr y))) → Σ (𝒫.X (P + ∂ Q y)) (λ u →
    𝒫._≈_ (∂ (P + Q) (inr y)) (Maps.Embedding.map (Sum.below P Q y) u) v)
  covers (inl x , _) = inl x , 𝒫.≈-refl P x
  covers (inr z , p) = inr (z , p) , 𝒫.≈-refl Q z

------------------------------------------------------------------------
-- Products

opaque
  unfolding _·_ point

  -- Mathematical shape: ∂_{D·X}(x, d) ≃ D · ∂x + ∂d. A point below
  -- (x, d) lies in an earlier block, a copy of D at a point below x, or
  -- in the block of x below d.
  product : (D X : 𝒫 ℓ) (x : Normal.Point X) (d : Normal.Point D)
    → ((D · domain X x) + domain D d)
      Presented.≃𝒫 ∂ (D · X) (point D X x d)
  product D X x d = bijection embedding covers
    where
    module Blocks = Order.Sum (Normal.order X) (λ _ → Normal.order D)
    module Copies =
      Order.Sum (Normal.order (domain X x)) (λ _ → Normal.order D)

    -- A normalized point of ∂x, as a normalized point of X below x.
    ι : Normal.Point (domain X x) → Normal.Point X
    ι w = Normal.class X (pr₁ (Normal.representative (domain X x) w))

    ι< : (w : Normal.Point (domain X x)) → Normal.Strict X (ι w) x
    ι< w = transport (Normal.Strict X (ι w)) (Normal.class-representative X x)
      (Normal.class-strict X
        {x = pr₁ (Normal.representative (domain X x) w)}
        {y = Normal.representative X x}
        (pr₂ (Normal.representative (domain X x) w)))

    ι-strict : {w w′ : Normal.Point (domain X x)}
      → Normal.Strict (domain X x) w w′
      → Normal.Strict X (ι w) (ι w′)
    ι-strict {w} {w′} p = Normal.class-strict X
      {x = pr₁ (Normal.representative (domain X x) w)}
      {y = pr₁ (Normal.representative (domain X x) w′)}
      (Normal.representative-strict (domain X x) {a = w} {b = w′} p)

    -- A point of D below d, as a normalized point below d.
    κ< : (z : 𝒫.X D) → 𝒫._<_ D z (Normal.representative D d)
      → Normal.Strict D (Normal.class D z) d
    κ< z q = transport (Normal.Strict D (Normal.class D z))
      (Normal.class-representative D d)
      (Normal.class-strict D {x = z} {y = Normal.representative D d} q)

    map : 𝒫.X ((D · (domain X x)) + (domain D d))
      → 𝒫.X (∂ (D · X) (point D X x d))
    map (inl (lift (w , d₀))) =
      lift (ι w , d₀) , lift (Blocks.earlier {x = d₀} {y = d} (ι< w))
    map (inr (z , q)) =
      lift (x , Normal.class D z) , lift (Blocks.within x (κ< z q))

    resp : ∀ {u v} → 𝒫._≈_ ((D · (domain X x)) + (domain D d)) u v
      → 𝒫._≈_ (∂ (D · X) (point D X x d)) (map u) (map v)
    resp {inl _} {inl _} (lift e) =
      lift (ap (λ u → ι (pr₁ u) , pr₂ u) e)
    resp {inl _} {inr _} ()
    resp {inr _} {inl _} ()
    resp {inr (z , _)} {inr (z′ , _)} p =
      lift (ap (x ,_) (Normal.class-resp D p))

    strict : ∀ {u v} → 𝒫._<_ ((D · (domain X x)) + (domain D d)) u v
      → 𝒫._<_ (∂ (D · X) (point D X x d)) (map u) (map v)
    strict {inl (lift (w , a))} {inl (lift (w′ , b))}
      (lift (Copies.earlier p)) =
      lift (Blocks.earlier {x = a} {y = b} (ι-strict {w} {w′} p))
    strict {inl (lift (w , a))} {inl (lift (.w , b))}
      (lift (Copies.within .w p)) = lift (Blocks.within (ι w) p)
    strict {inl (lift (w , a))} {inr (z , q)} _ =
      lift (Blocks.earlier {x = a} {y = Normal.class D z} (ι< w))
    strict {inr _} {inl _} ()
    strict {inr (z , _)} {inr (z′ , _)} p =
      lift (Blocks.within x (Normal.class-strict D {x = z} {y = z′} p))

    embedding : Maps.Embedding ((D · (domain X x)) + (domain D d))
      (∂ (D · X) (point D X x d))
    embedding = record
      { map = map
      ; resp = λ {u} {v} → resp {u} {v}
      ; strict = λ {u} {v} → strict {u} {v}
      }

    -- A point of an earlier block comes from ∂x, one of the block of x
    -- from ∂d.
    covers : (v : 𝒫.X (∂ (D · X) (point D X x d)))
      → Σ (𝒫.X ((D · (domain X x)) + (domain D d))) (λ u →
          𝒫._≈_ (∂ (D · X) (point D X x d)) (map u) v)
    covers (lift (x₀ , d₀) , lift (Blocks.earlier q)) =
      inl (lift (Normal.class (domain X x)
        (Normal.representative X x₀ , below) , d₀))
      , lift (ap (_, d₀) (
          (Normal.class-resp X
            (Normal.representative-class (domain X x)
              (Normal.representative X x₀ , below)))
          ∙ Normal.class-representative X x₀))
      where
      below : 𝒫._<_ X (Normal.representative X x₀) (Normal.representative X x)
      below = Normal.representative-strict X {a = x₀} {b = x} q
    covers (lift (.x , d₀) , lift (Blocks.within .x q)) =
      inr (Normal.representative D d₀ ,
        Normal.representative-strict D {a = d₀} {b = d} q)
      , lift (ap (x ,_) (Normal.class-representative D d₀))
