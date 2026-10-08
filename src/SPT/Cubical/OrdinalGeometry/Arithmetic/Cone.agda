{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Cone where

-- Predecessor domains ∂x = Σ y. y < x of points of sums and products.
-- An equivalence carries the domain of a point to the domain of its
-- image, and equivalent points have equivalent domains. In P + Q the
-- domain below a left point is its domain in P, and below a right point y
-- it is P + ∂y. In D · X the domain below the point (x, d) is
-- D · ∂x + ∂d. Points with equivalent domains are equivalent.

open import Agda.Primitive using (Level)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; sym; trans; subst)

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
transport : (e : P Presented.≃𝒫 Q) (x : 𝒫.X P)
  → ∂ P x Presented.≃𝒫 ∂ Q (Presented._≃𝒫_.to e x)
transport {P = P} e x = record
  { to = λ u → E.to (proj₁ u) , E.to-< (proj₂ u)
  ; from = λ v → E.from (proj₁ v) ,
      𝒫.<-respʳ-≈ P (E.from-to-≈ x) (E.from-< (proj₂ v))
  ; to-≈ = E.to-≈
  ; from-≈ = E.from-≈
  ; to-< = E.to-<
  ; from-< = E.from-<
  ; from-to-≈ = λ u → E.from-to-≈ (proj₁ u)
  ; to-from-≈ = λ v → E.to-from-≈ (proj₁ v)
  }
  where
  module E = Presented._≃𝒫_ e

-- Points with equivalent domains are equivalent: a strictly smaller
-- point has a strictly bounded domain.
injective : (P : 𝒫 ℓ) {x y : 𝒫.X P} → ∂ P x Presented.≃𝒫 ∂ P y
  → 𝒫._≈_ P x y
injective P {x} {y} e with 𝒫.compare P x y
... | inj₁ p =
  ⊥-elim (Presented.≃𝒫↛≺𝒫 e (Principal.Segments.Inside.strict P y x p))
... | inj₂ (inj₁ q) = q
... | inj₂ (inj₂ p) = ⊥-elim
  (Presented.≃𝒫↛≺𝒫 (Presented.≃𝒫-sym e)
    (Principal.Segments.Inside.strict P x y p))

-- Normalized points with equivalent domains are equal.
points : (P : 𝒫 ℓ) {a b : Normal.Point P}
  → domain P a Presented.≃𝒫 domain P b → a ≡ b
points P {a} {b} e = trans (sym (Normal.class-representative P a))
  (trans (Normal.class-resp P (injective P e))
    (Normal.class-representative P b))

------------------------------------------------------------------------
-- Sums

-- Below a left point of P + Q lies its domain in P.
left : (P Q : 𝒫 ℓ) (x : 𝒫.X P)
  → ∂ (P + Q) (inj₁ x) Presented.≃𝒫 ∂ P x
left P Q x = Presented.≃𝒫-sym (bijection embedding covers)
  where
  embedding : Maps.Embedding (∂ P x) (∂ (P + Q) (inj₁ x))
  embedding = record
    { map = λ u → inj₁ (proj₁ u) , proj₂ u
    ; resp = λ p → p
    ; strict = λ p → p
    }

  covers : (v : 𝒫.X (∂ (P + Q) (inj₁ x))) → Σ (𝒫.X (∂ P x)) (λ u →
    𝒫._≈_ (∂ (P + Q) (inj₁ x)) (Maps.Embedding.map embedding u) v)
  covers (inj₁ y , p) = (y , p) , 𝒫.≈-refl P y
  covers (inj₂ y , ())

-- Below a right point y of P + Q lie P and then ∂y.
right : (P Q : 𝒫 ℓ) (y : 𝒫.X Q)
  → ∂ (P + Q) (inj₂ y) Presented.≃𝒫 (P + ∂ Q y)
right P Q y = Presented.≃𝒫-sym (bijection (Sum.below P Q y) covers)
  where
  covers : (v : 𝒫.X (∂ (P + Q) (inj₂ y))) → Σ (𝒫.X (P + ∂ Q y)) (λ u →
    𝒫._≈_ (∂ (P + Q) (inj₂ y)) (Maps.Embedding.map (Sum.below P Q y) u) v)
  covers (inj₁ x , _) = inj₁ x , 𝒫.≈-refl P x
  covers (inj₂ z , p) = inj₂ (z , p) , 𝒫.≈-refl Q z

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
    ι w = Normal.class X (proj₁ (Normal.representative (domain X x) w))

    ι< : (w : Normal.Point (domain X x)) → Normal.Strict X (ι w) x
    ι< w = subst (Normal.Strict X (ι w)) (Normal.class-representative X x)
      (Normal.class-strict X
        {x = proj₁ (Normal.representative (domain X x) w)}
        {y = Normal.representative X x}
        (proj₂ (Normal.representative (domain X x) w)))

    ι-strict : {w w′ : Normal.Point (domain X x)}
      → Normal.Strict (domain X x) w w′
      → Normal.Strict X (ι w) (ι w′)
    ι-strict {w} {w′} p = Normal.class-strict X
      {x = proj₁ (Normal.representative (domain X x) w)}
      {y = proj₁ (Normal.representative (domain X x) w′)}
      (Normal.representative-strict (domain X x) {a = w} {b = w′} p)

    -- A point of D below d, as a normalized point below d.
    κ< : (z : 𝒫.X D) → 𝒫._<_ D z (Normal.representative D d)
      → Normal.Strict D (Normal.class D z) d
    κ< z q = subst (Normal.Strict D (Normal.class D z))
      (Normal.class-representative D d)
      (Normal.class-strict D {x = z} {y = Normal.representative D d} q)

    map : 𝒫.X ((D · (domain X x)) + (domain D d))
      → 𝒫.X (∂ (D · X) (point D X x d))
    map (inj₁ (lift (w , d₀))) =
      lift (ι w , d₀) , lift (Blocks.earlier {x = d₀} {y = d} (ι< w))
    map (inj₂ (z , q)) =
      lift (x , Normal.class D z) , lift (Blocks.within x (κ< z q))

    resp : ∀ {u v} → 𝒫._≈_ ((D · (domain X x)) + (domain D d)) u v
      → 𝒫._≈_ (∂ (D · X) (point D X x d)) (map u) (map v)
    resp {inj₁ _} {inj₁ _} (lift e) =
      lift (cong (λ u → ι (proj₁ u) , proj₂ u) e)
    resp {inj₁ _} {inj₂ _} ()
    resp {inj₂ _} {inj₁ _} ()
    resp {inj₂ (z , _)} {inj₂ (z′ , _)} p =
      lift (cong (x ,_) (Normal.class-resp D p))

    strict : ∀ {u v} → 𝒫._<_ ((D · (domain X x)) + (domain D d)) u v
      → 𝒫._<_ (∂ (D · X) (point D X x d)) (map u) (map v)
    strict {inj₁ (lift (w , a))} {inj₁ (lift (w′ , b))}
      (lift (Copies.earlier p)) =
      lift (Blocks.earlier {x = a} {y = b} (ι-strict {w} {w′} p))
    strict {inj₁ (lift (w , a))} {inj₁ (lift (.w , b))}
      (lift (Copies.within .w p)) = lift (Blocks.within (ι w) p)
    strict {inj₁ (lift (w , a))} {inj₂ (z , q)} _ =
      lift (Blocks.earlier {x = a} {y = Normal.class D z} (ι< w))
    strict {inj₂ _} {inj₁ _} ()
    strict {inj₂ (z , _)} {inj₂ (z′ , _)} p =
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
      inj₁ (lift (Normal.class (domain X x)
        (Normal.representative X x₀ , below) , d₀))
      , lift (cong (_, d₀) (trans
          (Normal.class-resp X
            (Normal.representative-class (domain X x)
              (Normal.representative X x₀ , below)))
          (Normal.class-representative X x₀)))
      where
      below : 𝒫._<_ X (Normal.representative X x₀) (Normal.representative X x)
      below = Normal.representative-strict X {a = x₀} {b = x} q
    covers (lift (.x , d₀) , lift (Blocks.within .x q)) =
      inj₂ (Normal.representative D d₀ ,
        Normal.representative-strict D {a = d₀} {b = d} q)
      , lift (cong (x ,_) (Normal.class-representative D d₀))
