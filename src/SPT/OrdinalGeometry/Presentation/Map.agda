{-# OPTIONS --safe --without-K #-}

module SPT.OrdinalGeometry.Presentation.Map where

-- Order embeddings and initial maps of presented ordinals, their comparison
-- laws, and proper principal segments with predecessor coverage. An order
-- embedding (`Embedding`) reflects < and ≈ (`embedding-reflect`,
-- `embedding-reflect-≈`), never descends (`nondecreasing`) and admits no
-- bounded embedding back (`no-reverse`). An initial map (`Initial`) keeps a
-- preimage for every predecessor of an image point; initial maps compose,
-- are pointwise unique up to ≈ (`Uniqueness.pointwise`), and two opposite
-- ones give an equivalence (`antisymmetry`); an initial map with an
-- embedding back is onto (`surjective`, `isomorphism`). A principal segment
-- (`Segment`) covers its domain below its ceiling and so extends to the
-- successor (`segment-closed`).

open import SPT.Base
open import SPT.Foundation.Accessibility using (is-accessible; acc)
import SPT.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (Countable-Ordinal𝒫 to 𝒫)
open Presented.Diagonal.Successor using
  (Entry; point; top; point≈; top≈; point<; point<top)
open import SPT.OrdinalGeometry.Presentation.Successor using
  (constant-presentation-family; presentation-successor)

------------------------------------------------------------------------
-- Order embeddings

-- An order embedding has no selected ceiling or predecessor-coverage law.
record Embedding {ℓ : Level} (P Q : 𝒫 ℓ) : Set ℓ where
  field
    map : 𝒫.X P → 𝒫.X Q
    resp : {x y : 𝒫.X P} → 𝒫._≈_ P x y → 𝒫._≈_ Q (map x) (map y)
    strict : {x y : 𝒫.X P} → 𝒫._<_ P x y → 𝒫._<_ Q (map x) (map y)

module _ {ℓ : Level} {P Q : 𝒫 ℓ} where

  embedding-reflect : (f : Embedding P Q) {x y : 𝒫.X P} →
    𝒫._<_ Q (Embedding.map f x) (Embedding.map f y) → 𝒫._<_ P x y
  embedding-reflect f {x} {y} p with 𝒫.compare P x y
  ... | inl q = q
  ... | inr (inl q) =
    𝟘-elim (Presented.Presentation.≈↛< Q (Embedding.resp f q) p)
  ... | inr (inr q) =
    𝟘-elim (Presented.Presentation.<-asym Q p (Embedding.strict f q))

  embedding-reflect-≈ : (f : Embedding P Q) {x y : 𝒫.X P} →
    𝒫._≈_ Q (Embedding.map f x) (Embedding.map f y) → 𝒫._≈_ P x y
  embedding-reflect-≈ f {x} {y} p with 𝒫.compare P x y
  ... | inl q =
    𝟘-elim (Presented.Presentation.≈↛< Q p (Embedding.strict f q))
  ... | inr (inl q) = q
  ... | inr (inr q) =
    𝟘-elim
      (Presented.Presentation.≈↛< Q (𝒫.≈-sym Q p) (Embedding.strict f q))

module _ {ℓ : Level} {P : 𝒫 ℓ} where

  ascending : (f : Embedding P P) (x : 𝒫.X P) →
    is-accessible (𝒫._<_ P) x → ¬ (𝒫._<_ P (Embedding.map f x) x)
  ascending f x (acc smaller) p =
    ascending f (Embedding.map f x) (smaller (Embedding.map f x) p)
      (Embedding.strict f p)

abstract
  nondecreasing : {ℓ : Level} {P : 𝒫 ℓ} (f : Embedding P P)
    (x : 𝒫.X P) → ¬ (𝒫._<_ P (Embedding.map f x) x)
  nondecreasing {ℓ} {P} f x = ascending f x (𝒫.<-wf P x)

  no-reverse : {ℓ : Level} {P Q : 𝒫 ℓ} →
    Embedding P Q → ¬ (Q Presented.≺𝒫 P)
  no-reverse {ℓ} {P} {Q} f e = Presented.Embedding.irrefl Q record
    { to = λ x → Embedding.map f (Presented.Embedding.to e x)
    ; to-≈ = λ p → Embedding.resp f (Presented.Embedding.to-≈ e p)
    ; to-< = λ p → Embedding.strict f (Presented.Embedding.to-< e p)
    ; reflects-< = λ p →
        Presented.Embedding.reflects-< e (embedding-reflect f p)
    ; ceiling = Embedding.map f (Presented.Embedding.ceiling e)
    ; below = λ x → Embedding.strict f (Presented.Embedding.below e x)
    }

-- Two order embeddings in turn.
composite : {ℓ : Level} {P Q R : 𝒫 ℓ} → Embedding P Q → Embedding Q R →
  Embedding P R
composite f g = record
  { map = λ x → Embedding.map g (Embedding.map f x)
  ; resp = λ p → Embedding.resp g (Embedding.resp f p)
  ; strict = λ p → Embedding.strict g (Embedding.strict f p)
  }

------------------------------------------------------------------------
-- Initial maps

-- An initial map keeps a preimage, with its equivalence witness, for every
-- predecessor of every image point. Equivalence need not be identity. No
-- ceiling, image decision, or uniqueness of strict witnesses is required.
record Initial {ℓ : Level} (P Q : 𝒫 ℓ) : Set ℓ where
  open Presented.Countable-Ordinal𝒫 P using ()
    renaming (X to X₁; _≈_ to infix 6 _≈₁_; _<_ to infix 30 _<₁_)
  open Presented.Countable-Ordinal𝒫 Q using ()
    renaming (X to X₂; _≈_ to infix 6 _≈₂_; _<_ to infix 30 _<₂_)
  field
    map : X₁ → X₂
    resp : {x y : X₁} → x ≈₁ y → map x ≈₂ map y
    strict : {x y : X₁} → x <₁ y → map x <₂ map y
    lower : (x : X₁) (y : X₂) → y <₂ map x → Σ X₁ (λ z → map z ≈₂ y)

module _ {ℓ : Level} {P Q : 𝒫 ℓ} where

  initial-reflect : (f : Initial P Q) {x y : 𝒫.X P} →
    𝒫._<_ Q (Initial.map f x) (Initial.map f y) → 𝒫._<_ P x y
  initial-reflect f {x} {y} p with 𝒫.compare P x y
  ... | inl q = q
  ... | inr (inl q) =
    𝟘-elim (Presented.Presentation.≈↛< Q (Initial.resp f q) p)
  ... | inr (inr q) =
    𝟘-elim (Presented.Presentation.<-asym Q p (Initial.strict f q))

  initial-reflect-≈ : (f : Initial P Q) {x y : 𝒫.X P} →
    𝒫._≈_ Q (Initial.map f x) (Initial.map f y) → 𝒫._≈_ P x y
  initial-reflect-≈ f {x} {y} p with 𝒫.compare P x y
  ... | inl q =
    𝟘-elim (Presented.Presentation.≈↛< Q p (Initial.strict f q))
  ... | inr (inl q) = q
  ... | inr (inr q) =
    𝟘-elim
      (Presented.Presentation.≈↛< Q (𝒫.≈-sym Q p) (Initial.strict f q))

  -- Forgetting the lower law leaves an order embedding.
  initial-embedding : Initial P Q → Embedding P Q
  initial-embedding f = record
    { map = Initial.map f ; resp = Initial.resp f ; strict = Initial.strict f }

identity : {ℓ : Level} (P : 𝒫 ℓ) → Initial P P
identity P = record
  { map = λ x → x ; resp = λ p → p ; strict = λ p → p
  ; lower = λ _ y _ → y , 𝒫.≈-refl P y
  }

module _ {ℓ : Level} {P Q R : 𝒫 ℓ} where

  compose-lower : (f : Initial P Q) (g : Initial Q R) (x : 𝒫.X P)
    (z : 𝒫.X R) → 𝒫._<_ R z (Initial.map g (Initial.map f x)) →
    Σ (𝒫.X P) (λ y → 𝒫._≈_ R (Initial.map g (Initial.map f y)) z)
  compose-lower f g x z p with Initial.lower g (Initial.map f x) z p
  ... | y , q
    with Initial.lower f x y
           (initial-reflect g (𝒫.<-respˡ-≈ R (𝒫.≈-sym R q) p))
  ... | a , r = a , 𝒫.≈-trans R (Initial.resp g r) q

  compose : Initial P Q → Initial Q R → Initial P R
  compose f g = record
    { map = λ x → Initial.map g (Initial.map f x)
    ; resp = λ p → Initial.resp g (Initial.resp f p)
    ; strict = λ p → Initial.strict g (Initial.strict f p)
    ; lower = compose-lower f g
    }

equivalence : {ℓ : Level} {P Q : 𝒫 ℓ} → P Presented.≃𝒫 Q → Initial P Q
equivalence e = record
  { map = Presented._≃𝒫_.to e
  ; resp = Presented._≃𝒫_.to-≈ e
  ; strict = Presented._≃𝒫_.to-< e
  ; lower = λ _ y _ →
      Presented._≃𝒫_.from e y , Presented._≃𝒫_.to-from-≈ e y
  }

-- An embedding carries a strict bound, including its selected ceiling.
carry : {ℓ : Level} {P Q R : 𝒫 ℓ} →
  P Presented.≺𝒫 Q → Embedding Q R → P Presented.≺𝒫 R
carry b f = record
  { to = λ x → Embedding.map f (Presented.Embedding.to b x)
  ; to-≈ = λ p → Embedding.resp f (Presented.Embedding.to-≈ b p)
  ; to-< = λ p → Embedding.strict f (Presented.Embedding.to-< b p)
  ; reflects-< = λ p →
      Presented.Embedding.reflects-< b (embedding-reflect f p)
  ; ceiling = Embedding.map f (Presented.Embedding.ceiling b)
  ; below = λ x → Embedding.strict f (Presented.Embedding.below b x)
  }

bounded : {ℓ : Level} {P Q R : 𝒫 ℓ} →
  P Presented.≺𝒫 Q → Initial Q R → P Presented.≺𝒫 R
bounded e f = record
  { to = λ x → Initial.map f (Presented.Embedding.to e x)
  ; to-≈ = λ p → Initial.resp f (Presented.Embedding.to-≈ e p)
  ; to-< = λ p → Initial.strict f (Presented.Embedding.to-< e p)
  ; reflects-< = λ p →
      Presented.Embedding.reflects-< e (initial-reflect f p)
  ; ceiling = Initial.map f (Presented.Embedding.ceiling e)
  ; below = λ x → Initial.strict f (Presented.Embedding.below e x)
  }

------------------------------------------------------------------------
-- Uniqueness and antisymmetry

-- Initial maps have pointwise equivalent images. The witnesses stay
-- equivalences in Q; neither identity of points nor identification of maps
-- is inferred.
module Uniqueness {ℓ : Level} {P Q : 𝒫 ℓ} (f g : Initial P Q) where

  agree : (x : 𝒫.X P) → is-accessible (𝒫._<_ P) x →
    𝒫._≈_ Q (Initial.map f x) (Initial.map g x)
  agree x (acc smaller)
    with 𝒫.compare Q (Initial.map f x) (Initial.map g x)
  ... | inr (inl q) = q
  ... | inl p with Initial.lower g x (Initial.map f x) p
  ...   | y , q =
    let r = initial-reflect g (𝒫.<-respˡ-≈ Q (𝒫.≈-sym Q q) p)
    in 𝟘-elim
         (Presented.Presentation.≈↛< Q
           (𝒫.≈-trans Q (agree y (smaller y r)) q) (Initial.strict f r))
  agree x (acc smaller) | inr (inr p)
    with Initial.lower f x (Initial.map g x) p
  ... | y , q =
    let r = initial-reflect f (𝒫.<-respˡ-≈ Q (𝒫.≈-sym Q q) p)
    in 𝟘-elim
         (Presented.Presentation.≈↛< Q
           (𝒫.≈-trans Q (𝒫.≈-sym Q (agree y (smaller y r))) q)
           (Initial.strict g r))

  abstract
    pointwise : (x : 𝒫.X P) → 𝒫._≈_ Q (Initial.map f x) (Initial.map g x)
    pointwise x = agree x (𝒫.<-wf P x)

antisymmetry : {ℓ : Level} {P Q : 𝒫 ℓ} →
  Initial P Q → Initial Q P → P Presented.≃𝒫 Q
antisymmetry {ℓ} {P} {Q} f g = record
  { to = Initial.map f ; from = Initial.map g
  ; to-≈ = Initial.resp f ; from-≈ = Initial.resp g
  ; to-< = Initial.strict f ; from-< = Initial.strict g
  ; from-to-≈ = Uniqueness.pointwise (compose f g) (identity P)
  ; to-from-≈ = Uniqueness.pointwise (compose g f) (identity Q)
  }

------------------------------------------------------------------------
-- Onto maps

-- An initial map with an order embedding in the opposite direction is onto.
-- Comparing x with f (g x) gives a preimage; a strict decrease is
-- impossible.
abstract
  surjective : {ℓ : Level} {P Q : 𝒫 ℓ} (f : Initial P Q) →
    Embedding Q P → (x : 𝒫.X Q) →
    Σ (𝒫.X P) (λ y → 𝒫._≈_ Q (Initial.map f y) x)
  surjective {ℓ} {P} {Q} f g x
    with 𝒫.compare Q x (Initial.map f (Embedding.map g x))
  ... | inl p = Initial.lower f (Embedding.map g x) x p
  ... | inr (inl p) = Embedding.map g x , 𝒫.≈-sym Q p
  ... | inr (inr p) = 𝟘-elim (nondecreasing self x p)
    where
    self : Embedding Q Q
    self = record
      { map = λ y → Initial.map f (Embedding.map g y)
      ; resp = λ q → Initial.resp f (Embedding.resp g q)
      ; strict = λ q → Initial.strict f (Embedding.strict g q)
      }

  onto : {ℓ : Level} {P Q : 𝒫 ℓ} (f : Initial P Q) →
    ((x : 𝒫.X Q) → Σ (𝒫.X P) (λ y → 𝒫._≈_ Q (Initial.map f y) x)) →
    P Presented.≃𝒫 Q
  onto {ℓ} {P} {Q} f covers = record
    { to = Initial.map f
    ; from = λ x → pr₁ (covers x)
    ; to-≈ = Initial.resp f
    ; from-≈ = λ {x} {y} p →
        initial-reflect-≈ f
          (𝒫.≈-trans Q (pr₂ (covers x))
            (𝒫.≈-trans Q p (𝒫.≈-sym Q (pr₂ (covers y)))))
    ; to-< = Initial.strict f
    ; from-< = λ {x} {y} p →
        initial-reflect f
          (𝒫.<-respʳ-≈ Q (𝒫.≈-sym Q (pr₂ (covers y)))
            (𝒫.<-respˡ-≈ Q (𝒫.≈-sym Q (pr₂ (covers x))) p))
    ; from-to-≈ = λ x →
        initial-reflect-≈ f (pr₂ (covers (Initial.map f x)))
    ; to-from-≈ = λ x → pr₂ (covers x)
    }

  onto-β : {ℓ : Level} {P Q : 𝒫 ℓ} (f : Initial P Q)
    (covers : (x : 𝒫.X Q) → Σ (𝒫.X P) (λ y → 𝒫._≈_ Q (Initial.map f y) x))
    (x : 𝒫.X P) →
    𝒫._≈_ Q (Presented._≃𝒫_.to (onto f covers) x) (Initial.map f x)
  onto-β {ℓ} {P} {Q} f covers x = 𝒫.≈-refl Q (Initial.map f x)

  isomorphism : {ℓ : Level} {P Q : 𝒫 ℓ} →
    Initial P Q → Embedding Q P → P Presented.≃𝒫 Q
  isomorphism f g = onto f (surjective f g)

------------------------------------------------------------------------
-- The successor and principal segments

module Successor {ℓ : Level} (P : 𝒫 ℓ) where

  next : 𝒫 ℓ
  next = presentation-successor P

  initial : Initial P next
  initial = record
    { map = point ; resp = point≈ ; strict = point<
    ; lower = λ { x (point y) (point< p) → y , point≈ (𝒫.≈-refl P y) }
    }

  strict : P Presented.≺𝒫 next
  strict = record
    { to = point ; to-≈ = point≈ ; to-< = point<
    ; reflects-< = λ { (point< p) → p }
    ; ceiling = top ; below = λ _ → point<top
    }

  module Into (Q : 𝒫 ℓ) (e : P Presented.≺𝒫 Q)
    (covers : (y : 𝒫.X Q) → 𝒫._<_ Q y (Presented.Embedding.ceiling e) →
      Σ (𝒫.X P) (λ x → 𝒫._≈_ Q (Presented.Embedding.to e x) y))
    where

    map : Entry (constant-presentation-family P) zero → 𝒫.X Q
    map (point x) = Presented.Embedding.to e x
    map top = Presented.Embedding.ceiling e

    lower-preimage : (x : Entry (constant-presentation-family P) zero)
      (y : 𝒫.X Q) → 𝒫._<_ Q y (map x) →
      Σ (Entry (constant-presentation-family P) zero)
        (λ z → 𝒫._≈_ Q (map z) y)
    lower-preimage (point x) y p
      with covers y (𝒫.<-trans Q p (Presented.Embedding.below e x))
    ... | z , q = point z , q
    lower-preimage top y p with covers y p
    ... | z , q = point z , q

    closed : Initial next Q
    closed = record
      { map = map
      ; resp = λ where
          (point≈ p) → Presented.Embedding.to-≈ e p
          top≈ → 𝒫.≈-refl Q (Presented.Embedding.ceiling e)
      ; strict = λ where
          (point< p) → Presented.Embedding.to-< e p
          (point<top {x}) → Presented.Embedding.below e x
      ; lower = lower-preimage
      }

-- A principal strict bound covers the whole domain below its selected
-- ceiling. That further coverage, absent from a bounded embedding alone,
-- extends its map to an initial map on the successor domain.
record Segment {ℓ : Level} (P Q : 𝒫 ℓ) : Set ℓ where
  field
    bound : P Presented.≺𝒫 Q
    covers : (y : 𝒫.X Q) →
      𝒫._<_ Q y (Presented.Embedding.ceiling bound) →
      Σ (𝒫.X P) (λ x → 𝒫._≈_ Q (Presented.Embedding.to bound x) y)

segment-closed : {ℓ : Level} {P Q : 𝒫 ℓ} → Segment P Q →
  Initial (Successor.next P) Q
segment-closed {ℓ} {P} {Q} s =
  Successor.Into.closed P Q (Segment.bound s) (Segment.covers s)

inclusion : {ℓ : Level} {P Q : 𝒫 ℓ} → Segment P Q → Initial P Q
inclusion {ℓ} {P} {Q} s = record
  { map = Presented.Embedding.to (Segment.bound s)
  ; resp = Presented.Embedding.to-≈ (Segment.bound s)
  ; strict = Presented.Embedding.to-< (Segment.bound s)
  ; lower = λ x y p →
      Segment.covers s y
        (𝒫.<-trans Q p (Presented.Embedding.below (Segment.bound s) x))
  }

successor : {ℓ : Level} (P : 𝒫 ℓ) → Segment P (Successor.next P)
successor P = record
  { bound = Successor.strict P
  ; covers = λ { (point x) point<top → x , point≈ (𝒫.≈-refl P x) }
  }

module _ {ℓ : Level} {P Q R : 𝒫 ℓ} where

  along-cover : (e : Segment P Q) (f : Initial Q R) (y : 𝒫.X R) →
    𝒫._<_ R y
      (Initial.map f (Presented.Embedding.ceiling (Segment.bound e))) →
    Σ (𝒫.X P) (λ x →
      𝒫._≈_ R
        (Initial.map f (Presented.Embedding.to (Segment.bound e) x)) y)
  along-cover e f y p
    with Initial.lower f (Presented.Embedding.ceiling (Segment.bound e)) y p
  ... | z , q
    with Segment.covers e z
           (initial-reflect f (𝒫.<-respˡ-≈ R (𝒫.≈-sym R q) p))
  ... | x , r = x , 𝒫.≈-trans R (Initial.resp f r) q

  along : Segment P Q → Initial Q R → Segment P R
  along e f = record
    { bound = bounded (Segment.bound e) f ; covers = along-cover e f }
