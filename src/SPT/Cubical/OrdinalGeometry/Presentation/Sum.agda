{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Presentation.Sum where

-- The ordered sum P + Q of two presented countable ordinals: every point
-- of P precedes every point of Q. P enters by an initial map and Q by an
-- order embedding. Below a point y of Q, the predecessor domain of y in
-- P + Q receives P followed by the predecessor domain of y in Q. Also:
-- predecessor domains ∂x and their maps (narrowing to a smaller point,
-- nesting inside a larger one, the cone of a segment's ceiling), and the
-- successor P + 1 with its top and the extension of a cone map to it.

open import SPT.Cubical.Base hiding (_+_)
open import SPT.Cubical.Foundation.Accessibility using (acc; is-accessible)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Principal as Principal
import SPT.Cubical.OrdinalGeometry.Presentation.Successor as Adjoin

private
  variable
    ℓ : Level

  -- Even indices enumerate the left summand, odd indices the right one.
  parity : ℕ → ℕ ⊎ ℕ
  parity zero = inl zero
  parity (suc zero) = inr zero
  parity (suc (suc n)) = ⊎-map suc suc (parity n)

  even : ℕ → ℕ
  even zero = zero
  even (suc n) = suc (suc (even n))

  parity-even : (n : ℕ) → parity (even n) ＝ inl n
  parity-even zero = refl
  parity-even (suc n) = ap (⊎-map suc suc) (parity-even n)

  parity-odd : (n : ℕ) → parity (suc (even n)) ＝ inr n
  parity-odd zero = refl
  parity-odd (suc n) = ap (⊎-map suc suc) (parity-odd n)

------------------------------------------------------------------------
-- Predecessor domains

-- The predecessor domain Σ y. y < x of a point x.
∂ : (P : 𝒫 ℓ) → 𝒫.X P → 𝒫 ℓ
∂ P x = Principal.Segments.lower P x

-- The predecessor domain of x includes into P as the segment below x.
cone : (P : 𝒫 ℓ) (x : 𝒫.X P) → Maps.Segment (∂ P x) P
cone P x = record
  { bound = Principal.Segments.inclusion P x
  ; covers = λ y p → (y , p) , 𝒫.≈-refl P y
  }

-- Forgetting the strict witness includes ∂x into P.
inclusion : (P : 𝒫 ℓ) (x : 𝒫.X P) → Maps.Embedding (∂ P x) P
inclusion P x = Maps.Initial.embedding (Maps.inclusion (cone P x))

-- An order embedding restricts to the predecessor domains of a point and
-- of its image.
restrict : {P Q : 𝒫 ℓ} (f : Maps.Embedding P Q) (x : 𝒫.X P)
  → Maps.Embedding (∂ P x) (∂ Q (Maps.Embedding.map f x))
restrict f x = record
  { map = λ u →
      Maps.Embedding.map f (pr₁ u) , Maps.Embedding.strict f (pr₂ u)
  ; resp = Maps.Embedding.resp f
  ; strict = Maps.Embedding.strict f
  }

------------------------------------------------------------------------
-- The ordered sum

private
  module Construction (P Q : 𝒫 ℓ) where

    module P = 𝒫 P
    module Q = 𝒫 Q

    Carrier : Set ℓ
    Carrier = P.X ⊎ Q.X

    infix 6 _≈_
    infix 30 _<_

    _≈_ : Carrier → Carrier → Set ℓ
    inl x ≈ inl y = x P.≈ y
    inl x ≈ inr y = Lift ℓ 𝟘
    inr x ≈ inl y = Lift ℓ 𝟘
    inr x ≈ inr y = x Q.≈ y

    _<_ : Carrier → Carrier → Set ℓ
    inl x < inl y = x P.< y
    inl x < inr y = Lift ℓ 𝟙
    inr x < inl y = Lift ℓ 𝟘
    inr x < inr y = x Q.< y

    ≈-refl : (x : Carrier) → x ≈ x
    ≈-refl (inl x) = P.≈-refl x
    ≈-refl (inr x) = Q.≈-refl x

    ≈-sym : {x y : Carrier} → x ≈ y → y ≈ x
    ≈-sym {inl _} {inl _} p = P.≈-sym p
    ≈-sym {inl _} {inr _} ()
    ≈-sym {inr _} {inl _} ()
    ≈-sym {inr _} {inr _} p = Q.≈-sym p

    ≈-trans : {x y z : Carrier} → x ≈ y → y ≈ z → x ≈ z
    ≈-trans {inl _} {inl _} {inl _} p q = P.≈-trans p q
    ≈-trans {inl _} {inl _} {inr _} p ()
    ≈-trans {inl _} {inr _} () q
    ≈-trans {inr _} {inl _} () q
    ≈-trans {inr _} {inr _} {inl _} p ()
    ≈-trans {inr _} {inr _} {inr _} p q = Q.≈-trans p q

    <-trans : {x y z : Carrier} → x < y → y < z → x < z
    <-trans {inl _} {inl _} {inl _} p q = P.<-trans p q
    <-trans {inl _} {inl _} {inr _} p q = (lift ⋆)
    <-trans {inl _} {inr _} {inl _} p ()
    <-trans {inl _} {inr _} {inr _} p q = (lift ⋆)
    <-trans {inr _} {inl _} () q
    <-trans {inr _} {inr _} {inl _} p ()
    <-trans {inr _} {inr _} {inr _} p q = Q.<-trans p q

    <-respˡ : {x x′ y : Carrier} → x ≈ x′ → x < y → x′ < y
    <-respˡ {inl _} {inl _} {inl _} p q = P.<-respˡ-≈ p q
    <-respˡ {inl _} {inl _} {inr _} p q = (lift ⋆)
    <-respˡ {inl _} {inr _} () q
    <-respˡ {inr _} {inl _} () q
    <-respˡ {inr _} {inr _} {inl _} p ()
    <-respˡ {inr _} {inr _} {inr _} p q = Q.<-respˡ-≈ p q

    <-respʳ : {x y y′ : Carrier} → y ≈ y′ → x < y → x < y′
    <-respʳ {inl _} {inl _} {inl _} p q = P.<-respʳ-≈ p q
    <-respʳ {inl _} {inl _} {inr _} () q
    <-respʳ {inl _} {inr _} {inl _} () q
    <-respʳ {inl _} {inr _} {inr _} p q = (lift ⋆)
    <-respʳ {inr _} {inl _} p ()
    <-respʳ {inr _} {inr _} {inl _} () q
    <-respʳ {inr _} {inr _} {inr _} p q = Q.<-respʳ-≈ p q

    left-acc : (x : P.X) → is-accessible P._<_ x → is-accessible _<_ (inl x)
    left-acc x (acc smaller) = acc λ where
      (inl y) p → left-acc y (smaller y p)
      (inr y) ()

    right-acc : (y : Q.X) → is-accessible Q._<_ y → is-accessible _<_ (inr y)
    right-acc y (acc smaller) = acc λ where
      (inl x) p → left-acc x (P.<-wf x)
      (inr z) p → right-acc z (smaller z p)

    well-founded : (x : Carrier) → is-accessible _<_ x
    well-founded (inl x) = left-acc x (P.<-wf x)
    well-founded (inr y) = right-acc y (Q.<-wf y)

    compare : (x y : Carrier) → x < y ⊎ ((x ≈ y) ⊎ y < x)
    compare (inl x) (inl y) = P.compare x y
    compare (inl x) (inr y) = inl (lift ⋆)
    compare (inr x) (inl y) = inr (inr (lift ⋆))
    compare (inr x) (inr y) = Q.compare x y

    pick : ℕ ⊎ ℕ → Maybe Carrier
    pick (inl n) = maybe-map inl (P.enum n)
    pick (inr n) = maybe-map inr (Q.enum n)

    enum : ℕ → Maybe Carrier
    enum n = pick (parity n)

    covers : (x : Carrier)
      → Σ ℕ λ n → Σ Carrier λ r → (enum n ＝ just r) × (r ≈ x)
    covers (inl x) with P.covers x
    ... | n , r , p , q = even n , inl r ,
      ap pick (parity-even n) ∙ ap (maybe-map inl) p , q
    covers (inr y) with Q.covers y
    ... | n , r , p , q = suc (even n) , inr r ,
      ap pick (parity-odd n) ∙ ap (maybe-map inr) p , q

    presentation : 𝒫 ℓ
    presentation = record
      { X = Carrier
      ; _≈_ = _≈_
      ; _<_ = _<_
      ; ≈-refl = ≈-refl
      ; ≈-sym = λ {x} {y} → ≈-sym {x} {y}
      ; ≈-trans = λ {x} {y} {z} → ≈-trans {x} {y} {z}
      ; <-trans = λ {x} {y} {z} → <-trans {x} {y} {z}
      ; <-respˡ-≈ = λ {x} {x′} {y} → <-respˡ {x} {x′} {y}
      ; <-respʳ-≈ = λ {x} {y} {y′} → <-respʳ {x} {y} {y′}
      ; <-wf = well-founded
      ; compare = compare
      ; enum = enum
      ; covers = covers
      }

infixl 35 _+_

-- Mathematical shape: P + Q, with carrier |P| ⊎ |Q|, each summand ordered
-- as before, and inl x < inr y for all x and y.
_+_ : 𝒫 ℓ → 𝒫 ℓ → 𝒫 ℓ
P + Q = Construction.presentation P Q

carrier-β : (P Q : 𝒫 ℓ) → 𝒫.X (P + Q) ＝ (𝒫.X P ⊎ 𝒫.X Q)
carrier-β P Q = refl

-- P is an initial part of P + Q.
left : (P Q : 𝒫 ℓ) → Maps.Initial P (P + Q)
left P Q = record
  { map = inl
  ; resp = λ p → p
  ; strict = λ p → p
  ; lower = λ where
      x (inl y) p → y , 𝒫.≈-refl P y
      x (inr y) ()
  }

-- Q follows P inside P + Q.
right : (P Q : 𝒫 ℓ) → Maps.Embedding Q (P + Q)
right P Q = record { map = inr ; resp = λ p → p ; strict = λ p → p }

-- Below a right point y, P + Q has P followed by the predecessors of y:
--
--   P + ∂_Q(y) → ∂_{P+Q}(inr y).
below : (P Q : 𝒫 ℓ) (y : 𝒫.X Q)
  → Maps.Embedding (P + ∂ Q y) (∂ (P + Q) (inr y))
below P Q y = record
  { map = λ where
      (inl x) → inl x , (lift ⋆)
      (inr u) → inr (pr₁ u) , pr₂ u
  ; resp = λ where
      {inl _} {inl _} p → p
      {inl _} {inr _} ()
      {inr _} {inl _} ()
      {inr _} {inr _} p → p
  ; strict = λ where
      {inl _} {inl _} p → p
      {inl _} {inr _} p → (lift ⋆)
      {inr _} {inl _} ()
      {inr _} {inr _} p → p
  }

-- P sits below every right point of P + Q.
under : (P Q : 𝒫 ℓ) (y : 𝒫.X Q)
  → Maps.Embedding P (∂ (P + Q) (inr y))
under P Q y = Maps.composite
  (Maps.Initial.embedding (left P (∂ Q y))) (below P Q y)

-- Two order embeddings act on both summands.
map : {P P′ Q Q′ : 𝒫 ℓ}
  → Maps.Embedding P P′ → Maps.Embedding Q Q′
  → Maps.Embedding (P + Q) (P′ + Q′)
map f g = record
  { map = λ where
      (inl x) → inl (Maps.Embedding.map f x)
      (inr y) → inr (Maps.Embedding.map g y)
  ; resp = λ where
      {inl _} {inl _} p → Maps.Embedding.resp f p
      {inl _} {inr _} ()
      {inr _} {inl _} ()
      {inr _} {inr _} p → Maps.Embedding.resp g p
  ; strict = λ where
      {inl _} {inl _} p → Maps.Embedding.strict f p
      {inl _} {inr _} p → (lift ⋆)
      {inr _} {inl _} ()
      {inr _} {inr _} p → Maps.Embedding.strict g p
  }

------------------------------------------------------------------------
-- Cones below points

-- A proper segment P ⊂ Q lies in the predecessor domain of its ceiling.
ceiling-cone : {P Q : 𝒫 ℓ} (s : Maps.Segment P Q)
  → Maps.Embedding P
      (∂ Q (Presented._≺𝒫_.ceiling (Maps.Segment.bound s)))
ceiling-cone s = record
  { map = λ x → Bound.to x , Bound.below x
  ; resp = Bound.to-≈
  ; strict = Bound.to-<
  }
  where
  module Bound = Presented._≺𝒫_ (Maps.Segment.bound s)

-- A smaller point has a smaller predecessor domain.
narrow : (Q : 𝒫 ℓ) {a b : 𝒫.X Q} → 𝒫._<_ Q b a
  → Maps.Embedding (∂ Q b) (∂ Q a)
narrow Q p = record
  { map = λ u → pr₁ u , 𝒫.<-trans Q (pr₂ u) p
  ; resp = λ q → q
  ; strict = λ q → q
  }

-- The predecessors of b < a, read inside the predecessor domain of a.
nest : (Q : 𝒫 ℓ) {a b : 𝒫.X Q} (p : 𝒫._<_ Q b a)
  → Maps.Embedding (∂ Q b) (∂ (∂ Q a) (b , p))
nest Q p = record
  { map = λ u → (pr₁ u , 𝒫.<-trans Q (pr₂ u) p) , pr₂ u
  ; resp = λ q → q
  ; strict = λ q → q
  }

------------------------------------------------------------------------
-- Successors

-- P + 1, with its new top point.
next : 𝒫 ℓ → 𝒫 ℓ
next = Maps.Successor.next

top : (P : 𝒫 ℓ) → 𝒫.X (next P)
top P = Presented._≺𝒫_.ceiling (Maps.Segment.bound (Maps.successor P))

-- P is the predecessor domain of the top of P + 1.
beneath : (P : 𝒫 ℓ) → Maps.Embedding P (∂ (next P) (top P))
beneath P = ceiling-cone (Maps.successor P)

-- P is an initial part of P + 1.
onward : (P : 𝒫 ℓ) → Maps.Embedding P (next P)
onward P = Maps.Initial.embedding (Maps.Successor.initial P)

-- An embedding of P below a point c of Q extends to P + 1, the top
-- landing on c.
cap : {P Q : 𝒫 ℓ} (c : 𝒫.X Q) → Maps.Embedding P (∂ Q c)
  → Maps.Embedding (next P) Q
cap {P = P} {Q} c f = record
  { map = image
  ; resp = λ {x} {y} → resp {x} {y}
  ; strict = λ {x} {y} → strict {x} {y}
  }
  where
  module Entry = Presented.Diagonal.Successor
    (Adjoin.constant P) zero

  image : Entry.Entry → 𝒫.X Q
  image (Entry.point x) = pr₁ (Maps.Embedding.map f x)
  image Entry.top = c

  resp : {x y : Entry.Entry} → x Entry.≈ y
    → 𝒫._≈_ Q (image x) (image y)
  resp (Entry.point≈ p) = Maps.Embedding.resp f p
  resp Entry.top≈ = 𝒫.≈-refl Q c

  strict : {x y : Entry.Entry} → x Entry.< y
    → 𝒫._<_ Q (image x) (image y)
  strict (Entry.point< p) = Maps.Embedding.strict f p
  strict Entry.point<top = pr₂ (Maps.Embedding.map f _)

-- The successor acts on order embeddings, top to top.
next-map : {P Q : 𝒫 ℓ} → Maps.Embedding P Q
  → Maps.Embedding (next P) (next Q)
next-map {Q = Q} f = cap (top Q) (Maps.composite f (beneath Q))
