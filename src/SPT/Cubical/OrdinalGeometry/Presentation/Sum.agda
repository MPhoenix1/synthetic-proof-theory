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

open import Agda.Primitive using (Level)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Maybe using (Maybe; just)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Sum as Sum
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; trans)

open import SPT.Cubical.Core.WellFounded using (Acc; acc)
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
  parity zero = inj₁ zero
  parity (suc zero) = inj₂ zero
  parity (suc (suc n)) = Sum.map suc suc (parity n)

  even : ℕ → ℕ
  even zero = zero
  even (suc n) = suc (suc (even n))

  parity-even : (n : ℕ) → parity (even n) ≡ inj₁ n
  parity-even zero = refl
  parity-even (suc n) = cong (Sum.map suc suc) (parity-even n)

  parity-odd : (n : ℕ) → parity (suc (even n)) ≡ inj₂ n
  parity-odd zero = refl
  parity-odd (suc n) = cong (Sum.map suc suc) (parity-odd n)

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
      Maps.Embedding.map f (proj₁ u) , Maps.Embedding.strict f (proj₂ u)
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

    infix 4 _≈_ _<_

    _≈_ : Carrier → Carrier → Set ℓ
    inj₁ x ≈ inj₁ y = x P.≈ y
    inj₁ x ≈ inj₂ y = ⊥
    inj₂ x ≈ inj₁ y = ⊥
    inj₂ x ≈ inj₂ y = x Q.≈ y

    _<_ : Carrier → Carrier → Set ℓ
    inj₁ x < inj₁ y = x P.< y
    inj₁ x < inj₂ y = ⊤
    inj₂ x < inj₁ y = ⊥
    inj₂ x < inj₂ y = x Q.< y

    ≈-refl : (x : Carrier) → x ≈ x
    ≈-refl (inj₁ x) = P.≈-refl x
    ≈-refl (inj₂ x) = Q.≈-refl x

    ≈-sym : {x y : Carrier} → x ≈ y → y ≈ x
    ≈-sym {inj₁ _} {inj₁ _} p = P.≈-sym p
    ≈-sym {inj₁ _} {inj₂ _} ()
    ≈-sym {inj₂ _} {inj₁ _} ()
    ≈-sym {inj₂ _} {inj₂ _} p = Q.≈-sym p

    ≈-trans : {x y z : Carrier} → x ≈ y → y ≈ z → x ≈ z
    ≈-trans {inj₁ _} {inj₁ _} {inj₁ _} p q = P.≈-trans p q
    ≈-trans {inj₁ _} {inj₁ _} {inj₂ _} p ()
    ≈-trans {inj₁ _} {inj₂ _} () q
    ≈-trans {inj₂ _} {inj₁ _} () q
    ≈-trans {inj₂ _} {inj₂ _} {inj₁ _} p ()
    ≈-trans {inj₂ _} {inj₂ _} {inj₂ _} p q = Q.≈-trans p q

    <-trans : {x y z : Carrier} → x < y → y < z → x < z
    <-trans {inj₁ _} {inj₁ _} {inj₁ _} p q = P.<-trans p q
    <-trans {inj₁ _} {inj₁ _} {inj₂ _} p q = tt
    <-trans {inj₁ _} {inj₂ _} {inj₁ _} p ()
    <-trans {inj₁ _} {inj₂ _} {inj₂ _} p q = tt
    <-trans {inj₂ _} {inj₁ _} () q
    <-trans {inj₂ _} {inj₂ _} {inj₁ _} p ()
    <-trans {inj₂ _} {inj₂ _} {inj₂ _} p q = Q.<-trans p q

    <-respˡ : {x x′ y : Carrier} → x ≈ x′ → x < y → x′ < y
    <-respˡ {inj₁ _} {inj₁ _} {inj₁ _} p q = P.<-respˡ-≈ p q
    <-respˡ {inj₁ _} {inj₁ _} {inj₂ _} p q = tt
    <-respˡ {inj₁ _} {inj₂ _} () q
    <-respˡ {inj₂ _} {inj₁ _} () q
    <-respˡ {inj₂ _} {inj₂ _} {inj₁ _} p ()
    <-respˡ {inj₂ _} {inj₂ _} {inj₂ _} p q = Q.<-respˡ-≈ p q

    <-respʳ : {x y y′ : Carrier} → y ≈ y′ → x < y → x < y′
    <-respʳ {inj₁ _} {inj₁ _} {inj₁ _} p q = P.<-respʳ-≈ p q
    <-respʳ {inj₁ _} {inj₁ _} {inj₂ _} () q
    <-respʳ {inj₁ _} {inj₂ _} {inj₁ _} () q
    <-respʳ {inj₁ _} {inj₂ _} {inj₂ _} p q = tt
    <-respʳ {inj₂ _} {inj₁ _} p ()
    <-respʳ {inj₂ _} {inj₂ _} {inj₁ _} () q
    <-respʳ {inj₂ _} {inj₂ _} {inj₂ _} p q = Q.<-respʳ-≈ p q

    left-acc : (x : P.X) → Acc P._<_ x → Acc _<_ (inj₁ x)
    left-acc x (acc smaller) = acc λ where
      (inj₁ y) p → left-acc y (smaller y p)
      (inj₂ y) ()

    right-acc : (y : Q.X) → Acc Q._<_ y → Acc _<_ (inj₂ y)
    right-acc y (acc smaller) = acc λ where
      (inj₁ x) p → left-acc x (P.<-wf x)
      (inj₂ z) p → right-acc z (smaller z p)

    well-founded : (x : Carrier) → Acc _<_ x
    well-founded (inj₁ x) = left-acc x (P.<-wf x)
    well-founded (inj₂ y) = right-acc y (Q.<-wf y)

    compare : (x y : Carrier) → x < y ⊎ (x ≈ y ⊎ y < x)
    compare (inj₁ x) (inj₁ y) = P.compare x y
    compare (inj₁ x) (inj₂ y) = inj₁ tt
    compare (inj₂ x) (inj₁ y) = inj₂ (inj₂ tt)
    compare (inj₂ x) (inj₂ y) = Q.compare x y

    pick : ℕ ⊎ ℕ → Maybe Carrier
    pick (inj₁ n) = Maybe.map inj₁ (P.enum n)
    pick (inj₂ n) = Maybe.map inj₂ (Q.enum n)

    enum : ℕ → Maybe Carrier
    enum n = pick (parity n)

    covers : (x : Carrier)
      → Σ ℕ λ n → Σ Carrier λ r → (enum n ≡ just r) × (r ≈ x)
    covers (inj₁ x) with P.covers x
    ... | n , r , p , q = even n , inj₁ r ,
      trans (cong pick (parity-even n)) (cong (Maybe.map inj₁) p) , q
    covers (inj₂ y) with Q.covers y
    ... | n , r , p , q = suc (even n) , inj₂ r ,
      trans (cong pick (parity-odd n)) (cong (Maybe.map inj₂) p) , q

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

infixl 6 _+_

-- Mathematical shape: P + Q, with carrier |P| ⊎ |Q|, each summand ordered
-- as before, and inl x < inr y for all x and y.
_+_ : 𝒫 ℓ → 𝒫 ℓ → 𝒫 ℓ
P + Q = Construction.presentation P Q

carrier-β : (P Q : 𝒫 ℓ) → 𝒫.X (P + Q) ≡ (𝒫.X P ⊎ 𝒫.X Q)
carrier-β P Q = refl

-- P is an initial part of P + Q.
left : (P Q : 𝒫 ℓ) → Maps.Initial P (P + Q)
left P Q = record
  { map = inj₁
  ; resp = λ p → p
  ; strict = λ p → p
  ; lower = λ where
      x (inj₁ y) p → y , 𝒫.≈-refl P y
      x (inj₂ y) ()
  }

-- Q follows P inside P + Q.
right : (P Q : 𝒫 ℓ) → Maps.Embedding Q (P + Q)
right P Q = record { map = inj₂ ; resp = λ p → p ; strict = λ p → p }

-- Below a right point y, P + Q has P followed by the predecessors of y:
--
--   P + ∂_Q(y) → ∂_{P+Q}(inr y).
below : (P Q : 𝒫 ℓ) (y : 𝒫.X Q)
  → Maps.Embedding (P + ∂ Q y) (∂ (P + Q) (inj₂ y))
below P Q y = record
  { map = λ where
      (inj₁ x) → inj₁ x , tt
      (inj₂ u) → inj₂ (proj₁ u) , proj₂ u
  ; resp = λ where
      {inj₁ _} {inj₁ _} p → p
      {inj₁ _} {inj₂ _} ()
      {inj₂ _} {inj₁ _} ()
      {inj₂ _} {inj₂ _} p → p
  ; strict = λ where
      {inj₁ _} {inj₁ _} p → p
      {inj₁ _} {inj₂ _} p → tt
      {inj₂ _} {inj₁ _} ()
      {inj₂ _} {inj₂ _} p → p
  }

-- P sits below every right point of P + Q.
under : (P Q : 𝒫 ℓ) (y : 𝒫.X Q)
  → Maps.Embedding P (∂ (P + Q) (inj₂ y))
under P Q y = Maps.composite
  (Maps.Initial.embedding (left P (∂ Q y))) (below P Q y)

-- Two order embeddings act on both summands.
map : {P P′ Q Q′ : 𝒫 ℓ}
  → Maps.Embedding P P′ → Maps.Embedding Q Q′
  → Maps.Embedding (P + Q) (P′ + Q′)
map f g = record
  { map = λ where
      (inj₁ x) → inj₁ (Maps.Embedding.map f x)
      (inj₂ y) → inj₂ (Maps.Embedding.map g y)
  ; resp = λ where
      {inj₁ _} {inj₁ _} p → Maps.Embedding.resp f p
      {inj₁ _} {inj₂ _} ()
      {inj₂ _} {inj₁ _} ()
      {inj₂ _} {inj₂ _} p → Maps.Embedding.resp g p
  ; strict = λ where
      {inj₁ _} {inj₁ _} p → Maps.Embedding.strict f p
      {inj₁ _} {inj₂ _} p → tt
      {inj₂ _} {inj₁ _} ()
      {inj₂ _} {inj₂ _} p → Maps.Embedding.strict g p
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
  { map = λ u → proj₁ u , 𝒫.<-trans Q (proj₂ u) p
  ; resp = λ q → q
  ; strict = λ q → q
  }

-- The predecessors of b < a, read inside the predecessor domain of a.
nest : (Q : 𝒫 ℓ) {a b : 𝒫.X Q} (p : 𝒫._<_ Q b a)
  → Maps.Embedding (∂ Q b) (∂ (∂ Q a) (b , p))
nest Q p = record
  { map = λ u → (proj₁ u , 𝒫.<-trans Q (proj₂ u) p) , proj₂ u
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
  image (Entry.point x) = proj₁ (Maps.Embedding.map f x)
  image Entry.top = c

  resp : {x y : Entry.Entry} → x Entry.≈ y
    → 𝒫._≈_ Q (image x) (image y)
  resp (Entry.point≈ p) = Maps.Embedding.resp f p
  resp Entry.top≈ = 𝒫.≈-refl Q c

  strict : {x y : Entry.Entry} → x Entry.< y
    → 𝒫._<_ Q (image x) (image y)
  strict (Entry.point< p) = Maps.Embedding.strict f p
  strict Entry.point<top = proj₂ (Maps.Embedding.map f _)

-- The successor acts on order embeddings, top to top.
next-map : {P Q : 𝒫 ℓ} → Maps.Embedding P Q
  → Maps.Embedding (next P) (next Q)
next-map {Q = Q} f = cap (top Q) (Maps.composite f (beneath Q))
