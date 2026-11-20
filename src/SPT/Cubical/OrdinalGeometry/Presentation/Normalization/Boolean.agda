{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Presentation.Normalization.Boolean
  where

-- Every presentation, at every level, is equivalent to the presentation
-- of a Boolean order (normal, equivalence).  Its points are the least
-- enumeration indices of the classes of P (Normalization.Point), a
-- decidable set of natural numbers, and its order is the strict order of
-- their representatives, decided by the comparison of P.  So the small
-- type of Boolean orders presents every countable ordinal of every level.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Accessibility using
  ( acc; is-accessible; is-well-founded )
open import SPT.Cubical.Foundation.Two.Decisions using
  (bit-gives-witness; decision-bit; witness-gives-bit)
open import SPT.Cubical.Foundation.Two.Truth using (is-₁)

import SPT.Cubical.Foundation.Nat.FirstSuccess as Search
open Search.Sequence using (Hit; value; decide; hit-proposition)
import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
open 𝒫
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization as Normalization
open Normalization using
  (Point; Strict; class; representative; code)
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization.Presentation
  as Normalized
import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order
open import SPT.Cubical.OrdinalGeometry.ExactOrder.Boolean using
  (BooleanOrder; Points; order; point-≡)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- Indices of points

-- n is an index of P when n is the least enumeration index of the class
-- of the value enumerated at n.
Index : (P : 𝒫 ℓ) → ℕ → Set
Index P n =
  Σ (Hit (enum P) n) λ h → code P (value (enum P) n h) ＝ n

pointOf : (P : 𝒫 ℓ) {n : ℕ} → Index P n → Point P
pointOf P {n} (h , p) = (n , h) , p

index? : (P : 𝒫 ℓ) (n : ℕ) → is-decidable (Index P n)
index? P n with decide (enum P) n
... | inr miss = inr λ i → miss (pr₁ i)
... | inl h with ℕ-has-decidable-equality (code P (value (enum P) n h)) n
...   | inl p = inl (h , p)
...   | inr q = inr λ i → q
  (transport (λ k → code P (value (enum P) n k) ＝ n)
    (hit-proposition (enum P) n (pr₁ i) h) (pr₂ i))

private
  -- Two witnesses of one index give the same point.
  pointOf-≡ : (P : 𝒫 ℓ) {n : ℕ} (a b : Index P n)
    → pointOf P a ＝ pointOf P b
  pointOf-≡ P a b = Normalization.equal P refl

  -- The strict order of points, decided by the comparison of P.
  -- The comparison is consumed as an argument: Strict P a b itself
  -- mentions the comparison, so a `with` on it would rewrite the goal.
  strict? : (P : 𝒫 ℓ) (a b : Point P) → is-decidable (Strict P a b)
  strict? P a b =
    decision (compare P (representative P a) (representative P b))
    where
      x = representative P a
      y = representative P b

      decision : _<_ P x y ⊎ (_≈_ P x y ⊎ _<_ P y x) →
        is-decidable (Strict P a b)
      decision (inl p) =
        inl (Normalization.representative-reflect P {a} {b} p)
      decision (inr (inl e)) = inr λ s → Presented.Presentation.≈↛< P e
        (Normalization.representative-strict P {a} {b} s)
      decision (inr (inr p)) = inr λ s → Presented.Presentation.<-asym P p
        (Normalization.representative-strict P {a} {b} s)

  lessAt : (P : 𝒫 ℓ) {i j : ℕ}
    → is-decidable (Index P i) → is-decidable (Index P j) → 𝟚
  lessAt P (inl a) (inl b) =
    decision-bit (strict? P (pointOf P a) (pointOf P b))
  lessAt P (inl a) (inr _) = ₀
  lessAt P (inr _) _ = ₀

  lessAt-sound : (P : 𝒫 ℓ) {i j : ℕ}
    (d : is-decidable (Index P i)) (e : is-decidable (Index P j))
    → is-₁ (lessAt P d e)
    → Σ (Index P i) λ a → Σ (Index P j) λ b →
        Strict P (pointOf P a) (pointOf P b)
  lessAt-sound P (inl a) (inl b) t =
    a , b , bit-gives-witness (strict? P (pointOf P a) (pointOf P b)) t
  lessAt-sound P (inl a) (inr _) ()
  lessAt-sound P (inr _) _ ()

  lessAt-complete : (P : 𝒫 ℓ) {i j : ℕ} (a : Index P i) (b : Index P j)
    → Strict P (pointOf P a) (pointOf P b)
    → (d : is-decidable (Index P i)) (e : is-decidable (Index P j))
    → is-₁ (lessAt P d e)
  lessAt-complete P a b s (inl a′) (inl b′) =
    witness-gives-bit (strict? P (pointOf P a′) (pointOf P b′))
      (transport₂ (Strict P) (pointOf-≡ P a a′) (pointOf-≡ P b b′) s)
  lessAt-complete P a b s (inl a′) (inr not-b) = not-b b
  lessAt-complete P a b s (inr not-a) _ = not-a a

------------------------------------------------------------------------
-- The Boolean order of a presentation

point : (P : 𝒫 ℓ) → ℕ → 𝟚
point P n = decision-bit (index? P n)

less : (P : 𝒫 ℓ) → ℕ → ℕ → 𝟚
less P i j = lessAt P (index? P i) (index? P j)

private
  less-sound : (P : 𝒫 ℓ) {i j : ℕ} → is-₁ (less P i j)
    → Σ (Index P i) λ a → Σ (Index P j) λ b →
        Strict P (pointOf P a) (pointOf P b)
  less-sound P {i} {j} = lessAt-sound P (index? P i) (index? P j)

  less-complete : (P : 𝒫 ℓ) {i j : ℕ} (a : Index P i) (b : Index P j)
    → Strict P (pointOf P a) (pointOf P b) → is-₁ (less P i j)
  less-complete P {i} {j} a b s =
    lessAt-complete P a b s (index? P i) (index? P j)

  less-trans : (P : 𝒫 ℓ) {i j k : ℕ}
    → is-₁ (less P i j) → is-₁ (less P j k) → is-₁ (less P i k)
  less-trans P {i} {j} {k} p q =
    let (a , b , s) = less-sound P {i} {j} p
        (b′ , c , s′) = less-sound P {j} {k} q
    in less-complete P a c
      (Order.Order.trans (Normalization.order P)
        {pointOf P a} {pointOf P b} {pointOf P c} s
        (transport (λ x → Strict P x (pointOf P c)) (pointOf-≡ P b′ b) s′))

  -- Accessibility of a point carries over to its index; indices of
  -- non-points have no predecessors.
  accessible : (P : 𝒫 ℓ) (c : Point P) → is-accessible (Strict P) c
    → (i : ℕ) (a : Index P i) → pointOf P a ＝ c
    → is-accessible (λ i j → is-₁ (less P i j)) i
  accessible P c (acc smaller) i a e = acc λ j t →
    let (b , a′ , s) = less-sound P {j} {i} t
    in accessible P (pointOf P b)
      (smaller (pointOf P b)
        (transport (Strict P (pointOf P b)) (pointOf-≡ P a′ a ∙ e) s))
      j b refl

  less-wf : (P : 𝒫 ℓ) → is-well-founded (λ i j → is-₁ (less P i j))
  less-wf P i = from (index? P i)
    where
      from : is-decidable (Index P i) →
        is-accessible (λ i j → is-₁ (less P i j)) i
      from (inl a) =
        accessible P (pointOf P a)
          (Order.Order.wf (Normalization.order P) (pointOf P a)) i a refl
      from (inr not-a) = acc λ j t → 𝟘-elim (not-a (pr₁ (pr₂
        (less-sound P {j} {i} t))))

  less-compare : (P : 𝒫 ℓ) (i j : ℕ) → is-₁ (point P i) → is-₁ (point P j)
    → is-₁ (less P i j) ⊎ ((i ＝ j) ⊎ is-₁ (less P j i))
  less-compare P i j s t =
    compareAt (bit-gives-witness (index? P i) s)
      (bit-gives-witness (index? P j) t)
    where
      compareAt : Index P i → Index P j
        → is-₁ (less P i j) ⊎ ((i ＝ j) ⊎ is-₁ (less P j i))
      compareAt a b
          with Order.Order.compare (Normalization.order P)
            (pointOf P a) (pointOf P b)
      ... | inl p = inl (less-complete P a b p)
      ... | inr (inl e) = inr (inl (ap (Normalization.index P) e))
      ... | inr (inr p) = inr (inr (less-complete P b a p))

-- Mathematical shape: normal(P) = (index?_P , less_P), where less_P i j
-- holds when i and j are indices whose points are strictly ordered.
normal : 𝒫 ℓ → BooleanOrder
normal P = record
  { point = point P
  ; less = less P
  ; trans = less-trans P
  ; wf = less-wf P
  ; compare = less-compare P
  }

------------------------------------------------------------------------
-- P is equivalent to the presentation of its Boolean order

private
  embed : (P : 𝒫 ℓ) → Point P → Points (normal P)
  embed P ((n , h) , p) = n , witness-gives-bit (index? P n) (h , p)

  -- The index witnessed by a point of the Boolean order.
  witness : (P : 𝒫 ℓ) (a : Points (normal P)) → Index P (pr₁ a)
  witness P a = bit-gives-witness (index? P (pr₁ a)) (pr₂ a)

  retrieve : (P : 𝒫 ℓ) → Points (normal P) → Point P
  retrieve P a = pointOf P (witness P a)

  retrieve-embed : (P : 𝒫 ℓ) (c : Point P) → retrieve P (embed P c) ＝ c
  retrieve-embed P c = Normalization.equal P refl

  embed-retrieve : (P : 𝒫 ℓ) (a : Points (normal P))
    → embed P (retrieve P a) ＝ a
  embed-retrieve P a = point-≡ (normal P) refl

  -- The index of the class of x, as a witness for its point.
  indexOf : (P : 𝒫 ℓ) (x : X P) → Index P (code P x)
  indexOf P x = pr₂ (pr₁ (class P x)) , pr₂ (class P x)

-- Mathematical shape: P ≃𝒫 presentation(normal P), with
--
--   to x = class index of x,   from n = representative at n.
equivalence : (P : 𝒫 ℓ)
  → P Presented.≃𝒫 Normalized.presentation (order (normal P))
equivalence P = record
  { to = λ x → lift (embed P (class P x))
  ; from = λ a → representative P (retrieve P (lower a))
  ; to-≈ = λ p → lift (ap (embed P) (Normalization.class-resp P p))
  ; from-≈ = λ {a} {b} e →
      transport
        (λ c → _≈_ P (representative P (retrieve P (lower a)))
          (representative P (retrieve P c)))
        (lower e)
        (≈-refl P _)
  ; to-< = λ {x} {y} p → lift
      (less-complete P (indexOf P x) (indexOf P y)
        (Normalization.class-strict P p))
  ; from-< = λ {a} {b} p →
      let (a′ , b′ , s) = less-sound P (lower p)
      in Normalization.representative-strict P
        {retrieve P (lower a)} {retrieve P (lower b)}
        (transport₂ (Strict P)
          (pointOf-≡ P a′ (witness P (lower a)))
          (pointOf-≡ P b′ (witness P (lower b)))
          s)
  ; from-to-≈ = λ x →
      transport (λ c → _≈_ P (representative P c) x)
        (retrieve-embed P (class P x) ⁻¹)
        (Normalization.representative-class P x)
  ; to-from-≈ = λ a → lift
      (
        (ap (embed P)
          (Normalization.class-representative P (retrieve P (lower a))))
        ∙ embed-retrieve P (lower a))
  }
