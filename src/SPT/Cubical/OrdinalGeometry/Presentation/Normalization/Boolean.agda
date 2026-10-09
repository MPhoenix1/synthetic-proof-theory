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

open import Agda.Primitive using (Level)
open import Data.Bool.Base using (Bool; false; T)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (isYes; toWitness; fromWitness)

open import SPT.Cubical.Core.WellFounded using (Acc; acc; WellFounded)
import SPT.Cubical.Core.Nat.FirstSuccess as Search
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
  Σ (Hit (enum P) n) λ h → code P (value (enum P) n h) ≡ n

pointOf : (P : 𝒫 ℓ) {n : ℕ} → Index P n → Point P
pointOf P {n} (h , p) = (n , h) , p

index? : (P : 𝒫 ℓ) (n : ℕ) → Dec (Index P n)
index? P n with decide (enum P) n
... | no miss = no λ i → miss (proj₁ i)
... | yes h with code P (value (enum P) n h) ≟ n
...   | yes p = yes (h , p)
...   | no q = no λ i → q
  (subst (λ k → code P (value (enum P) n k) ≡ n)
    (hit-proposition (enum P) n (proj₁ i) h) (proj₂ i))

private
  -- Two witnesses of one index give the same point.
  pointOf-≡ : (P : 𝒫 ℓ) {n : ℕ} (a b : Index P n)
    → pointOf P a ≡ pointOf P b
  pointOf-≡ P a b = Normalization.equal P refl

  -- The strict order of points, decided by the comparison of P.
  -- The comparison is consumed as an argument: Strict P a b itself
  -- mentions the comparison, so a `with` on it would rewrite the goal.
  strict? : (P : 𝒫 ℓ) (a b : Point P) → Dec (Strict P a b)
  strict? P a b =
    decision (compare P (representative P a) (representative P b))
    where
      x = representative P a
      y = representative P b

      decision : _<_ P x y ⊎ (_≈_ P x y ⊎ _<_ P y x) → Dec (Strict P a b)
      decision (inj₁ p) =
        yes (Normalization.representative-reflect P {a} {b} p)
      decision (inj₂ (inj₁ e)) = no λ s → Presented.Presentation.≈↛< P e
        (Normalization.representative-strict P {a} {b} s)
      decision (inj₂ (inj₂ p)) = no λ s → Presented.Presentation.<-asym P p
        (Normalization.representative-strict P {a} {b} s)

  lessAt : (P : 𝒫 ℓ) {i j : ℕ}
    → Dec (Index P i) → Dec (Index P j) → Bool
  lessAt P (yes a) (yes b) = isYes (strict? P (pointOf P a) (pointOf P b))
  lessAt P (yes a) (no _) = false
  lessAt P (no _) _ = false

  lessAt-sound : (P : 𝒫 ℓ) {i j : ℕ}
    (d : Dec (Index P i)) (e : Dec (Index P j))
    → T (lessAt P d e)
    → Σ (Index P i) λ a → Σ (Index P j) λ b →
        Strict P (pointOf P a) (pointOf P b)
  lessAt-sound P (yes a) (yes b) t = a , b , toWitness t
  lessAt-sound P (yes a) (no _) ()
  lessAt-sound P (no _) _ ()

  lessAt-complete : (P : 𝒫 ℓ) {i j : ℕ} (a : Index P i) (b : Index P j)
    → Strict P (pointOf P a) (pointOf P b)
    → (d : Dec (Index P i)) (e : Dec (Index P j))
    → T (lessAt P d e)
  lessAt-complete P a b s (yes a′) (yes b′) =
    fromWitness (subst₂ (Strict P) (pointOf-≡ P a a′) (pointOf-≡ P b b′) s)
  lessAt-complete P a b s (yes a′) (no not-b) = not-b b
  lessAt-complete P a b s (no not-a) _ = not-a a

------------------------------------------------------------------------
-- The Boolean order of a presentation

point : (P : 𝒫 ℓ) → ℕ → Bool
point P n = isYes (index? P n)

less : (P : 𝒫 ℓ) → ℕ → ℕ → Bool
less P i j = lessAt P (index? P i) (index? P j)

private
  less-sound : (P : 𝒫 ℓ) {i j : ℕ} → T (less P i j)
    → Σ (Index P i) λ a → Σ (Index P j) λ b →
        Strict P (pointOf P a) (pointOf P b)
  less-sound P {i} {j} = lessAt-sound P (index? P i) (index? P j)

  less-complete : (P : 𝒫 ℓ) {i j : ℕ} (a : Index P i) (b : Index P j)
    → Strict P (pointOf P a) (pointOf P b) → T (less P i j)
  less-complete P {i} {j} a b s =
    lessAt-complete P a b s (index? P i) (index? P j)

  less-trans : (P : 𝒫 ℓ) {i j k : ℕ}
    → T (less P i j) → T (less P j k) → T (less P i k)
  less-trans P {i} {j} {k} p q =
    let (a , b , s) = less-sound P {i} {j} p
        (b′ , c , s′) = less-sound P {j} {k} q
    in less-complete P a c
      (Order.Order.trans (Normalization.order P)
        {pointOf P a} {pointOf P b} {pointOf P c} s
        (subst (λ x → Strict P x (pointOf P c)) (pointOf-≡ P b′ b) s′))

  -- Accessibility of a point carries over to its index; indices of
  -- non-points have no predecessors.
  accessible : (P : 𝒫 ℓ) (c : Point P) → Acc (Strict P) c
    → (i : ℕ) (a : Index P i) → pointOf P a ≡ c
    → Acc (λ i j → T (less P i j)) i
  accessible P c (acc smaller) i a e = acc λ j t →
    let (b , a′ , s) = less-sound P {j} {i} t
    in accessible P (pointOf P b)
      (smaller (pointOf P b)
        (subst (Strict P (pointOf P b)) (trans (pointOf-≡ P a′ a) e) s))
      j b refl

  less-wf : (P : 𝒫 ℓ) → WellFounded (λ i j → T (less P i j))
  less-wf P i = from (index? P i)
    where
      from : Dec (Index P i) → Acc (λ i j → T (less P i j)) i
      from (yes a) =
        accessible P (pointOf P a)
          (Order.Order.wf (Normalization.order P) (pointOf P a)) i a refl
      from (no not-a) = acc λ j t → ⊥-elim (not-a (proj₁ (proj₂
        (less-sound P {j} {i} t))))

  less-compare : (P : 𝒫 ℓ) (i j : ℕ) → T (point P i) → T (point P j)
    → T (less P i j) ⊎ (i ≡ j ⊎ T (less P j i))
  less-compare P i j s t =
    compareAt (toWitness {a? = index? P i} s) (toWitness {a? = index? P j} t)
    where
      compareAt : Index P i → Index P j
        → T (less P i j) ⊎ (i ≡ j ⊎ T (less P j i))
      compareAt a b
          with Order.Order.compare (Normalization.order P)
            (pointOf P a) (pointOf P b)
      ... | inj₁ p = inj₁ (less-complete P a b p)
      ... | inj₂ (inj₁ e) = inj₂ (inj₁ (cong (Normalization.index P) e))
      ... | inj₂ (inj₂ p) = inj₂ (inj₂ (less-complete P b a p))

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
  embed P ((n , h) , p) = n , fromWitness (h , p)

  -- The index witnessed by a point of the Boolean order.
  witness : (P : 𝒫 ℓ) (a : Points (normal P)) → Index P (proj₁ a)
  witness P a = toWitness {a? = index? P (proj₁ a)} (proj₂ a)

  retrieve : (P : 𝒫 ℓ) → Points (normal P) → Point P
  retrieve P a = pointOf P (witness P a)

  retrieve-embed : (P : 𝒫 ℓ) (c : Point P) → retrieve P (embed P c) ≡ c
  retrieve-embed P c = Normalization.equal P refl

  embed-retrieve : (P : 𝒫 ℓ) (a : Points (normal P))
    → embed P (retrieve P a) ≡ a
  embed-retrieve P a = point-≡ (normal P) refl

  -- The index of the class of x, as a witness for its point.
  indexOf : (P : 𝒫 ℓ) (x : X P) → Index P (code P x)
  indexOf P x = proj₂ (proj₁ (class P x)) , proj₂ (class P x)

-- Mathematical shape: P ≃𝒫 presentation(normal P), with
--
--   to x = class index of x,   from n = representative at n.
equivalence : (P : 𝒫 ℓ)
  → P Presented.≃𝒫 Normalized.presentation (order (normal P))
equivalence P = record
  { to = λ x → lift (embed P (class P x))
  ; from = λ a → representative P (retrieve P (lower a))
  ; to-≈ = λ p → lift (cong (embed P) (Normalization.class-resp P p))
  ; from-≈ = λ {a} {b} e →
      subst
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
        (subst₂ (Strict P)
          (pointOf-≡ P a′ (witness P (lower a)))
          (pointOf-≡ P b′ (witness P (lower b)))
          s)
  ; from-to-≈ = λ x →
      subst (λ c → _≈_ P (representative P c) x)
        (sym (retrieve-embed P (class P x)))
        (Normalization.representative-class P x)
  ; to-from-≈ = λ a → lift
      (trans
        (cong (embed P)
          (Normalization.class-representative P (retrieve P (lower a))))
        (embed-retrieve P (lower a)))
  }
