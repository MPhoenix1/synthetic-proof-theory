{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Arithmetic.Exponential where

-- ω^P satisfies the exponentiation specification of Kraus, Nordvall
-- Forsberg and Xu with base ω, the presentation of the natural numbers:
--   ω^Z ≃ S                 for Z a zero and S a successor of Z,
--   ω^S ≃ ω^P · ω           for S a successor of P,
--   ω^A ≃ D                 for A the limit of a strictly increasing Pₙ
--                           and D a supremum of the ω^Pₙ.
-- A support of ω^(P + 1) is either a support of ω^P, in copy 0 of ω^P · ω,
-- or the top exponent with a coefficient k followed by a support of ω^P,
-- in copy k + 1. ω^ respects ≃𝒫.

open import Agda.Primitive using (Level)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_)
import Data.List as List
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s)
import Data.Nat as Nat
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; trans)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
import SPT.Cubical.OrdinalGeometry.Presentation.Successor as Adjoin
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization as Normal
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization.Maps
  as NormalMaps
import SPT.Cubical.OrdinalGeometry.Presentation.Normalization.Presentation
  as Exact
import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order
import SPT.Cubical.OrdinalGeometry.ExactOrder.Maps as Orders
import SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.Support as Support
import SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.Initial
  as ExponentialInitial
import SPT.Cubical.OrdinalGeometry.Operation.Exponential as Exponential
open Exponential using (exp)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Characterization using
  (bijection; Zero; empty; Successor; module Successors; Supremum;
   module Suprema; Increasing)
open import SPT.Cubical.OrdinalGeometry.Arithmetic.Multiplication using (_·_)

private
  variable
    ℓ : Level
    P Q S : 𝒫 ℓ

-- The natural numbers, as a presented ordinal.
omega : 𝒫 ℓ
omega = Exact.presentation Order.natural

-- ω^ respects equivalence.
respect : P Presented.≃𝒫 Q → exp P Presented.≃𝒫 exp Q
respect e = Maps.antisymmetry (Exponential.initial (Maps.equivalence e))
  (Exponential.initial (Maps.equivalence (Presented.≃𝒫-sym e)))

opaque
  unfolding exp _·_

  -- Mathematical shape: ω^Z ≃ Z + 1; the empty support is the only one.
  single : (Z : 𝒫 ℓ) → Zero Z → exp Z Presented.≃𝒫 Maps.Successor.next Z
  single Z z = Presented.≃𝒫-sym (bijection embedding covers)
    where
    module Entry = Presented.Diagonal.Successor
      (Adjoin.constant Z) zero

    map : Entry.Entry → 𝒫.X (exp Z)
    map (Entry.point x) = ⊥-elim (empty z x)
    map Entry.top = lift ([] , tt)

    resp : ∀ {u v} → u Entry.≈ v → 𝒫._≈_ (exp Z) (map u) (map v)
    resp {Entry.point x} _ = ⊥-elim (empty z x)
    resp {Entry.top} {Entry.top} Entry.top≈ = lift refl

    strict : ∀ {u v} → u Entry.< v → 𝒫._<_ (exp Z) (map u) (map v)
    strict {Entry.point x} _ = ⊥-elim (empty z x)
    strict {Entry.top} ()

    embedding : Maps.Embedding (Maps.Successor.next Z) (exp Z)
    embedding = record
      { map = map
      ; resp = λ {u} {v} → resp {u} {v}
      ; strict = λ {u} {v} → strict {u} {v}
      }

    covers : (y : 𝒫.X (exp Z))
      → Σ Entry.Entry (λ u → 𝒫._≈_ (exp Z) (map u) y)
    covers (lift ([] , tt)) = Entry.top , lift refl
    covers (lift (((e , k) ∷ xs) , v)) =
      ⊥-elim (empty z (Normal.representative Z e))

  -- Mathematical shape: ω^(P + 1) ≃ ω^P · ω. The copy of a support is the
  -- coefficient of the top exponent plus one, or 0 without that exponent.
  next : (P : 𝒫 ℓ)
    → exp (Maps.Successor.next P) Presented.≃𝒫 (exp P · omega)
  next {ℓ} P = Presented.≃𝒫-sym (bijection embedding covers)
    where
    N : 𝒫 ℓ
    N = Maps.Successor.next P

    ω : 𝒫 ℓ
    ω = omega

    module Entry = Presented.Diagonal.Successor
      (Adjoin.constant P) zero
    module Base = Support.Power (Normal.order P)
    module Top = Support.Power (Normal.order N)
    module Copies = Order.Sum (Normal.order ω)
      (λ _ → Normal.order (exp P))

    -- Old exponents, as normalized points of P + 1.
    lifted : Orders.Embedding (Normal.order P) (Normal.order N)
    lifted = NormalMaps.embedding
      (Maps.Initial.embedding (Maps.Successor.initial P))

    raise : Base.Term → Top.Term
    raise = Orders.Embedding.map (ExponentialInitial.embedding lifted)

    peak : Normal.Point N
    peak = Normal.class N Entry.top

    lifted-peak : (a : Normal.Point P)
      → Normal.Strict N (Orders.Embedding.map lifted a) peak
    lifted-peak a = Normal.class-strict N
      {x = Entry.point (Normal.representative P a)} {y = Entry.top}
      Entry.point<top

    -- The top exponent above a raised support.
    capped : (k : ℕ) (s : Base.Term)
      → Top.Valid ((peak , k) ∷ Top.raw (raise s))
    capped k ([] , _) = tt
    capped k (((a , n) ∷ xs) , v) =
      Top.complete {Orders.Embedding.map lifted a} {peak} (lifted-peak a) ,
      proj₂ (raise (((a , n) ∷ xs) , v))

    -- The support in copy n of ω^P.
    glue : ℕ → Base.Term → Top.Term
    glue zero s = raise s
    glue (suc k) s = ((peak , k) ∷ Top.raw (raise s)) , capped k s

    number : Normal.Point ω → ℕ
    number j = lower (Normal.representative ω j)

    shape : Normal.Point (exp P) → Base.Term
    shape a = lower (Normal.representative (exp P) a)

    map : 𝒫.X (exp P · ω) → 𝒫.X (exp N)
    map (lift (j , a)) = lift (glue (number j) (shape a))

    -- A raised support lies below every support led by the top exponent.
    under : (s : Base.Term) {k : ℕ} {ys : Top.Raw}
      → Top.raw (raise s) Top.≺ ((peak , k) ∷ ys)
    under ([] , _) = Top.empty
    under (((a , n) ∷ xs) , v) {k} = Top.head (Top.Pair.earlier
      {a = Orders.Embedding.map lifted a} {a′ = peak} {x = n} {y = k}
      (lifted-peak a))

    earlier : {m n : ℕ} → m Nat.< n → (s t : Base.Term)
      → glue m s Top.< glue n t
    earlier {zero} {suc k} (s≤s z≤n) s t = under s
    earlier {suc j} {suc k} (s≤s p) s t = Top.head (Top.Pair.within peak p)

    within : (n : ℕ) {s t : Base.Term} → s Base.< t
      → glue n s Top.< glue n t
    within zero {s} {t} p =
      Orders.Embedding.strict (ExponentialInitial.embedding lifted) {s} {t} p
    within (suc k) {s} {t} p = Top.tail
      (Orders.Embedding.strict (ExponentialInitial.embedding lifted) {s} {t} p)

    strict : ∀ {u v} → 𝒫._<_ (exp P · ω) u v
      → 𝒫._<_ (exp N) (map u) (map v)
    strict {lift (j , a)} {lift (j′ , b)} (lift (Copies.earlier p)) =
      lift (earlier {number j} {number j′}
        (lower (Normal.representative-strict ω {a = j} {b = j′} p))
        (shape a) (shape b))
    strict {lift (j , a)} {lift (.j , b)} (lift (Copies.within .j p)) =
      lift (within (number j) {shape a} {shape b}
        (lower (Normal.representative-strict (exp P) {a = a} {b = b} p)))

    embedding : Maps.Embedding (exp P · ω) (exp N)
    embedding = record
      { map = map
      ; resp = λ where
          (lift e) → lift (cong (λ w → glue (number (proj₁ w))
            (shape (proj₂ w))) e)
      ; strict = λ {u} {v} → strict {u} {v}
      }

    -- A normalized point strictly below another is an old exponent.
    image : (b : Normal.Point N) (x : 𝒫.X P)
      → Normal.representative N b ≡ Entry.point x
      → Σ (Normal.Point P) (λ a → Orders.Embedding.map lifted a ≡ b)
    image b x r = Normal.class P x , trans
      (Normal.class-resp N (Entry.point≈ (Normal.representative-class P x)))
      (trans (cong (Normal.class N) (sym r)) (Normal.class-representative N b))

    beneath : (b e : Normal.Point N) → Normal.Strict N b e
      → Σ (Normal.Point P) (λ a → Orders.Embedding.map lifted a ≡ b)
    beneath b e p = old (Normal.representative N b) refl
      (Normal.representative-strict N {a = b} {b = e} p)
      where
      old : (u : Entry.Entry) → Normal.representative N b ≡ u
        → u Entry.< Normal.representative N e
        → Σ (Normal.Point P) (λ a → Orders.Embedding.map lifted a ≡ b)
      old (Entry.point x) r _ = image b x r
      old Entry.top r ()

    -- The exponents after the leading one lie below it.
    descending : (e : Normal.Point N) (k : ℕ) (xs : Top.Raw)
      → Top.Valid ((e , k) ∷ xs)
      → All (λ b → Normal.Strict N b e) (List.map proj₁ xs)
    descending e k [] _ = []
    descending e k ((b , m) ∷ ys) (p , w) = Top.sound {b} {e} p ∷ All.map
      (λ {c} q → Order.Order.trans (Normal.order N) {c} {b} {e} q
        (Top.sound {b} {e} p))
      (descending b m ys w)

    restrict : (t : Top.Term)
      → All (λ b → Σ (Normal.Point P)
          (λ a → Orders.Embedding.map lifted a ≡ b)) (Top.exponents t)
      → Σ Base.Term (λ s → raise s ≡ t)
    restrict = ExponentialInitial.restrict lifted

    -- Every support of ω^(P + 1) is glued from a copy and a support.
    decompose : (t : Top.Term)
      → Σ ℕ (λ n → Σ Base.Term (λ s → glue n s ≡ t))
    decompose ([] , v) = zero , Base.zero , Top.equal refl
    decompose (((e , k) ∷ xs) , v) with Normal.representative N e in r
    ... | Entry.top with restrict (xs , Top.tail-valid v)
          (All.map (λ {b} q → beneath b e q) (descending e k xs v))
    ...   | s , q = suc k , s , Top.equal (cong₂ _∷_
            (cong (_, k) (trans (cong (Normal.class N) (sym r))
              (Normal.class-representative N e)))
            (cong Top.raw q))
    decompose (((e , k) ∷ xs) , v) | Entry.point y
      with restrict (((e , k) ∷ xs) , v)
        (image e y r ∷ All.map (λ {b} q → beneath b e q)
          (descending e k xs v))
    ... | s , q = zero , s , q

    covers : (y : 𝒫.X (exp N))
      → Σ (𝒫.X (exp P · ω)) (λ u → 𝒫._≈_ (exp N) (map u) y)
    covers (lift t) with decompose t
    ... | n , s , e =
      lift (Normal.class ω (lift n) , Normal.class (exp P) (lift s)) ,
      lift (trans (cong₂ glue
        (lower (Normal.representative-class ω (lift n)))
        (lower (Normal.representative-class (exp P) (lift s)))) e)

------------------------------------------------------------------------
-- The specification

-- Mathematical shape: is-zero Z → S is-suc-of Z → ω^Z ≃ S.
zero-law : (Z : 𝒫 ℓ) → Zero Z → Successor Z S → exp Z Presented.≃𝒫 S
zero-law Z z s = Presented.≃𝒫-trans (single Z z)
  (Presented.≃𝒫-sym (Successors.equivalent s))

-- Mathematical shape: S is-suc-of P → ω^S ≃ ω^P · ω.
successor-law : Successor P S → exp S Presented.≃𝒫 (exp P · omega)
successor-law {P = P} s =
  Presented.≃𝒫-trans (respect (Successors.equivalent s)) (next P)

-- Mathematical shape: A is-lim-of Pₙ → D is-sup-of ω^Pₙ → ω^A ≃ D.
limit-law : (s : Increasing ℓ) {A D : 𝒫 ℓ}
  → Supremum (Increasing.stage s) A
  → Supremum (λ n → exp (Increasing.stage s n)) D
  → exp A Presented.≃𝒫 D
limit-law s a d = Presented.≃𝒫-trans
  (respect (Suprema.unique a (Increasing.supremum s)))
  (Presented.≃𝒫-trans
    (Presented.≃𝒫-sym (Exponential.continuous (Increasing.chain s)))
    (Suprema.unique
      (Suprema.completion (Exponential.chain (Increasing.chain s))) d))
