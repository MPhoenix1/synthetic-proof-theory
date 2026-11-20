{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Base.Fin where

-- `Fin n` is the type of the `n` numbers below `n`: `fzero` and the successors
-- `fsuc i` of points of `Fin m` for `n = suc m`. It indexes finitely many
-- things, such as the variables in scope of a formula. Each point has its
-- number (`to-ℕ`), the successor is injective, and equality is decidable.
--
-- The numeral `# m` is the point with number `m`. Its bound `is-below m n` is
-- the unit type when `m` is below `n` and the empty type otherwise, so at a
-- numeral the bound is found by computation and is never written. `Fin m` and
-- `Fin n` embed in `Fin (m + n)`: at the same number (`i ↑ˡ n`), and after the
-- first `m` numbers (`m ↑ʳ j`).
--
-- An environment of `n` points of `A` is a function `Fin n → A`. A point and
-- an environment give the environment with the point at the newest position
-- (`extend-environment`):
--
--   extend-environment x env fzero = x,
--   extend-environment x env (fsuc i) = env i.
--
-- Given a default point, an environment extends to all numbers
-- (`extend-to-naturals`). Under a reflexive relation, the image of the
-- extension at the number of a position is related to the image of the
-- entry there (`extended-related-at`).
--
-- The points below m + n are the sum of the points below m and the points
-- below n. A point of Fin (m + n) splits into a point of Fin m or one of
-- Fin n (`split-at`), and the embeddings ↑ˡ and ↑ʳ join a point of the sum
-- back (`join-at`). Splitting and joining are inverse,
--
--   join-at m n (split-at m n i) ＝ i,   split-at m n (join-at m n x) ＝ x,
--
-- and an embedded point splits to its side (`split-at-↑ˡ`, `split-at-↑ʳ`).
-- The number of a point embedded on the left is its own, on the right it
-- is moved by m (`to-ℕ-↑ˡ`, `to-ℕ-↑ʳ`); every number is below its bound
-- (`to-ℕ-is-below`), and a point is determined by its number
-- (`to-ℕ-is-injective`).

open import SPT.Cubical.Base.Empty using (𝟘)
open import SPT.Cubical.Base.Universes using (Level)
open import SPT.Cubical.Base.Unit using (𝟙)
open import SPT.Cubical.Base.Identity using (_＝_; refl; _≠_; ap; _∙_)
open import SPT.Cubical.Base.Sum using (inl; inr; cases; _⊎_)
open import SPT.Cubical.Base.Decidable using (has-decidable-equality)
open import SPT.Cubical.Base.Natural using
  (ℕ; zero; suc; _+_; _<ℕˢ_; suc-is-injective; s≤s; z≤n)

data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (suc n)
  fsuc : {n : ℕ} → Fin n → Fin (suc n)

to-ℕ : {n : ℕ} → Fin n → ℕ
to-ℕ fzero = zero
to-ℕ (fsuc i) = suc (to-ℕ i)

------------------------------------------------------------------------
-- Numerals

-- `m` is below `n`, computed.
is-below : ℕ → ℕ → Set
is-below m zero = 𝟘
is-below zero (suc n) = 𝟙
is-below (suc m) (suc n) = is-below m n

infix 70 #_

#_ : (m : ℕ) {n : ℕ} {below : is-below m n} → Fin n
#_ m {zero} {()}
#_ zero {suc n} = fzero
#_ (suc m) {suc n} {below} = fsuc (#_ m {n} {below})

------------------------------------------------------------------------
-- Embeddings in a sum

infixl 32 _↑ˡ_
infixr 32 _↑ʳ_

_↑ˡ_ : {m : ℕ} → Fin m → (n : ℕ) → Fin (m + n)
fzero ↑ˡ n = fzero
fsuc i ↑ˡ n = fsuc (i ↑ˡ n)

_↑ʳ_ : {n : ℕ} (m : ℕ) → Fin n → Fin (m + n)
zero ↑ʳ j = j
suc m ↑ʳ j = fsuc (m ↑ʳ j)

------------------------------------------------------------------------
-- Properties

fzero-is-not-fsuc : {n : ℕ} {i : Fin n} → fzero ≠ fsuc i
fzero-is-not-fsuc ()

fsuc-is-injective : {n : ℕ} {i j : Fin n} → fsuc i ＝ fsuc j → i ＝ j
fsuc-is-injective refl = refl

Fin-has-decidable-equality : (n : ℕ) → has-decidable-equality (Fin n)
Fin-has-decidable-equality (suc n) fzero fzero = inl refl
Fin-has-decidable-equality (suc n) fzero (fsuc j) = inr fzero-is-not-fsuc
Fin-has-decidable-equality (suc n) (fsuc i) fzero = inr (λ ())
Fin-has-decidable-equality (suc n) (fsuc i) (fsuc j) =
  cases
    (λ e → inl (ap fsuc e))
    (λ d → inr (λ e → d (fsuc-is-injective e)))
    (Fin-has-decidable-equality n i j)

------------------------------------------------------------------------
-- Environments

module _ {ℓ : Level} {A : Set ℓ} where

  extend-environment : {n : ℕ} → A → (Fin n → A) → Fin (suc n) → A
  extend-environment x env fzero = x
  extend-environment x env (fsuc i) = env i

------------------------------------------------------------------------
-- Environments on all numbers

module _ {ℓ : Level} {A : Set ℓ} (a : A) where

  extend-to-naturals : {n : ℕ} → (Fin n → A) → ℕ → A
  extend-to-naturals {zero} ρ k = a
  extend-to-naturals {suc n} ρ zero = ρ fzero
  extend-to-naturals {suc n} ρ (suc k) = extend-to-naturals (λ i → ρ (fsuc i)) k

  module _ {κ μ : Level} {B : Set κ} (R : B → B → Set μ)
    (r : (b : B) → R b b) where

    extended-related-at : {n : ℕ} (ρ : Fin n → A) (f : A → B) (i : Fin n) →
      R (f (extend-to-naturals ρ (to-ℕ i))) (f (ρ i))
    extended-related-at ρ f fzero = r (f (ρ fzero))
    extended-related-at ρ f (fsuc i) =
      extended-related-at (λ k → ρ (fsuc k)) f i

------------------------------------------------------------------------
-- Points below a sum: splitting and joining

-- A point of the left summand moved past one more point.
left-fsuc : {m n : ℕ} → Fin m ⊎ Fin n → Fin (suc m) ⊎ Fin n
left-fsuc = cases (λ i → inl (fsuc i)) inr

split-at : (m n : ℕ) → Fin (m + n) → Fin m ⊎ Fin n
split-at zero n i = inr i
split-at (suc m) n fzero = inl fzero
split-at (suc m) n (fsuc i) = left-fsuc (split-at m n i)

join-at : (m n : ℕ) → Fin m ⊎ Fin n → Fin (m + n)
join-at m n = cases (λ i → i ↑ˡ n) (λ j → m ↑ʳ j)

------------------------------------------------------------------------
-- Splitting and joining are inverse

split-at-↑ˡ : (m : ℕ) (i : Fin m) (n : ℕ) → split-at m n (i ↑ˡ n) ＝ inl i
split-at-↑ˡ (suc m) fzero n = refl
split-at-↑ˡ (suc m) (fsuc i) n = ap left-fsuc (split-at-↑ˡ m i n)

split-at-↑ʳ : (m n : ℕ) (j : Fin n) → split-at m n (m ↑ʳ j) ＝ inr j
split-at-↑ʳ zero n j = refl
split-at-↑ʳ (suc m) n j = ap left-fsuc (split-at-↑ʳ m n j)

join-at-left-fsuc : (m n : ℕ) (x : Fin m ⊎ Fin n) →
  join-at (suc m) n (left-fsuc x) ＝ fsuc (join-at m n x)
join-at-left-fsuc m n (inl i) = refl
join-at-left-fsuc m n (inr j) = refl

join-at-split-at : (m n : ℕ) (i : Fin (m + n)) →
  join-at m n (split-at m n i) ＝ i
join-at-split-at zero n i = refl
join-at-split-at (suc m) n fzero = refl
join-at-split-at (suc m) n (fsuc i) =
  join-at-left-fsuc m n (split-at m n i) ∙ ap fsuc (join-at-split-at m n i)

split-at-join-at : (m n : ℕ) (x : Fin m ⊎ Fin n) →
  split-at m n (join-at m n x) ＝ x
split-at-join-at m n (inl i) = split-at-↑ˡ m i n
split-at-join-at m n (inr j) = split-at-↑ʳ m n j

------------------------------------------------------------------------
-- Numbers of points

to-ℕ-↑ˡ : {m : ℕ} (i : Fin m) (n : ℕ) → to-ℕ (i ↑ˡ n) ＝ to-ℕ i
to-ℕ-↑ˡ fzero n = refl
to-ℕ-↑ˡ (fsuc i) n = ap suc (to-ℕ-↑ˡ i n)

to-ℕ-↑ʳ : {n : ℕ} (m : ℕ) (j : Fin n) → to-ℕ (m ↑ʳ j) ＝ m + to-ℕ j
to-ℕ-↑ʳ zero j = refl
to-ℕ-↑ʳ (suc m) j = ap suc (to-ℕ-↑ʳ m j)

to-ℕ-is-below : {n : ℕ} (i : Fin n) → to-ℕ i <ℕˢ n
to-ℕ-is-below fzero = s≤s z≤n
to-ℕ-is-below (fsuc i) = s≤s (to-ℕ-is-below i)

to-ℕ-is-injective : {n : ℕ} {i j : Fin n} → to-ℕ i ＝ to-ℕ j → i ＝ j
to-ℕ-is-injective {suc n} {fzero} {fzero} e = refl
to-ℕ-is-injective {suc n} {fzero} {fsuc j} ()
to-ℕ-is-injective {suc n} {fsuc i} {fzero} ()
to-ℕ-is-injective {suc n} {fsuc i} {fsuc j} e =
  ap fsuc (to-ℕ-is-injective (suc-is-injective e))
