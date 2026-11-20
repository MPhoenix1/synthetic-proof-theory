{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Nat.Arithmetic where

-- The structural order of ℕ with addition and truncated subtraction, and
-- the powers of two. The order splits into the strict order and identity
-- (`≤ℕˢ-split`, `≤ℕˢ-or-above`), recursing on the numbers, and any two of
-- its proofs are identified (`≤ℕˢ-is-proposition`); subtraction from a
-- bound reverses the strict order (`∸-reverses-<ℕˢ`), subtraction of a
-- common lower bound preserves it (`∸-right-preserves-<ℕˢ`), and addition
-- and subtraction undo each other (`∸-+-cancels`, `+-∸-cancels`):
--
--   n ≤ m → (m ∸ n) + n ＝ m,   (m + n) ∸ n ＝ m;
--
-- addition is monotone
-- (`+-preserves-≤ℕˢ`) and cancellable on the left (`+-left-cancels-≤ℕˢ`),
-- and a number above k is k plus a positive number (`above-decomposes`).
-- The power 2ⁿ is the successor of 2ⁿ − 1 (`below-2^`), so that
--
--   2ⁿ⁺¹ ＝ 2ⁿ + 2ⁿ
--
-- holds by definition (`2^-suc`). Addition commutes and exchanges its left
-- arguments (`+-commutes`, `+-left-exchange`), and multiplication, which
-- recurses on its left argument, has the recursion equations on its right
-- one (`*-zero-right`, `*-suc-right`), from SPT.Base's `+-zero-right` and
-- `+-suc-right`.

open import SPT.Base
open import SPT.Foundation.Propositions using (is-proposition)

------------------------------------------------------------------------
-- The structural order

-- m ≤ n splits into m < n or m ＝ n. The split recurses on the numbers, so
-- on closed numbers it computes without reducing the proof of m ≤ n. Any
-- two proofs of m ≤ n are identified.

≤ℕˢ-pred : {m n : ℕ} → suc m ≤ℕˢ suc n → m ≤ℕˢ n
≤ℕˢ-pred (s≤s m≤n) = m≤n

suc-preserves-split : {m n : ℕ} → (m <ℕˢ n) ⊎ (m ＝ n) →
  (suc m <ℕˢ suc n) ⊎ (suc m ＝ suc n)
suc-preserves-split (inl m<n) = inl (s≤s m<n)
suc-preserves-split (inr m=n) = inr (ap suc m=n)

≤ℕˢ-split : (m n : ℕ) → m ≤ℕˢ n → (m <ℕˢ n) ⊎ (m ＝ n)
≤ℕˢ-split zero zero m≤n = inr refl
≤ℕˢ-split zero (suc n) m≤n = inl (s≤s z≤n)
≤ℕˢ-split (suc m) zero ()
≤ℕˢ-split (suc m) (suc n) m≤n =
  suc-preserves-split (≤ℕˢ-split m n (≤ℕˢ-pred m≤n))

≤ℕˢ-is-proposition : {m n : ℕ} → is-proposition (m ≤ℕˢ n)
≤ℕˢ-is-proposition z≤n z≤n = refl
≤ℕˢ-is-proposition (s≤s p) (s≤s q) = ap s≤s (≤ℕˢ-is-proposition p q)

<ℕˢ-to-≤ℕˢ : {m n : ℕ} → m <ℕˢ n → m ≤ℕˢ n
<ℕˢ-to-≤ℕˢ {m} m<n = ≤ℕˢ-trans (≤ℕˢ-suc (≤ℕˢ-refl m)) m<n

-- A number at most m is not m + 1.
≤ℕˢ-excludes-suc : {c m : ℕ} → c ≤ℕˢ m → suc m ≠ c
≤ℕˢ-excludes-suc {c} {m} c≤m e =
  <ℕˢ-irrefl m (transport (λ k → k ≤ℕˢ m) (e ⁻¹) c≤m)

-- Every pair of numbers is ordered one way or the other.
order-from-trichotomy : (a b : ℕ) → Trichotomy _＝_ _<ℕˢ_ a b →
  (a ≤ℕˢ b) ⊎ (b <ℕˢ a)
order-from-trichotomy a b (inl a<b) = inl (<ℕˢ-to-≤ℕˢ a<b)
order-from-trichotomy a b (inr (inl a=b)) =
  inl (transport (λ k → a ≤ℕˢ k) a=b (≤ℕˢ-refl a))
order-from-trichotomy a b (inr (inr b<a)) = inr b<a

≤ℕˢ-or-above : (a b : ℕ) → (a ≤ℕˢ b) ⊎ (b <ℕˢ a)
≤ℕˢ-or-above a b = order-from-trichotomy a b (<ℕˢ-trichotomy a b)

------------------------------------------------------------------------
-- Subtraction from a bound

∸-≤ℕˢ : (n k : ℕ) → (n ∸ k) ≤ℕˢ n
∸-≤ℕˢ n zero = ≤ℕˢ-refl n
∸-≤ℕˢ zero (suc k) = z≤n
∸-≤ℕˢ (suc n) (suc k) = ≤ℕˢ-suc (∸-≤ℕˢ n k)

-- Below a bound n, the distance to n decreases as the number increases.
∸-reverses-<ℕˢ : (n : ℕ) {x y : ℕ} → x <ℕˢ y → y ≤ℕˢ n →
  (n ∸ y) <ℕˢ (n ∸ x)
∸-reverses-<ℕˢ n {x} {zero} () y≤n
∸-reverses-<ℕˢ zero {x} {suc y} x<y ()
∸-reverses-<ℕˢ (suc n) {zero} {suc y} x<y (s≤s y≤n) = s≤s (∸-≤ℕˢ n y)
∸-reverses-<ℕˢ (suc n) {suc x} {suc y} (s≤s x<y) (s≤s y≤n) =
  ∸-reverses-<ℕˢ n x<y y≤n

-- Subtracting a common lower bound k preserves the strict order.
∸-right-preserves-<ℕˢ : (k : ℕ) {x y : ℕ} → k ≤ℕˢ x → x <ℕˢ y →
  (x ∸ k) <ℕˢ (y ∸ k)
∸-right-preserves-<ℕˢ zero k≤x x<y = x<y
∸-right-preserves-<ℕˢ (suc k) {suc x} {suc y} (s≤s k≤x) (s≤s x<y) =
  ∸-right-preserves-<ℕˢ k k≤x x<y

-- Adding back what was subtracted from above returns the number, and so
-- does subtracting what was added.
∸-+-cancels : {m n : ℕ} → n ≤ℕˢ m → (m ∸ n) + n ＝ m
∸-+-cancels {m} {zero} z≤n = +-zero-right m
∸-+-cancels {suc m} {suc n} (s≤s n≤m) =
  +-suc-right (m ∸ n) n ∙ ap suc (∸-+-cancels n≤m)

+-∸-cancels : (m n : ℕ) → (m + n) ∸ n ＝ m
+-∸-cancels m zero = +-zero-right m
+-∸-cancels m (suc n) =
  ap (λ k → k ∸ suc n) (+-suc-right m n) ∙ +-∸-cancels m n

------------------------------------------------------------------------
-- Addition

-- A number above k is k plus a positive number.
above-decomposition-suc : (k c : ℕ) →
  Σ ℕ (λ w → (zero <ℕˢ w) × (k + w ＝ c)) →
  Σ ℕ (λ w → (zero <ℕˢ w) × (suc k + w ＝ suc c))
above-decomposition-suc k c (w , 0<w , e) = w , 0<w , ap suc e

above-decomposes : (k c : ℕ) → k <ℕˢ c →
  Σ ℕ (λ w → (zero <ℕˢ w) × (k + w ＝ c))
above-decomposes zero c 0<c = c , 0<c , refl
above-decomposes (suc k) (suc c) (s≤s k<c) =
  above-decomposition-suc k c (above-decomposes k c k<c)

+-left-cancels-≤ℕˢ : (k w n : ℕ) → (k + w) ≤ℕˢ (k + n) → w ≤ℕˢ n
+-left-cancels-≤ℕˢ zero w n w≤n = w≤n
+-left-cancels-≤ℕˢ (suc k) w n (s≤s p) = +-left-cancels-≤ℕˢ k w n p

+-left-cancels-<ℕˢ : (k w n : ℕ) → (k + w) <ℕˢ (k + n) → w <ℕˢ n
+-left-cancels-<ℕˢ zero w n w<n = w<n
+-left-cancels-<ℕˢ (suc k) w n (s≤s p) = +-left-cancels-<ℕˢ k w n p

+-left-preserves-<ℕˢ : (k w n : ℕ) → w <ℕˢ n → (k + w) <ℕˢ (k + n)
+-left-preserves-<ℕˢ zero w n w<n = w<n
+-left-preserves-<ℕˢ (suc k) w n w<n = s≤s (+-left-preserves-<ℕˢ k w n w<n)

-- A number is at most itself plus any number, on either side, and
-- addition is monotone.
≤ℕˢ-+-left : (c d : ℕ) → d ≤ℕˢ (c + d)
≤ℕˢ-+-left zero d = ≤ℕˢ-refl d
≤ℕˢ-+-left (suc c) d = ≤ℕˢ-suc (≤ℕˢ-+-left c d)

≤ℕˢ-+-right : (n k : ℕ) → n ≤ℕˢ (n + k)
≤ℕˢ-+-right zero k = z≤n
≤ℕˢ-+-right (suc n) k = s≤s (≤ℕˢ-+-right n k)

+-preserves-≤ℕˢ : {a b c d : ℕ} → a ≤ℕˢ c → b ≤ℕˢ d → (a + b) ≤ℕˢ (c + d)
+-preserves-≤ℕˢ {zero} {b} {c} {d} z≤n b≤d = ≤ℕˢ-trans b≤d (≤ℕˢ-+-left c d)
+-preserves-≤ℕˢ (s≤s a≤c) b≤d = s≤s (+-preserves-≤ℕˢ a≤c b≤d)

+-right-preserves-≤ℕˢ : {w n : ℕ} (k : ℕ) → w ≤ℕˢ n → (w + k) ≤ℕˢ (n + k)
+-right-preserves-≤ℕˢ {zero} {n} k z≤n = ≤ℕˢ-+-left n k
+-right-preserves-≤ℕˢ k (s≤s w≤n) = s≤s (+-right-preserves-≤ℕˢ k w≤n)

------------------------------------------------------------------------
-- Powers of two

-- 2ⁿ − 1, the largest value strictly below the top of the Laver table Aₙ,
-- and 2ⁿ, its successor. 2ⁿ⁺¹ − 1 is (2ⁿ − 1) + 2ⁿ, so that 2ⁿ⁺¹ is
-- 2ⁿ + 2ⁿ by definition (`2^-suc`).

below-2^ : ℕ → ℕ
below-2^ zero = zero
below-2^ (suc n) = below-2^ n + suc (below-2^ n)

infix 45 2^_

2^_ : ℕ → ℕ
2^ n = suc (below-2^ n)

2^-suc : (n : ℕ) → 2^ (suc n) ＝ 2^ n + 2^ n
2^-suc n = refl

------------------------------------------------------------------------
-- Commutativity, and multiplication on the right

+-left-exchange : (a b c : ℕ) → a + (b + c) ＝ b + (a + c)
+-left-exchange zero b c = refl
+-left-exchange (suc a) b c =
  ap suc (+-left-exchange a b c) ∙ (+-suc-right b (a + c)) ⁻¹

+-commutes : (m n : ℕ) → m + n ＝ n + m
+-commutes zero n = (+-zero-right n) ⁻¹
+-commutes (suc m) n = ap suc (+-commutes m n) ∙ (+-suc-right n m) ⁻¹

*-zero-right : (n : ℕ) → n * zero ＝ zero
*-zero-right zero = refl
*-zero-right (suc n) = *-zero-right n

*-suc-right : (m n : ℕ) → m * suc n ＝ m + m * n
*-suc-right zero n = refl
*-suc-right (suc m) n =
  ap suc
    ( ap (λ k → n + k) (*-suc-right m n) ∙ +-left-exchange n m (m * n))
