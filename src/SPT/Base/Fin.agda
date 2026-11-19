{-# OPTIONS --safe --without-K #-}

module SPT.Base.Fin where

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

open import SPT.Base.Empty using (𝟘)
open import SPT.Base.Unit using (𝟙)
open import SPT.Base.Identity using (_＝_; refl; _≠_; ap)
open import SPT.Base.Sum using (inl; inr; cases)
open import SPT.Base.Decidable using (has-decidable-equality)
open import SPT.Base.Natural using (ℕ; zero; suc; _+_)

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
