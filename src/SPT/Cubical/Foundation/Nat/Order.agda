{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Nat.Order where

-- Natural numbers are compared by a function `cmpℕ` into the three answers
-- `less`, `greater` and `equal` (`Tri`). The computational order `m <ℕᶜ n` is
-- the equation `cmpℕ m n ＝ less`, and `m ≤ℕᶜ n` is `m <ℕᶜ n` or `m ＝ n`. Each
-- answer is tied to the relation between the numbers it compares: comparing in
-- the opposite order flips the answer, `equal` means identified, a number
-- compared with itself gives `equal`, and `less` is transitive. The comparison
-- decides trichotomy (`cmpℕᶜ`), and the order is the structural order `<ℕˢ` of
-- `SPT.Base.Natural` (`cmpℕ-less⇒<ℕˢ`, `<ℕˢ⇒cmpℕ-less`), with its successor and
-- maximum laws.
--
-- The positive naturals `ℕ⁺` are represented by their predecessor, `1+ n` for
-- `n + 1`, and compared by comparing predecessors.
--
-- The points of `<ℕᶜ` cannot be read off its witnesses, since `cmpℕ` is not
-- injective; the transitivity laws take the three numbers explicitly.

open import SPT.Cubical.Base

------------------------------------------------------------------------
-- Answers of a comparison

data Tri : Set where
  less greater equal : Tri

flipTri : Tri → Tri
flipTri less = greater
flipTri greater = less
flipTri equal = equal

------------------------------------------------------------------------
-- Comparison of natural numbers

cmpℕ : ℕ → ℕ → Tri
cmpℕ zero zero = equal
cmpℕ zero (suc n) = less
cmpℕ (suc m) zero = greater
cmpℕ (suc m) (suc n) = cmpℕ m n

------------------------------------------------------------------------
-- Positive naturals

record ℕ⁺ : Set where
  constructor 1+_
  field
    pred : ℕ

open ℕ⁺ public

infix 46 1+_

one⁺ : ℕ⁺
one⁺ = 1+ 0

two⁺ : ℕ⁺
two⁺ = 1+ 1

cmp⁺ : ℕ⁺ → ℕ⁺ → Tri
cmp⁺ (1+ m) (1+ n) = cmpℕ m n

------------------------------------------------------------------------
-- The computational orders

infix 30 _<ℕᶜ_ _≤ℕᶜ_ _<⁺ᶜ_

_<ℕᶜ_ : ℕ → ℕ → Set
m <ℕᶜ n = cmpℕ m n ＝ less

_≤ℕᶜ_ : ℕ → ℕ → Set
m ≤ℕᶜ n = (m <ℕᶜ n) ⊎ (m ＝ n)

_<⁺ᶜ_ : ℕ⁺ → ℕ⁺ → Set
m <⁺ᶜ n = cmp⁺ m n ＝ less

------------------------------------------------------------------------
-- Distinct answers are distinct

less≢equal : {A : Set} → less ＝ equal → A
less≢equal ()

greater≢equal : {A : Set} → greater ＝ equal → A
greater≢equal ()

equal≢less : {A : Set} → equal ＝ less → A
equal≢less ()

equal≢greater : {A : Set} → equal ＝ greater → A
equal≢greater ()

greater≢less : {A : Set} → greater ＝ less → A
greater≢less ()

less≢greater : {A : Set} → less ＝ greater → A
less≢greater ()

------------------------------------------------------------------------
-- The comparison of natural numbers

cmpℕ-flip : (m n : ℕ) → cmpℕ n m ＝ flipTri (cmpℕ m n)
cmpℕ-flip zero zero = refl
cmpℕ-flip zero (suc n) = refl
cmpℕ-flip (suc m) zero = refl
cmpℕ-flip (suc m) (suc n) = cmpℕ-flip m n

cmpℕ-equal⇒≡ : (m n : ℕ) → cmpℕ m n ＝ equal → m ＝ n
cmpℕ-equal⇒≡ zero zero refl = refl
cmpℕ-equal⇒≡ (suc m) (suc n) p = ap suc (cmpℕ-equal⇒≡ m n p)

cmpℕ-self : (n : ℕ) → cmpℕ n n ＝ equal
cmpℕ-self zero = refl
cmpℕ-self (suc n) = cmpℕ-self n

cmpℕ-trans-less : (m n k : ℕ) →
  cmpℕ m n ＝ less → cmpℕ n k ＝ less → cmpℕ m k ＝ less
cmpℕ-trans-less zero (suc n) (suc k) m<n n<k = refl
cmpℕ-trans-less (suc m) (suc n) (suc k) m<n n<k =
  cmpℕ-trans-less m n k m<n n<k

cmpℕ<zero-impossible : (n : ℕ) → ¬ (cmpℕ n zero ＝ less)
cmpℕ<zero-impossible zero p = equal≢less p
cmpℕ<zero-impossible (suc n) p = greater≢less p

------------------------------------------------------------------------
-- The comparison of positive naturals

cmp⁺-flip : (m n : ℕ⁺) → cmp⁺ n m ＝ flipTri (cmp⁺ m n)
cmp⁺-flip (1+ m) (1+ n) = cmpℕ-flip m n

cmp⁺-equal⇒≡ : (m n : ℕ⁺) → cmp⁺ m n ＝ equal → m ＝ n
cmp⁺-equal⇒≡ (1+ m) (1+ n) p = ap 1+_ (cmpℕ-equal⇒≡ m n p)

cmp⁺-self : (n : ℕ⁺) → cmp⁺ n n ＝ equal
cmp⁺-self (1+ n) = cmpℕ-self n

cmp⁺-trans-less : (m n k : ℕ⁺) →
  cmp⁺ m n ＝ less → cmp⁺ n k ＝ less → cmp⁺ m k ＝ less
cmp⁺-trans-less (1+ m) (1+ n) (1+ k) m<n n<k =
  cmpℕ-trans-less m n k m<n n<k

cmp⁺-less-respʳ-equal : (m n k : ℕ⁺) →
  cmp⁺ m n ＝ less → cmp⁺ n k ＝ equal → cmp⁺ m k ＝ less
cmp⁺-less-respʳ-equal m n k m<n n=k =
  transport (λ x → cmp⁺ m x ＝ less) (cmp⁺-equal⇒≡ n k n=k) m<n

cmp⁺-less-respˡ-equal : (m n k : ℕ⁺) →
  cmp⁺ m n ＝ equal → cmp⁺ n k ＝ less → cmp⁺ m k ＝ less
cmp⁺-less-respˡ-equal m n k m=n n<k =
  transport (λ x → cmp⁺ x k ＝ less) (cmp⁺-equal⇒≡ m n m=n ⁻¹) n<k

cmp⁺-equal-trans : (m n k : ℕ⁺) →
  cmp⁺ m n ＝ equal → cmp⁺ n k ＝ equal → cmp⁺ m k ＝ equal
cmp⁺-equal-trans m n k m=n n=k =
  transport (λ x → cmp⁺ m x ＝ equal)
    (cmp⁺-equal⇒≡ m n m=n ∙ cmp⁺-equal⇒≡ n k n=k) (cmp⁺-self m)

cmp⁺<one-impossible : (n : ℕ⁺) → ¬ (cmp⁺ n one⁺ ＝ less)
cmp⁺<one-impossible (1+ n) p = cmpℕ<zero-impossible n p

cmp⁺-less⇒pred<ℕᶜ : {m n : ℕ⁺} → m <⁺ᶜ n → pred m <ℕᶜ pred n
cmp⁺-less⇒pred<ℕᶜ {1+ m} {1+ n} p = p

------------------------------------------------------------------------
-- Trichotomy

-- An answer of `cmpℕ m n`, with the identification that produced it, gives the
-- case of the trichotomy.

trichotomy-from-comparison : (m n : ℕ) (t : Tri) → cmpℕ m n ＝ t →
  Trichotomy _＝_ _<ℕᶜ_ m n
trichotomy-from-comparison m n less e = inl e
trichotomy-from-comparison m n equal e = inr (inl (cmpℕ-equal⇒≡ m n e))
trichotomy-from-comparison m n greater e =
  inr (inr (cmpℕ-flip m n ∙ ap flipTri e))

cmpℕᶜ : (m n : ℕ) → Trichotomy _＝_ _<ℕᶜ_ m n
cmpℕᶜ m n = trichotomy-from-comparison m n (cmpℕ m n) refl

------------------------------------------------------------------------
-- Successors and maxima

<ℕᶜ-suc : (n : ℕ) → n <ℕᶜ suc n
<ℕᶜ-suc zero = refl
<ℕᶜ-suc (suc n) = <ℕᶜ-suc n

<ℕᶜ-suc-split : (m r : ℕ) → m <ℕᶜ suc r → (m <ℕᶜ r) ⊎ (m ＝ r)
<ℕᶜ-suc-split zero zero p = inr refl
<ℕᶜ-suc-split zero (suc r) p = inl refl
<ℕᶜ-suc-split (suc m) zero p = 𝟘-elim (cmpℕ<zero-impossible m p)
<ℕᶜ-suc-split (suc m) (suc r) p =
  cases inl (λ e → inr (ap suc e)) (<ℕᶜ-suc-split m r p)

<ℕᶜ-suc-⊔ˡ : (m n : ℕ) → m <ℕᶜ suc (m ⊔ℕ n)
<ℕᶜ-suc-⊔ˡ zero n = refl
<ℕᶜ-suc-⊔ˡ (suc m) zero = <ℕᶜ-suc m
<ℕᶜ-suc-⊔ˡ (suc m) (suc n) = <ℕᶜ-suc-⊔ˡ m n

<ℕᶜ-suc-⊔ʳ : (m n : ℕ) → n <ℕᶜ suc (m ⊔ℕ n)
<ℕᶜ-suc-⊔ʳ zero zero = refl
<ℕᶜ-suc-⊔ʳ zero (suc n) = <ℕᶜ-suc n
<ℕᶜ-suc-⊔ʳ (suc m) zero = refl
<ℕᶜ-suc-⊔ʳ (suc m) (suc n) = <ℕᶜ-suc-⊔ʳ m n

≤ℕᶜ-refl : {a : ℕ} → a ≤ℕᶜ a
≤ℕᶜ-refl = inr refl

≤ℕᶜ-⊔ˡ : (a b : ℕ) → a ≤ℕᶜ (a ⊔ℕ b)
≤ℕᶜ-⊔ˡ a b = <ℕᶜ-suc-split a (a ⊔ℕ b) (<ℕᶜ-suc-⊔ˡ a b)

≤ℕᶜ-⊔ʳ : (a b : ℕ) → b ≤ℕᶜ (a ⊔ℕ b)
≤ℕᶜ-⊔ʳ a b = <ℕᶜ-suc-split b (a ⊔ℕ b) (<ℕᶜ-suc-⊔ʳ a b)

------------------------------------------------------------------------
-- Transitivity

<ℕᶜ-trans : (a b c : ℕ) → a <ℕᶜ b → b <ℕᶜ c → a <ℕᶜ c
<ℕᶜ-trans a b c a<b b<c = cmpℕ-trans-less a b c a<b b<c

≤ℕᶜ-trans : (a b c : ℕ) → a ≤ℕᶜ b → b ≤ℕᶜ c → a ≤ℕᶜ c
≤ℕᶜ-trans a b c (inl a<b) (inl b<c) = inl (<ℕᶜ-trans a b c a<b b<c)
≤ℕᶜ-trans a b c (inl a<b) (inr e) =
  inl (transport (λ x → a <ℕᶜ x) e a<b)
≤ℕᶜ-trans a b c (inr e) b≤c = transport (λ x → x ≤ℕᶜ c) (e ⁻¹) b≤c

<ℕᶜ-resp-≤ : (a b c : ℕ) → a <ℕᶜ b → b ≤ℕᶜ c → a <ℕᶜ c
<ℕᶜ-resp-≤ a b c a<b (inl b<c) = <ℕᶜ-trans a b c a<b b<c
<ℕᶜ-resp-≤ a b c a<b (inr e) = transport (λ x → a <ℕᶜ x) e a<b

⊔-monoʳ-≤ℕᶜ : (a b c : ℕ) → b ≤ℕᶜ c → (a ⊔ℕ b) ≤ℕᶜ (a ⊔ℕ c)
⊔-monoʳ-≤ℕᶜ a b c (inr e) = inr (ap (a ⊔ℕ_) e)
⊔-monoʳ-≤ℕᶜ zero b c (inl b<c) = inl b<c
⊔-monoʳ-≤ℕᶜ (suc a) zero zero (inl ())
⊔-monoʳ-≤ℕᶜ (suc a) zero (suc c) (inl b<c) =
  cases inl (λ e → inr (ap suc e)) (≤ℕᶜ-⊔ˡ a c)
⊔-monoʳ-≤ℕᶜ (suc a) (suc b) zero (inl ())
⊔-monoʳ-≤ℕᶜ (suc a) (suc b) (suc c) (inl b<c) =
  cases inl (λ e → inr (ap suc e)) (⊔-monoʳ-≤ℕᶜ a b c (inl b<c))

------------------------------------------------------------------------
-- The structural order

cmpℕ-less⇒<ℕˢ : {m n : ℕ} → m <ℕᶜ n → m <ℕˢ n
cmpℕ-less⇒<ℕˢ {zero} {suc n} p = s≤s z≤n
cmpℕ-less⇒<ℕˢ {suc m} {suc n} p = s≤s (cmpℕ-less⇒<ℕˢ {m} {n} p)

<ℕˢ⇒cmpℕ-less : {m n : ℕ} → m <ℕˢ n → m <ℕᶜ n
<ℕˢ⇒cmpℕ-less {zero} {suc n} p = refl
<ℕˢ⇒cmpℕ-less {suc m} {suc n} (s≤s p) = <ℕˢ⇒cmpℕ-less {m} {n} p
