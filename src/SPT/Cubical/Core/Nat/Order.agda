{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.Nat.Order where

-- A computational order on ℕ and on the positive naturals ℕ⁺: a comparison
-- function into three answers, `m <ℕᶜ n` as the equation `cmpℕ m n ≡ less`,
-- and its trichotomy, successor, maximum and transitivity laws.

open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Data.Nat.Base using (z≤n; s≤s) renaming (_<_ to _<ℕˢ_)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; sym; trans)
open import Relation.Nullary.Negation using (¬_)


-- The three answers of a comparison.  Lemmas below connect each answer
-- to the corresponding relation between the compared numbers.
data Tri : Set where
  less greater equal : Tri

-- Distinct answers are unequal.
less≢equal : {A : Set} → less ≡ equal → A
less≢equal ()

greater≢equal : {A : Set} → greater ≡ equal → A
greater≢equal ()

equal≢less : {A : Set} → equal ≡ less → A
equal≢less ()

equal≢greater : {A : Set} → equal ≡ greater → A
equal≢greater ()

greater≢less : {A : Set} → greater ≡ less → A
greater≢less ()

less≢greater : {A : Set} → less ≡ greater → A
less≢greater ()

-- Reversing a comparison swaps less and greater and leaves equal alone.
flipTri : Tri → Tri
flipTri less = greater
flipTri greater = less
flipTri equal = equal

-- Comparison of natural numbers.
cmpℕ : ℕ → ℕ → Tri
cmpℕ zero zero = equal
cmpℕ zero (suc n) = less
cmpℕ (suc m) zero = greater
cmpℕ (suc m) (suc n) = cmpℕ m n

-- Comparing naturals in the opposite order flips the result.
cmpℕ-flip : (m n : ℕ) → cmpℕ n m ≡ flipTri (cmpℕ m n)
cmpℕ-flip zero zero = refl
cmpℕ-flip zero (suc n) = refl
cmpℕ-flip (suc m) zero = refl
cmpℕ-flip (suc m) (suc n) = cmpℕ-flip m n

-- If the natural-number comparison returns equal, the inputs are
-- propositionally equal.
cmpℕ-equal⇒≡ : (m n : ℕ) → cmpℕ m n ≡ equal → m ≡ n
cmpℕ-equal⇒≡ zero zero refl = refl
cmpℕ-equal⇒≡ zero (suc n) ()
cmpℕ-equal⇒≡ (suc m) zero ()
cmpℕ-equal⇒≡ (suc m) (suc n) p =
  cong suc (cmpℕ-equal⇒≡ m n p)

-- Comparing a natural with itself computes to equal.
cmpℕ-self : (n : ℕ) → cmpℕ n n ≡ equal
cmpℕ-self zero = refl
cmpℕ-self (suc n) = cmpℕ-self n

-- Transitivity of less for natural numbers.
cmpℕ-trans-less :
  (m n k : ℕ) →
  cmpℕ m n ≡ less →
  cmpℕ n k ≡ less →
  cmpℕ m k ≡ less
cmpℕ-trans-less zero (suc n) (suc k) m<n n<k = refl
cmpℕ-trans-less (suc m) (suc n) (suc k) m<n n<k =
    cmpℕ-trans-less m n k m<n n<k

-- No natural number is computationally less than zero.
cmpℕ<zero-impossible : (n : ℕ) → ¬ (cmpℕ n zero ≡ less)
cmpℕ<zero-impossible zero p = equal≢less p
cmpℕ<zero-impossible (suc n) p = greater≢less p

-- Positive naturals, represented by their predecessor: `1+ n` is n + 1.
record ℕ⁺ : Set where
  constructor 1+_
  field
    pred : ℕ

open ℕ⁺ public

-- The positive naturals one and two.
one⁺ : ℕ⁺
one⁺ = 1+ 0

two⁺ : ℕ⁺
two⁺ = 1+ 1

-- Positive naturals compare by comparing their predecessors.
cmp⁺ : ℕ⁺ → ℕ⁺ → Tri
cmp⁺ (1+ m) (1+ n) = cmpℕ m n

cmp⁺-flip : (m n : ℕ⁺) → cmp⁺ n m ≡ flipTri (cmp⁺ m n)
cmp⁺-flip (1+ m) (1+ n) = cmpℕ-flip m n

cmp⁺-equal⇒≡ : (m n : ℕ⁺) → cmp⁺ m n ≡ equal → m ≡ n
cmp⁺-equal⇒≡ (1+ m) (1+ n) p =
  cong 1+_ (cmpℕ-equal⇒≡ m n p)

-- Comparing a positive natural with itself computes to equal.
cmp⁺-self : (n : ℕ⁺) → cmp⁺ n n ≡ equal
cmp⁺-self (1+ n) = cmpℕ-self n

-- Transitivity of less for positive naturals.
cmp⁺-trans-less :
  (m n k : ℕ⁺) →
  cmp⁺ m n ≡ less →
  cmp⁺ n k ≡ less →
  cmp⁺ m k ≡ less
cmp⁺-trans-less (1+ pred₁) (1+ pred₂) (1+ pred₃) m<n n<k =
    cmpℕ-trans-less pred₁ pred₂ pred₃ m<n n<k

-- If m < n and n = k, then m < k.
cmp⁺-less-respʳ-equal :
  (m n k : ℕ⁺) →
  cmp⁺ m n ≡ less →
  cmp⁺ n k ≡ equal →
  cmp⁺ m k ≡ less
cmp⁺-less-respʳ-equal m n k m<n n=k
  rewrite sym (cmp⁺-equal⇒≡ n k n=k) = m<n

-- If m = n and n < k, then m < k.
cmp⁺-less-respˡ-equal :
  (m n k : ℕ⁺) →
  cmp⁺ m n ≡ equal →
  cmp⁺ n k ≡ less →
  cmp⁺ m k ≡ less
cmp⁺-less-respˡ-equal m n k m=n n<k
  rewrite cmp⁺-equal⇒≡ m n m=n = n<k

-- Transitivity of equality for positive-natural comparison.
cmp⁺-equal-trans :
  (m n k : ℕ⁺) →
  cmp⁺ m n ≡ equal →
  cmp⁺ n k ≡ equal →
  cmp⁺ m k ≡ equal
cmp⁺-equal-trans m n k m=n n=k
  rewrite cmp⁺-equal⇒≡ m n m=n
        | cmp⁺-equal⇒≡ n k n=k = cmp⁺-self k

-- No positive natural is computationally less than one.
cmp⁺<one-impossible : (n : ℕ⁺) → ¬ (cmp⁺ n one⁺ ≡ less)
cmp⁺<one-impossible (1+ n) p = cmpℕ<zero-impossible n p

_<ℕᶜ_ : ℕ → ℕ → Set
m <ℕᶜ n = cmpℕ m n ≡ less

cmpℕᶜ :
    (m n : ℕ)
  → m <ℕᶜ n
      ⊎ (m ≡ n
        ⊎ n <ℕᶜ m)
cmpℕᶜ m n with cmpℕ m n in comparison
... | less =
  inj₁ refl
... | equal =
  inj₂ (inj₁ (cmpℕ-equal⇒≡ m n comparison))
... | greater =
  inj₂
    (inj₂
      (trans
        (cmpℕ-flip m n)
        (cong flipTri comparison)))

<ℕᶜ-suc : (n : ℕ) → n <ℕᶜ suc n
<ℕᶜ-suc zero = refl
<ℕᶜ-suc (suc n) = <ℕᶜ-suc n

<ℕᶜ-suc-split :
    (m r : ℕ)
  → m <ℕᶜ suc r
  → (m <ℕᶜ r) ⊎ (m ≡ r)
<ℕᶜ-suc-split zero zero p = inj₂ refl
<ℕᶜ-suc-split zero (suc r) p = inj₁ refl
<ℕᶜ-suc-split (suc m) zero p =
  ⊥-elim (cmpℕ<zero-impossible m p)
<ℕᶜ-suc-split (suc m) (suc r) p
  with <ℕᶜ-suc-split m r p
... | inj₁ m<r = inj₁ m<r
... | inj₂ m≡r = inj₂ (cong suc m≡r)

<ℕᶜ-suc-⊔ˡ : (m n : ℕ) → m <ℕᶜ suc (m ⊔ n)
<ℕᶜ-suc-⊔ˡ zero n = refl
<ℕᶜ-suc-⊔ˡ (suc m) zero = <ℕᶜ-suc m
<ℕᶜ-suc-⊔ˡ (suc m) (suc n) = <ℕᶜ-suc-⊔ˡ m n

<ℕᶜ-suc-⊔ʳ : (m n : ℕ) → n <ℕᶜ suc (m ⊔ n)
<ℕᶜ-suc-⊔ʳ zero zero = refl
<ℕᶜ-suc-⊔ʳ zero (suc n) = <ℕᶜ-suc n
<ℕᶜ-suc-⊔ʳ (suc m) zero = refl
<ℕᶜ-suc-⊔ʳ (suc m) (suc n) = <ℕᶜ-suc-⊔ʳ m n

cmpℕ-less⇒<ℕˢ : ∀ {m n} → m <ℕᶜ n → m <ℕˢ n
cmpℕ-less⇒<ℕˢ {zero} {zero} ()
cmpℕ-less⇒<ℕˢ {zero} {suc n} p = s≤s z≤n
cmpℕ-less⇒<ℕˢ {suc m} {zero} ()
cmpℕ-less⇒<ℕˢ {suc m} {suc n} p =
  s≤s (cmpℕ-less⇒<ℕˢ {m} {n} p)

<ℕˢ⇒cmpℕ-less : ∀ {m n} → m <ℕˢ n → m <ℕᶜ n
<ℕˢ⇒cmpℕ-less {zero} {suc n} p = refl
<ℕˢ⇒cmpℕ-less {suc m} {suc n} (s≤s p) =
  <ℕˢ⇒cmpℕ-less {m} {n} p

_<⁺ᶜ_ : ℕ⁺ → ℕ⁺ → Set
m <⁺ᶜ n = cmp⁺ m n ≡ less

cmp⁺-less⇒pred<ℕᶜ : ∀ {m n} → m <⁺ᶜ n → pred m <ℕᶜ pred n
cmp⁺-less⇒pred<ℕᶜ {1+ m} {1+ n} p = p

_≤ℕᶜ_ : ℕ → ℕ → Set
m ≤ℕᶜ n = (m <ℕᶜ n) ⊎ (m ≡ n)

≤ℕᶜ-refl : ∀ {a} → a ≤ℕᶜ a
≤ℕᶜ-refl = inj₂ refl

≤ℕᶜ-⊔ˡ : (a b : ℕ) → a ≤ℕᶜ (a ⊔ b)
≤ℕᶜ-⊔ˡ a b =
  <ℕᶜ-suc-split a (a ⊔ b) (<ℕᶜ-suc-⊔ˡ a b)

≤ℕᶜ-⊔ʳ : (a b : ℕ) → b ≤ℕᶜ (a ⊔ b)
≤ℕᶜ-⊔ʳ a b =
  <ℕᶜ-suc-split b (a ⊔ b) (<ℕᶜ-suc-⊔ʳ a b)

<ℕᶜ-trans :
    ∀ {a b c}
  → a <ℕᶜ b
  → b <ℕᶜ c
  → a <ℕᶜ c
<ℕᶜ-trans {a} {b} {c} a<b b<c =
  cmpℕ-trans-less a b c a<b b<c

≤ℕᶜ-trans :
    ∀ {a b c}
  → a ≤ℕᶜ b
  → b ≤ℕᶜ c
  → a ≤ℕᶜ c
≤ℕᶜ-trans {a} {b} {c} (inj₁ a<b) (inj₁ b<c) =
  inj₁ (<ℕᶜ-trans {a} {b} {c} a<b b<c)
≤ℕᶜ-trans (inj₁ a<b) (inj₂ refl) = inj₁ a<b
≤ℕᶜ-trans (inj₂ refl) b≤c = b≤c

⊔-monoʳ-≤ℕᶜ :
    ∀ {a b c}
  → b ≤ℕᶜ c
  → (a ⊔ b) ≤ℕᶜ (a ⊔ c)
⊔-monoʳ-≤ℕᶜ (inj₂ refl) = ≤ℕᶜ-refl
⊔-monoʳ-≤ℕᶜ {a = zero} (inj₁ b<c) = inj₁ b<c
⊔-monoʳ-≤ℕᶜ
  {a = suc a} {b = zero} {c = zero}
  (inj₁ ())
⊔-monoʳ-≤ℕᶜ
  {a = suc a} {b = zero} {c = suc c}
  (inj₁ b<c)
  with ≤ℕᶜ-⊔ˡ a c
... | inj₁ a<a⊔c = inj₁ a<a⊔c
... | inj₂ a≡a⊔c = inj₂ (cong suc a≡a⊔c)
⊔-monoʳ-≤ℕᶜ
  {a = suc a} {b = suc b} {c = zero}
  (inj₁ ())
⊔-monoʳ-≤ℕᶜ
  {a = suc a} {b = suc b} {c = suc c}
  (inj₁ b<c)
  with ⊔-monoʳ-≤ℕᶜ {a = a} {b = b} {c = c} (inj₁ b<c)
... | inj₁ a⊔b<a⊔c = inj₁ a⊔b<a⊔c
... | inj₂ a⊔b≡a⊔c = inj₂ (cong suc a⊔b≡a⊔c)

<ℕᶜ-resp-≤ :
    ∀ {a b c}
  → a <ℕᶜ b
  → b ≤ℕᶜ c
  → a <ℕᶜ c
<ℕᶜ-resp-≤ {a} {b} {c} a<b (inj₁ b<c) =
  <ℕᶜ-trans {a} {b} {c} a<b b<c
<ℕᶜ-resp-≤ a<b (inj₂ b≡c) rewrite b≡c = a<b
