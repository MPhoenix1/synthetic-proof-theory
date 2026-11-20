{-# OPTIONS --safe --without-K #-}

module SPT.IR.Indexed.General.Initiality.Discriminator where

-- Initiality at the counter of IR.Indexed.General.Discriminator,
-- whose step lands at a computed index. Counting reads the hypothesis at
-- the step's one child, so its methods are congruent with no
-- extensionality, and every valuation with its equations is the count
-- (`count-unique`); so is the decoding (`decoding-is-count`). The count
-- lies strictly below an induction counting a step twice, at the strict
-- order, which is not reflexive (`count-below`), and fusion carries it
-- along the successor (`successor-fusion`).

open import SPT.Base

open import SPT.IR.Indexed using (U; value)
open import SPT.IR.General using (Method; ind)
open import SPT.IR.Indexed.General using (universal; universal-computation)
open import SPT.IR.Indexed.General.Discriminator using (counting; count)
open import SPT.IR.Description.Indexed.Counter using (counter)
open import SPT.IR.General.Initiality using
  ( Relational; ind-rel; Congruent; Homomorphic; ind-unique
  ; ind-homomorphic; Carries; ind-fusion)
open import SPT.IR.Indexed.General.Initiality using (universal-initiality)
open import SPT.IR.Description.Indexed using (general)

------------------------------------------------------------------------
-- The count is the only valuation with its equations

-- Agreement at a step is agreement at its one child, which is all that
-- counting reads.

count-congruent : Congruent (universal counter) (λ i u → ℕ) counting
count-congruent (₀ , x) h k r = refl
count-congruent (₁ , j , g , x) (h , h′) (k , k′) (r , r′) = ap suc (r ⋆)

count-equations : Homomorphic (universal counter) (λ i u → ℕ) count counting
count-equations =
  ind-homomorphic (universal counter) (λ i u → ℕ)
    (universal-computation counter (λ i u → ℕ)) counting

count-unique :
  (v : (i : 𝟚) → U (general counter) i → ℕ)
  → Homomorphic (universal counter) (λ i u → ℕ) v counting
  → (i : 𝟚) (u : U (general counter) i) → v i u ＝ count i u
count-unique v equations =
  ind-unique (universal counter) (universal-initiality counter) (λ i u → ℕ) v
    counting count-congruent equations

-- The decoding satisfies counting's equations at both constructors, so it
-- is the count at every element.

decoding-equations :
  Homomorphic (universal counter) (λ i u → ℕ) (value (general counter))
    counting
decoding-equations (₀ , x) = refl
decoding-equations (₁ , j , g , x) = refl

decoding-is-count :
  (i : 𝟚) (u : U (general counter) i)
  → value (general counter) i u ＝ count i u
decoding-is-count =
  count-unique (value (general counter)) decoding-equations

------------------------------------------------------------------------
-- The count lies strictly below a second induction

-- `twice` counts the seed as one and a step as two more than its child.

twice : Method (universal counter) (λ i u → ℕ)
twice (₀ , x) h = suc zero
twice (₁ , j , g , x) (k , h) = suc (suc (k ⋆))

Below : (i : 𝟚) (u : U (general counter) i) → ℕ → ℕ → Set
Below i u y z = y <ℕˢ z

related :
  Relational (universal counter) (λ i u → ℕ) (λ i u → ℕ) Below counting
    twice
related (₀ , x) h k r = s≤s z≤n
related (₁ , j , g , x) (h , h′) (k , k′) (r , r′) =
  s≤s (≤ℕˢ-suc (r ⋆))

count-below :
  (i : 𝟚) (u : U (general counter) i)
  → count i u <ℕˢ ind (universal counter) (λ i u → ℕ) twice i u
count-below =
  ind-rel (universal counter) (universal-initiality counter) (λ i u → ℕ)
    (λ i u → ℕ) Below counting twice
    (universal-computation counter (λ i u → ℕ)) related

------------------------------------------------------------------------
-- Fusion along the successor

-- The successor carries counting to `shifted`, which counts the seed as
-- one; the successor of the count is the induction at `shifted`.

successor : (i : 𝟚) (u : U (general counter) i) → ℕ → ℕ
successor i u n = suc n

shifted : Method (universal counter) (λ i u → ℕ)
shifted (₀ , x) h = suc zero
shifted (₁ , j , g , x) (k , h) = suc (k ⋆)

shifted-congruent : Congruent (universal counter) (λ i u → ℕ) shifted
shifted-congruent (₀ , x) h k r = refl
shifted-congruent (₁ , j , g , x) (h , h′) (k , k′) (r , r′) = ap suc (r ⋆)

carries :
  Carries (universal counter) (λ i u → ℕ) (λ i u → ℕ) successor counting
    shifted
carries (₀ , x) h = refl
carries (₁ , j , g , x) (k , h) = refl

successor-fusion :
  (i : 𝟚) (u : U (general counter) i)
  → suc (count i u) ＝ ind (universal counter) (λ i u → ℕ) shifted i u
successor-fusion =
  ind-fusion (universal counter) (universal-initiality counter) (λ i u → ℕ)
    (λ i u → ℕ) successor (universal-computation counter (λ i u → ℕ))
    counting shifted shifted-congruent carries
