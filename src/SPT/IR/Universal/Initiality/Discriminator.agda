{-# OPTIONS --safe --without-K #-}

module SPT.IR.Universal.Initiality.Discriminator where

-- Initiality at the leaves and binary nodes of
-- IR.Universal.Discriminator, whose hypotheses at a node are one
-- function on the two children. Size reads it at both, so its methods are
-- congruent with no extensionality, and every valuation with size's
-- equations is size (`size-unique`). Depth, reading the first child, lies
-- strictly below size: the fundamental theorem at the strict order, which
-- is not reflexive (`depth-below-size`). Fusion carries depth along the
-- successor (`successor-fusion`).

open import SPT.Base

open import SPT.IR.Universal using (U; box; Method; ind)
open import SPT.IR.Universal.Discriminator using
  (γ; Depth; step; depth; node; plain)
open import SPT.IR.Universal.Initiality using
  ( Relational; ind-rel; Congruent; Homomorphic; ind-unique
  ; ind-homomorphic; Carries; ind-fusion)

------------------------------------------------------------------------
-- Size is the only valuation with its equations

-- A leaf has size one and a node one more than its two children. Agreement
-- at a node is agreement at each child, which is all that size reads.

size-step : Method γ Depth
size-step (box (₀ , b)) h = suc zero
size-step (box (₁ , box (f , b))) (h , rest) = suc (h ₀ + h ₁)

size : U γ → ℕ
size = ind γ Depth size-step

size-congruent : Congruent γ Depth size-step
size-congruent (box (₀ , b)) h k r = refl
size-congruent (box (₁ , box (f , b))) (h , rest) (k , rest′) (r , r′) =
  ap₂ (λ x y → suc (x + y)) (r ₀) (r ₁)

size-equations : Homomorphic γ Depth size size-step
size-equations = ind-homomorphic γ Depth size-step size-congruent

size-unique :
  (v : (u : U γ) → Depth u) → Homomorphic γ Depth v size-step
  → (u : U γ) → v u ＝ size u
size-unique v equations =
  ind-unique γ Depth v size-step size-congruent equations

size-node : size (node plain) ＝ suc (suc (suc zero))
size-node = refl

------------------------------------------------------------------------
-- Depth lies strictly below size

-- The strict order is not reflexive; the fundamental theorem asks only
-- that depth's and size's clauses be related at related children.

Below : (u : U γ) → Depth u → Depth u → Set
Below u x y = x <ℕˢ y

left-summand-below : (m n : ℕ) → m ≤ℕˢ m + n
left-summand-below zero n = z≤n
left-summand-below (suc m) n = s≤s (left-summand-below m n)

related : Relational γ Depth Depth Below step size-step
related (box (₀ , b)) h k r = s≤s z≤n
related (box (₁ , box (f , b))) (h , rest) (k , rest′) (r , r′) =
  s≤s (≤ℕˢ-trans (r ₀) (left-summand-below (k ₀) (k ₁)))

depth-below-size : (u : U γ) → depth u <ℕˢ size u
depth-below-size = ind-rel γ Depth Depth Below step size-step related

------------------------------------------------------------------------
-- Fusion along the successor

-- The successor carries depth's methods to `shifted`, which counts a leaf
-- as one; the successor of depth is the induction at `shifted`.

successor : (u : U γ) → Depth u → Depth u
successor u n = suc n

shifted : Method γ Depth
shifted (box (₀ , b)) h = suc zero
shifted (box (₁ , box (f , b))) (h , rest) = suc (h ₀)

shifted-congruent : Congruent γ Depth shifted
shifted-congruent (box (₀ , b)) h k r = refl
shifted-congruent (box (₁ , box (f , b))) (h , rest) (k , rest′) (r , r′) =
  ap suc (r ₀)

carries : Carries γ Depth Depth successor step shifted
carries (box (₀ , b)) h = refl
carries (box (₁ , box (f , b))) (h , rest) = refl

successor-fusion : (u : U γ) → suc (depth u) ＝ ind γ Depth shifted u
successor-fusion =
  ind-fusion γ Depth Depth successor step shifted shifted-congruent carries
