{-# OPTIONS --safe --without-K #-}

module SPT.IR.Generated.Initiality.Discriminator where

-- Initiality at the raised fixed point of a closed description of leaves
-- and binary forks, the generated part of its identity algebra. Size
-- reads the hypotheses at both children of a fork, so its methods are
-- congruent with no extensionality, and every valuation with size's
-- equations is size (`size-unique`). Depth lies strictly below an
-- induction counting a fork twice, at the strict order, which is not
-- reflexive (`depth-below`). Fusion carries depth along the successor
-- (`successor-fusion`).

open import SPT.Base

open import SPT.IR.Algebra using (identity)
open import SPT.IR.Description using (Desc; ι; σ; δ)
open import SPT.IR.Generated using (G; make; Method; ind)
open import SPT.IR.Generated.Initiality using
  ( Relational; ind-rel; Congruent; Homomorphic; ind-unique
  ; ind-homomorphic; Carries; ind-fusion)

------------------------------------------------------------------------
-- Leaves and binary forks

-- ₀ ↦ a leaf decoding to 𝟙; ₁ ↦ two recursive inputs, decoding to the
-- product of their decodings.

shapes : 𝟚 → Desc {s = lzero} Set
shapes ₀ = ι 𝟙
shapes ₁ = δ 𝟚 (λ q → ι (q ₀ × q ₁))

trees : Desc {s = lzero} Set
trees = σ 𝟚 shapes

leaf : G (identity trees)
leaf = make (identity trees) (₀ , lift ⋆)

fork : (𝟚 → G (identity trees)) → G (identity trees)
fork f = make (identity trees) (₁ , (f , lift ⋆))

Count : G (identity trees) → Set
Count g = ℕ

------------------------------------------------------------------------
-- Size is the only valuation with its equations

-- A leaf has size one and a fork one more than its two children. Agreement
-- at a fork is agreement at both children, which is all that size reads.

size-step : Method (identity trees) Count
size-step (₀ , z) xs h = suc zero
size-step (₁ , (f , z)) xs h = suc (h (inl ₀) + h (inl ₁))

size : G (identity trees) → ℕ
size = ind (identity trees) Count size-step

size-congruent : Congruent (identity trees) Count size-step
size-congruent (₀ , z) xs h k r = refl
size-congruent (₁ , (f , z)) xs h k r =
  ap₂ (λ x y → suc (x + y)) (r (inl ₀)) (r (inl ₁))

size-equations : Homomorphic (identity trees) Count size size-step
size-equations = ind-homomorphic (identity trees) Count size-step

size-unique :
  (v : (g : G (identity trees)) → Count g)
  → Homomorphic (identity trees) Count v size-step
  → (g : G (identity trees)) → v g ＝ size g
size-unique v equations =
  ind-unique (identity trees) Count v size-step size-congruent equations

size-fork : size (fork (λ x → leaf)) ＝ suc (suc (suc zero))
size-fork = refl

------------------------------------------------------------------------
-- Depth lies strictly below a second induction

-- `twice` counts a leaf as one and a fork as two more than its first
-- child. The strict order is not reflexive.

depth-step : Method (identity trees) Count
depth-step (₀ , z) xs h = zero
depth-step (₁ , (f , z)) xs h = suc (h (inl ₀))

twice : Method (identity trees) Count
twice (₀ , z) xs h = suc zero
twice (₁ , (f , z)) xs h = suc (suc (h (inl ₀)))

Below : (g : G (identity trees)) → Count g → Count g → Set
Below g x y = x <ℕˢ y

related :
  Relational (identity trees) Count Count Below depth-step twice
related (₀ , z) xs h k r = s≤s z≤n
related (₁ , (f , z)) xs h k r = s≤s (≤ℕˢ-suc (r (inl ₀)))

depth-below :
  (g : G (identity trees))
  → ind (identity trees) Count depth-step g
    <ℕˢ ind (identity trees) Count twice g
depth-below =
  ind-rel (identity trees) Count Count Below depth-step twice related

------------------------------------------------------------------------
-- Fusion along the successor

-- The successor carries depth's methods to `shifted`, which counts a leaf
-- as one; the successor of depth is the induction at `shifted`.

successor : (g : G (identity trees)) → Count g → Count g
successor g n = suc n

shifted : Method (identity trees) Count
shifted (₀ , z) xs h = suc zero
shifted (₁ , (f , z)) xs h = suc (h (inl ₀))

shifted-congruent : Congruent (identity trees) Count shifted
shifted-congruent (₀ , z) xs h k r = refl
shifted-congruent (₁ , (f , z)) xs h k r = ap suc (r (inl ₀))

carries :
  Carries (identity trees) Count Count successor depth-step shifted
carries (₀ , z) xs h = refl
carries (₁ , (f , z)) xs h = refl

successor-fusion :
  (g : G (identity trees))
  → suc (ind (identity trees) Count depth-step g)
    ＝ ind (identity trees) Count shifted g
successor-fusion =
  ind-fusion (identity trees) Count Count successor depth-step shifted
    shifted-congruent carries
