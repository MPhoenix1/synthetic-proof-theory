{-# OPTIONS --safe --without-K #-}

module SPT.IR.Indexed.Initiality.Discriminator where

-- Initiality at the universe of IR.Indexed.Discriminator, whose sums
-- take a family of codes over a decoding. Depth reads only the first code
-- of a sum, so its methods are congruent with no extensionality, and every
-- valuation with depth's equations is depth (`depth-unique`). At the
-- strict order, which is not reflexive, depth lies below an induction
-- counting a sum twice (`depth-below`). Fusion carries depth along the
-- successor to an induction counting a base name as one
-- (`successor-fusion`).

open import SPT.Base

open import SPT.IR.Indexed using (U; Method; ind)
open import SPT.IR.Indexed.Discriminator using
  (universe; Depth; step; depth; unit; sum)
open import SPT.IR.Indexed.Initiality using
  ( Relational; ind-rel; Congruent; Homomorphic; ind-unique
  ; ind-homomorphic; Carries; ind-fusion)

------------------------------------------------------------------------
-- Depth is the only valuation with its equations

-- Agreement at a sum gives agreement at its first code, which is all that
-- depth reads; the hypotheses over the decoding are never compared, so no
-- extensionality is needed although they are functions.

depth-congruent : Congruent universe Depth step
depth-congruent i (₀ , n) h k r = refl
depth-congruent i (₁ , (a , f)) h k r = ap suc (lower (pr₁ (pr₂ r)))

depth-equations : Homomorphic universe Depth (ind universe Depth step) step
depth-equations = ind-homomorphic universe Depth step depth-congruent

depth-unique :
  (v : (i : 𝟙) (u : U universe i) → Depth i u)
  → Homomorphic universe Depth v step
  → (u : U universe ⋆) → v ⋆ u ＝ depth u
depth-unique v equations u =
  ind-unique universe Depth v step depth-congruent equations ⋆ u

------------------------------------------------------------------------
-- Depth lies strictly below a second induction

-- `twice` counts a base name as one and a sum as two more than its first
-- code. The strict order is not reflexive, and the fundamental theorem
-- asks only that the two methods' clauses be related.

Below : (i : 𝟙) (u : U universe i) → Depth i u → Depth i u → Set
Below i u x y = x <ℕˢ y

twice : Method universe Depth
twice i (₀ , n) h = suc zero
twice i (₁ , (a , f)) h = suc (suc (lower (pr₁ (pr₂ h))))

related : Relational universe Depth Depth Below step twice
related i (₀ , n) h k r = s≤s z≤n
related i (₁ , (a , f)) h k r = s≤s (≤ℕˢ-suc (lower (pr₁ (pr₂ r))))

depth-below :
  (u : U universe ⋆) → depth u <ℕˢ ind universe Depth twice ⋆ u
depth-below u = ind-rel universe Depth Depth Below step twice related ⋆ u

twice-sum :
  ind universe Depth twice ⋆ (sum unit (λ x → unit)) ＝ suc (suc (suc zero))
twice-sum = refl

------------------------------------------------------------------------
-- Fusion along the successor

-- The successor carries depth's methods to `shifted`, which counts a base
-- name as one and a sum as one more than its first code; the successor of
-- depth is the induction at `shifted`.

successor : (i : 𝟙) (u : U universe i) → Depth i u → Depth i u
successor i u n = suc n

shifted : Method universe Depth
shifted i (₀ , n) h = suc zero
shifted i (₁ , (a , f)) h = suc (lower (pr₁ (pr₂ h)))

shifted-congruent : Congruent universe Depth shifted
shifted-congruent i (₀ , n) h k r = refl
shifted-congruent i (₁ , (a , f)) h k r = ap suc (lower (pr₁ (pr₂ r)))

carries : Carries universe Depth Depth successor step shifted
carries i (₀ , n) h = refl
carries i (₁ , (a , f)) h = refl

successor-fusion :
  (u : U universe ⋆) → suc (depth u) ＝ ind universe Depth shifted ⋆ u
successor-fusion u =
  ind-fusion universe Depth Depth successor step shifted shifted-congruent
    carries ⋆ u
