{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Nat.WellFounded where

-- The structural order `<ℕˢ` on ℕ is well-founded: everything below `n` is
-- accessible, by induction on `n`, since a point below a point below `suc n`
-- lies below `n` (`<ℕˢ-accessible-below`). The computational orders `<ℕᶜ` on ℕ
-- and `<⁺ᶜ` on the positive naturals are well-founded with it, the first as a
-- subrelation, the second through the predecessors
-- (`1+-preserves-accessibility`). The order itself needs no induction
-- principle, so this is kept apart from `SPT.Foundation.Nat.Order`.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Accessibility using
  (is-accessible; acc; is-well-founded)
open import SPT.Cubical.Foundation.WellFounded.Subrelation using
  (subrelations-are-well-founded)
open import SPT.Cubical.Foundation.Nat.Order using
  (_<ℕᶜ_; _<⁺ᶜ_; ℕ⁺; 1+_; pred; cmpℕ-less⇒<ℕˢ)

------------------------------------------------------------------------
-- Properties

<ℕˢ-accessible-below : (n m : ℕ) → m <ℕˢ n → is-accessible _<ℕˢ_ m
<ℕˢ-accessible-below zero m ()
<ℕˢ-accessible-below (suc n) m (s≤s m≤n) =
  acc (λ k k<m → <ℕˢ-accessible-below n k (≤ℕˢ-trans k<m m≤n))

wfℕˢ : is-well-founded _<ℕˢ_
wfℕˢ n = acc (<ℕˢ-accessible-below n)

wfℕᶜ : is-well-founded _<ℕᶜ_
wfℕᶜ = subrelations-are-well-founded cmpℕ-less⇒<ℕˢ wfℕˢ

1+-preserves-accessibility : (n : ℕ) → is-accessible _<ℕᶜ_ n →
  is-accessible _<⁺ᶜ_ (1+ n)
1+-preserves-accessibility n (acc smaller) =
  acc (λ m m<n →
    1+-preserves-accessibility (pred m) (smaller (pred m) m<n))

wf⁺ᶜ : is-well-founded _<⁺ᶜ_
wf⁺ᶜ (1+ n) = 1+-preserves-accessibility n (wfℕᶜ n)
