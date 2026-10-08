{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.Nat.WellFounded where

-- Well-foundedness of the computational orders on ℕ and ℕ⁺ of Nat.Order,
-- obtained from the standard library's well-foundedness of ℕ.  It is kept
-- apart from Nat.Order so that the order itself needs no induction
-- principle.

open import Data.Nat using (ℕ)
open import Data.Nat.Base using () renaming (_<_ to _<ℕˢ_)
import Data.Nat.Induction as NatInd
import Induction.WellFounded as StdWF

open import SPT.Cubical.Core.WellFounded public
open import SPT.Cubical.Core.Nat.Order public
open import SPT.Cubical.Core.WellFounded.Subrelation using (subrel-wf)

stdAccℕ→Acc : {n : ℕ} → StdWF.Acc _<ℕˢ_ n → Acc _<ℕˢ_ n
stdAccℕ→Acc (StdWF.acc smaller) =
  acc λ m m<n → stdAccℕ→Acc (smaller {m} m<n)

wfℕˢ : WellFounded _<ℕˢ_
wfℕˢ n = stdAccℕ→Acc (NatInd.<-wellFounded n)

wfℕᶜ : WellFounded _<ℕᶜ_
wfℕᶜ = subrel-wf cmpℕ-less⇒<ℕˢ wfℕˢ

wf⁺ᶜ : WellFounded _<⁺ᶜ_
wf⁺ᶜ (1+ n) = go n (wfℕᶜ n)
  where
    go : (n : ℕ) → Acc _<ℕᶜ_ n → Acc _<⁺ᶜ_ (1+ n)
    go n (acc smaller) =
      acc λ where
        (1+ m) m<n →
          go m (smaller m m<n)
