{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Hedberg where

-- Hedberg's theorem: a type with decidable equality is a set
-- (`decidable-equality-gives-set`), so ℕ and 𝟚 are sets (`ℕ-is-set`,
-- `𝟚-is-set`). A decision
-- of x ＝ y gives an endomap of x ＝ y that is constant
-- (`decision-path-is-constant`), and every identification is recovered
-- from its image (`decision-path-cancels`), so any two agree.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Propositions using (is-set)

module _ {ℓ : Level} {A : Set ℓ} (d : has-decidable-equality A) where

  -- The identification the decision gives, whatever identification is in
  -- hand.
  decision-path : {x y : A} → x ＝ y → x ＝ y
  decision-path {x} {y} p = cases (λ e → e) (λ n → 𝟘-elim (n p)) (d x y)

  decision-path-is-constant : {x y : A} (p q : x ＝ y) →
    decision-path p ＝ decision-path q
  decision-path-is-constant {x} {y} p q with d x y
  ... | inl e = refl
  ... | inr n = 𝟘-elim (n p)

  decision-path-cancels : {x y : A} (p : x ＝ y) →
    decision-path refl ⁻¹ ∙ decision-path p ＝ p
  decision-path-cancels refl = left-inverse (decision-path refl)

  decidable-equality-gives-set : is-set A
  decidable-equality-gives-set x y p q =
    decision-path-cancels p ⁻¹ ∙
    (ap (λ r → decision-path refl ⁻¹ ∙ r) (decision-path-is-constant p q) ∙
     decision-path-cancels q)

ℕ-is-set : is-set ℕ
ℕ-is-set = decidable-equality-gives-set ℕ-has-decidable-equality

𝟚-is-set : is-set 𝟚
𝟚-is-set = decidable-equality-gives-set 𝟚-has-decidable-equality
