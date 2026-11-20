{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Residence.Adjoined.Connectives where

-- Negation and disjunction of generated Tarski names use products with
-- empty values and sums over two. decided names the disjunction of a
-- lower name with its negation; excluded-middle takes their product over
-- every lower name. These are names, without any inhabitance hypothesis.

open import SPT.Base
open import SPT.Mahlo.Residence.Adjoined using
  (Name; empty; two; product; sum; lifted; below)

module _ {ℓ : Level} (L : Set ℓ) (D : L → Set ℓ) (I : Set (lsuc ℓ))
  (E : I → Set ℓ) where

  negation : Name L D I E → Name L D I E
  negation a = product a (λ x → empty)

  disjunction : Name L D I E → Name L D I E → Name L D I E
  disjunction a b =
    sum two (λ c → two-elim (λ x → Name L D I E) a b (lower c))

  decided : L → Name L D I E
  decided l = disjunction (lifted l) (negation (lifted l))

  excluded-middle : Name L D I E
  excluded-middle = product below decided
