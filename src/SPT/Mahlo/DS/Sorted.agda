{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Sorted where

-- The two-sorted family of small types and values of a type O (`Sort`): a
-- name is a small type or a value of O, decoded into an index type by the
-- type itself or by the empty type (`decode`). The formers act on the
-- types (`formers`). A family of names is a small type of indices with a
-- type or a value at each, so the Mahlo rule for this family
-- (Specification.Mahlo (formers ℓ O)) closes, for every operator on such
-- families, a small type of names of both sorts under the formers and the
-- operator. Descriptions with outputs in Sort ℓ O are induction–recursion
-- with outputs in O alongside types; for O empty the family is the
-- ambient one.

open import SPT.Base
open import SPT.Foundation.Tree.W using (W)
import SPT.Mahlo.Specification as Specification

Sort : {κ : Level} (ℓ : Level) → Set κ → Set (lsuc ℓ ⊔ κ)
Sort ℓ O = Set ℓ ⊎ O

decode : {κ : Level} (ℓ : Level) (O : Set κ) → Sort ℓ O → Set ℓ
decode ℓ O (inl A) = A
decode ℓ O (inr o) = Lift ℓ 𝟘

formers :
  {κ : Level} (ℓ : Level) (O : Set κ)
  → Specification.Formers (Sort ℓ O) (decode ℓ O)
formers ℓ O = record
  { empty = inl (Lift ℓ 𝟘)
  ; unit = inl (Lift ℓ 𝟙)
  ; two = inl (Lift ℓ 𝟚)
  ; natural = inl (Lift ℓ ℕ)
  ; product = λ F → inl ((x : decode ℓ O (pr₁ F)) → decode ℓ O (pr₂ F x))
  ; sum = λ F → inl (Σ (decode ℓ O (pr₁ F)) (λ x → decode ℓ O (pr₂ F x)))
  ; tree = λ F → inl (W (decode ℓ O (pr₁ F)) (λ x → decode ℓ O (pr₂ F x)))
  ; identity = λ a x y → inl (x ＝ y)
  }
