{-# OPTIONS --safe --without-K #-}

module SPT.IR.Algebra where

-- An algebra of a description γ: a carrier of a given level κ, a decoding,
-- and an operation on the shapes over the carrier (`Algebra`). Its law,
-- kept separate, says that the operation decodes to the output of each
-- shape (`Law`). The carrier level is a parameter: an algebra is small when
-- κ is the level of the arities. `identity` is the algebra on the outputs
-- themselves, at their own level, with its law by refl (`identity-β`); its
-- generated part is the raised fixed point of γ (Comparison).

open import SPT.Base

open import SPT.IR.Description using
  (Desc; indexed; Shape; Mark)

record Algebra {s j : Level} (κ : Level) {E : Set j} (γ : Desc {s = s} E) :
  Set (lsuc κ ⊔ s ⊔ j) where
  field
    K : Set κ
    value : K → E
    operation : Shape γ (indexed K value) → K

Law :
  {s κ j : Level} {E : Set j} {γ : Desc {s = s} E} → Algebra κ γ
  → Set (s ⊔ κ ⊔ j)
Law {γ = γ} M =
  (z : Shape γ (indexed (Algebra.K M) (Algebra.value M)))
  → Algebra.value M (Algebra.operation M z)
    ＝ Mark γ (indexed (Algebra.K M) (Algebra.value M)) z

identity : {s j : Level} {E : Set j} (γ : Desc {s = s} E) → Algebra j γ
identity {E = E} γ = record
  { K = E
  ; value = λ e → e
  ; operation = Mark γ (indexed E (λ e → e))
  }

identity-β : {s j : Level} {E : Set j} (γ : Desc {s = s} E)
  → Law (identity γ)
identity-β γ z = refl
