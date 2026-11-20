{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Realization.Discriminator where

-- Decoding by conversion at a closed description. The reflector is the
-- induction–recursive closure of each operator (`Code`, `interpret`,
-- `closure`, `reflector`), as in Mahlo.Relative: a reflector whose
-- names hold by refl, and the only induction–recursion of this folder. For
-- the closed description of a universe with ℕ, Π and identity types, the
-- type built from it by the smallness principle satisfies its decoding
-- equation by refl at every constructor, through the frontier, the family
-- extension and σ after δ (`naturals-β`, `products-β`, `identities-β`).

open import SPT.Base
import SPT.Mahlo.Ambient as Ambient
import SPT.Mahlo.Specification as Specification

open import SPT.IR.Description using (Desc; ι; σ; δ)
import SPT.Mahlo.DS.Ambient as Reflection
open import SPT.IR.Smallness using (Smallness; G; t; make)

------------------------------------------------------------------------
-- The induction–recursive closure of an operator

mutual
  data Code {ℓ : Level} (Ψ : Ambient.Operator ℓ) : Set ℓ where
    empty unit two natural : Code Ψ
    product sum tree result : (a : Code Ψ) → (interpret Ψ a → Code Ψ) → Code Ψ
    identity : (a : Code Ψ) → interpret Ψ a → interpret Ψ a → Code Ψ
    branch :
      (a : Code Ψ) (b : interpret Ψ a → Code Ψ)
      → pr₁ (Ψ (interpret Ψ a , (λ x → interpret Ψ (b x)))) → Code Ψ

  interpret : {ℓ : Level} (Ψ : Ambient.Operator ℓ) → Code Ψ → Set ℓ
  interpret {ℓ} Ψ empty = Specification.Formers.empty (Ambient.formers ℓ)
  interpret {ℓ} Ψ unit = Specification.Formers.unit (Ambient.formers ℓ)
  interpret {ℓ} Ψ two = Specification.Formers.two (Ambient.formers ℓ)
  interpret {ℓ} Ψ natural =
    Specification.Formers.natural (Ambient.formers ℓ)
  interpret {ℓ} Ψ (product a b) =
    Specification.Formers.product (Ambient.formers ℓ)
      (interpret Ψ a , (λ x → interpret Ψ (b x)))
  interpret {ℓ} Ψ (sum a b) =
    Specification.Formers.sum (Ambient.formers ℓ)
      (interpret Ψ a , (λ x → interpret Ψ (b x)))
  interpret {ℓ} Ψ (tree a b) =
    Specification.Formers.tree (Ambient.formers ℓ)
      (interpret Ψ a , (λ x → interpret Ψ (b x)))
  interpret {ℓ} Ψ (identity a x y) =
    Specification.Formers.identity (Ambient.formers ℓ) (interpret Ψ a) x y
  interpret Ψ (result a b) =
    pr₁ (Ψ (interpret Ψ a , (λ x → interpret Ψ (b x))))
  interpret Ψ (branch a b y) =
    pr₂ (Ψ (interpret Ψ a , (λ x → interpret Ψ (b x)))) y

closure :
  {ℓ : Level} (Ψ : Ambient.Operator ℓ)
  → Specification.Closure (Ambient.formers ℓ) Ψ (Code Ψ)
closure Ψ = record
  { interpret = interpret Ψ
  ; empty = empty , refl
  ; unit = unit , refl
  ; two = two , refl
  ; natural = natural , refl
  ; product = λ F → product (pr₁ F) (pr₂ F) , refl
  ; sum = λ F → sum (pr₁ F) (pr₂ F) , refl
  ; tree = λ F → tree (pr₁ F) (pr₂ F) , refl
  ; identity = λ a x y → identity a x y , refl
  ; inner = λ F → result (pr₁ F) (pr₂ F) , (λ y → branch (pr₁ F) (pr₂ F) y)
  ; inner-β = λ F → refl
  }

reflector : (ℓ : Level) → Specification.Mahlo (Ambient.formers ℓ)
reflector ℓ = record
  { reflect = λ Ψ → record { carrier = Code Ψ ; closure = closure Ψ } }

------------------------------------------------------------------------
-- A closed description and its decoding equations

-- The universe has ℕ; Π, whose second arity is the decoding of its first
-- recursive argument; and identity types over a decoded arity.

data Former : Set where
  naturals products identities : Former

branches : Former → Desc {s = lzero} Set
branches naturals = ι ℕ
branches products =
  δ (Lift lzero 𝟙)
    (λ A → δ (A (lift ⋆)) (λ B → ι ((x : A (lift ⋆)) → B x)))
branches identities =
  δ (Lift lzero 𝟙)
    (λ A → σ (A (lift ⋆)) (λ x → σ (A (lift ⋆)) (λ y → ι (x ＝ y))))

universe : Desc {s = lzero} Set
universe = σ Former branches

small : Smallness lzero
small = Reflection.smallness (reflector lzero)

naturals-β : t small universe (make small universe (naturals , lift ⋆)) ＝ ℕ
naturals-β = refl

products-β :
  (A : Lift lzero 𝟙 → G small universe)
  (B : t small universe (A (lift ⋆)) → G small universe)
  → t small universe
      (make small universe (products , (A , (B , lift ⋆))))
    ＝ ((x : t small universe (A (lift ⋆))) → t small universe (B x))
products-β A B = refl

identities-β :
  (A : Lift lzero 𝟙 → G small universe)
  (x y : t small universe (A (lift ⋆)))
  → t small universe
      (make small universe (identities , (A , (x , (y , lift ⋆)))))
    ＝ (x ＝ y)
identities-β A x y = refl
