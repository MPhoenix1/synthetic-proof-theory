{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.Mahlo.Specification where

-- Resident reflection over a Tarski family (C , D), as records.  A family
-- of the parent is a code a with a code-valued map on D a; an operator
-- maps families to families; Formers selects parent codes.  A closure of
-- Ψ on a type A of level ℓ interprets A in the codes and names, in A, the
-- selected formers of its own families and their images under Ψ:
--
--   inner-β F : map (inner F) = Ψ (map F).
--
-- A reflection of Ψ is a parent code whose decoding carries a closure,
-- and a reflector (Mahlo) reflects every operator: the Mahlo rule.  The
-- decoding laws of the formers are in Decoding.

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_)

private
  variable
    ℓ κ : Level

Family : {C : Set κ} → (C → Set ℓ) → Set (κ ⊔ ℓ)
Family {C = C} D = Σ C (λ a → D a → C)

Operator : {C : Set κ} → (C → Set ℓ) → Set (κ ⊔ ℓ)
Operator D = Family D → Family D

-- Selected parent codes; their decoding laws are in Decoding.
record Formers (C : Set κ) (D : C → Set ℓ) : Set (κ ⊔ ℓ) where
  field
    empty unit two natural : C
    product sum tree : Family D → C
    identity : (a : C) → D a → D a → C

-- A closure of Ψ on A: Name c is a point of A interpreted as c.
record Closure {C : Set κ} {D : C → Set ℓ}
  (Q : Formers C D) (Ψ : Operator D) (A : Set ℓ)
  : Set (κ ⊔ ℓ) where
  field
    interpret : A → C

  Decode : A → Set ℓ
  Decode a = D (interpret a)

  map : Family Decode → Family D
  map (a , b) = interpret a , λ x → interpret (b x)

  Name : C → Set (κ ⊔ ℓ)
  Name c = Σ A (λ a → interpret a ≡ c)

  field
    empty : Name (Formers.empty Q)
    unit : Name (Formers.unit Q)
    two : Name (Formers.two Q)
    natural : Name (Formers.natural Q)
    product : (F : Family Decode) → Name (Formers.product Q (map F))
    sum : (F : Family Decode) → Name (Formers.sum Q (map F))
    tree : (F : Family Decode) → Name (Formers.tree Q (map F))
    identity : (a : A) (x y : Decode a)
      → Name (Formers.identity Q (interpret a) x y)
    inner : Family Decode → Family Decode
    inner-β : (F : Family Decode) → map (inner F) ≡ Ψ (map F)

-- A reflection of Ψ: a parent code whose decoding carries a closure.
record Reflection {C : Set κ} {D : C → Set ℓ}
  (Q : Formers C D) (Ψ : Operator D) : Set (κ ⊔ ℓ) where
  field
    carrier : C
    closure : Closure Q Ψ (D carrier)

-- A reflector: a reflection of every operator.
record Mahlo {C : Set κ} {D : C → Set ℓ}
  (Q : Formers C D) : Set (κ ⊔ ℓ) where
  field
    reflect : (Ψ : Operator D) → Reflection Q Ψ
