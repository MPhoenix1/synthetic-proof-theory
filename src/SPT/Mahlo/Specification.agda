{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Specification where

-- Resident reflection over a Tarski family `(C , D)` of codes `C` decoding to
-- types `D a`. A family of the parent is a code `a` with a code-valued map on
-- `D a`, and an operator maps families to families. `Formers` selects parent
-- codes: empty, unit, two, the natural numbers, products, sums and trees of
-- families, and identity types.
--
-- An interpretation `interpret : A → C` of a type `A` of level `ℓ` decodes `A`
-- (`Decode`), sends its families to families of the parent (`map`), and names a
-- code `c` by the points of `A` interpreted as `c` (`Name`). These are
-- functions of the interpretation, outside every record, so the fields of a
-- closure and each later use write them alike.
--
-- A closure of an operator `Ψ` on `A` is an interpretation that names, in `A`,
-- the selected formers of its own families and their images under `Ψ`:
--
--   inner-β F : map (inner F) ＝ Ψ (map F).
--
-- A reflection of `Ψ` is a parent code whose decoding carries a closure, and a
-- reflector (`Mahlo`) reflects every operator: the Mahlo rule. The decoding
-- laws of the formers are in `SPT.Mahlo.Decoding`.

open import SPT.Base

------------------------------------------------------------------------
-- Families and operators

module _ {κ ℓ : Level} {C : Set κ} (D : C → Set ℓ) where

  Family : Set (κ ⊔ ℓ)
  Family = Σ C (λ a → D a → C)

  Operator : Set (κ ⊔ ℓ)
  Operator = Family → Family

------------------------------------------------------------------------
-- Formers

record Formers {κ ℓ : Level} (C : Set κ) (D : C → Set ℓ) :
  Set (κ ⊔ ℓ) where
  field
    empty unit two natural : C
    product sum tree : Family D → C
    identity : (a : C) → D a → D a → C

------------------------------------------------------------------------
-- Interpretations

-- `Name interpret c` is the type of points of `A` interpreted as `c`.

module _ {κ ℓ : Level} {C : Set κ} {A : Set ℓ} (interpret : A → C) where

  Name : C → Set (κ ⊔ ℓ)
  Name c = Σ A (λ a → interpret a ＝ c)

module _ {κ ℓ : Level} {C : Set κ} (D : C → Set ℓ) {A : Set ℓ}
  (interpret : A → C) where

  Decode : A → Set ℓ
  Decode a = D (interpret a)

  map : Family Decode → Family D
  map (a , b) = interpret a , (λ x → interpret (b x))

------------------------------------------------------------------------
-- Closures

record Closure {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Formers C D) (Ψ : Operator D) (A : Set ℓ) : Set (κ ⊔ ℓ) where
  field
    interpret : A → C
    empty : Name interpret (Formers.empty Q)
    unit : Name interpret (Formers.unit Q)
    two : Name interpret (Formers.two Q)
    natural : Name interpret (Formers.natural Q)
    product : (F : Family (Decode D interpret)) →
      Name interpret (Formers.product Q (map D interpret F))
    sum : (F : Family (Decode D interpret)) →
      Name interpret (Formers.sum Q (map D interpret F))
    tree : (F : Family (Decode D interpret)) →
      Name interpret (Formers.tree Q (map D interpret F))
    identity : (a : A) (x y : Decode D interpret a) →
      Name interpret (Formers.identity Q (interpret a) x y)
    inner : Family (Decode D interpret) → Family (Decode D interpret)
    inner-β : (F : Family (Decode D interpret)) →
      map D interpret (inner F) ＝ Ψ (map D interpret F)

------------------------------------------------------------------------
-- Reflections and reflectors

record Reflection {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Formers C D) (Ψ : Operator D) : Set (κ ⊔ ℓ) where
  field
    carrier : C
    closure : Closure Q Ψ (D carrier)

record Mahlo {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Formers C D) : Set (κ ⊔ ℓ) where
  field
    reflect : (Ψ : Operator D) → Reflection Q Ψ
