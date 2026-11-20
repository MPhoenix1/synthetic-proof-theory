{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Residence.Absorption where

-- Least closures and absorbed reflections over a Tarski family. A closure
-- is least when every motive with methods at its codes has a section
-- computing at each code (`Methods`, `Induction`). A small least closure
-- has its carrier at the level of the decodings (`Small-Least`). An
-- absorbed reflection is a reflection whose closure is least (`Absorbed`);
-- absorption gives one for every operator (`Absorption`), hence a reflector
-- (`mahlo`). Absorption factors exactly into a small least closure and a
-- name for its carrier (`absorbed-small`, `absorbed-named`, `carried`,
-- `named`).

open import SPT.Base
open import SPT.Mahlo.Specification using
  (Family; Operator; Formers; Decode; Closure; Reflection; Mahlo)

------------------------------------------------------------------------
-- Least closures

-- A method for each code of a closure L: the base codes, the product, sum and
-- tree of a family, the identity of two points, and the operator's result and
-- branch codes at a family, each from the motive at the codes it is formed
-- from.

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D}
  {Ψ : Operator D} {A : Set ℓ} where

  record Methods (L : Closure Q Ψ A) {ν : Level} (P : A → Set ν) :
    Set (κ ⊔ ℓ ⊔ ν) where
    field
      on-empty : P (pr₁ (Closure.empty L))
      on-unit : P (pr₁ (Closure.unit L))
      on-two : P (pr₁ (Closure.two L))
      on-natural : P (pr₁ (Closure.natural L))
      on-product : (φ : Family (Decode D (Closure.interpret L))) →
        P (pr₁ φ) →
        ((x : Decode D (Closure.interpret L) (pr₁ φ)) → P (pr₂ φ x)) →
        P (pr₁ (Closure.product L φ))
      on-sum : (φ : Family (Decode D (Closure.interpret L))) →
        P (pr₁ φ) →
        ((x : Decode D (Closure.interpret L) (pr₁ φ)) → P (pr₂ φ x)) →
        P (pr₁ (Closure.sum L φ))
      on-tree : (φ : Family (Decode D (Closure.interpret L))) →
        P (pr₁ φ) →
        ((x : Decode D (Closure.interpret L) (pr₁ φ)) → P (pr₂ φ x)) →
        P (pr₁ (Closure.tree L φ))
      on-identity : (a : A) (x y : Decode D (Closure.interpret L) a) →
        P a → P (pr₁ (Closure.identity L a x y))
      on-result : (φ : Family (Decode D (Closure.interpret L))) →
        P (pr₁ φ) →
        ((x : Decode D (Closure.interpret L) (pr₁ φ)) → P (pr₂ φ x)) →
        P (pr₁ (Closure.inner L φ))
      on-branch : (φ : Family (Decode D (Closure.interpret L)))
        (y : Decode D (Closure.interpret L) (pr₁ (Closure.inner L φ))) →
        P (pr₁ φ) →
        ((x : Decode D (Closure.interpret L) (pr₁ φ)) → P (pr₂ φ x)) →
        P (pr₂ (Closure.inner L φ) y)

  -- Mathematical shape: L is the least closure, for motives of level ν.
  record Induction (L : Closure Q Ψ A) (ν : Level) :
    Set (κ ⊔ ℓ ⊔ lsuc ν) where
    field
      induction : (P : A → Set ν) → Methods L P → (a : A) → P a
      induction-empty : (P : A → Set ν) (m : Methods L P) →
        induction P m (pr₁ (Closure.empty L)) ＝ Methods.on-empty m
      induction-unit : (P : A → Set ν) (m : Methods L P) →
        induction P m (pr₁ (Closure.unit L)) ＝ Methods.on-unit m
      induction-two : (P : A → Set ν) (m : Methods L P) →
        induction P m (pr₁ (Closure.two L)) ＝ Methods.on-two m
      induction-natural : (P : A → Set ν) (m : Methods L P) →
        induction P m (pr₁ (Closure.natural L)) ＝ Methods.on-natural m
      induction-product : (P : A → Set ν) (m : Methods L P)
        (φ : Family (Decode D (Closure.interpret L))) →
        induction P m (pr₁ (Closure.product L φ))
          ＝ Methods.on-product m φ (induction P m (pr₁ φ))
              (λ x → induction P m (pr₂ φ x))
      induction-sum : (P : A → Set ν) (m : Methods L P)
        (φ : Family (Decode D (Closure.interpret L))) →
        induction P m (pr₁ (Closure.sum L φ))
          ＝ Methods.on-sum m φ (induction P m (pr₁ φ))
              (λ x → induction P m (pr₂ φ x))
      induction-tree : (P : A → Set ν) (m : Methods L P)
        (φ : Family (Decode D (Closure.interpret L))) →
        induction P m (pr₁ (Closure.tree L φ))
          ＝ Methods.on-tree m φ (induction P m (pr₁ φ))
              (λ x → induction P m (pr₂ φ x))
      induction-identity : (P : A → Set ν) (m : Methods L P) (a : A)
        (x y : Decode D (Closure.interpret L) a) →
        induction P m (pr₁ (Closure.identity L a x y))
          ＝ Methods.on-identity m a x y (induction P m a)
      induction-result : (P : A → Set ν) (m : Methods L P)
        (φ : Family (Decode D (Closure.interpret L))) →
        induction P m (pr₁ (Closure.inner L φ))
          ＝ Methods.on-result m φ (induction P m (pr₁ φ))
              (λ x → induction P m (pr₂ φ x))
      induction-branch : (P : A → Set ν) (m : Methods L P)
        (φ : Family (Decode D (Closure.interpret L)))
        (y : Decode D (Closure.interpret L) (pr₁ (Closure.inner L φ))) →
        induction P m (pr₂ (Closure.inner L φ) y)
          ＝ Methods.on-branch m φ y (induction P m (pr₁ φ))
              (λ x → induction P m (pr₂ φ x))

------------------------------------------------------------------------
-- Small least closures and absorbed reflections

-- A small least closure need not be named; an absorbed reflection is one that
-- is. The carrier of an absorbed reflection is the decoding of its name, so the
-- factorization is literal in one direction and a transport along the naming
-- identification in the other.

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} where

  record Small-Least (Q : Formers C D) (Ψ : Operator D) (ν : Level) :
    Set (κ ⊔ lsuc ℓ ⊔ lsuc ν) where
    field
      carrier : Set ℓ
      closure : Closure Q Ψ carrier
      induction : Induction closure ν

  -- Mathematical shape: a reflection of Q and Ψ whose closure is least.
  record Absorbed (Q : Formers C D) (Ψ : Operator D) (ν : Level) :
    Set (κ ⊔ ℓ ⊔ lsuc ν) where
    field
      reflection : Reflection Q Ψ
      induction : Induction (Reflection.closure reflection) ν

  -- Mathematical shape: every operator has an absorbed reflection.
  record Absorption (Q : Formers C D) (ν : Level) :
    Set (κ ⊔ ℓ ⊔ lsuc ν) where
    field
      absorb : (Ψ : Operator D) → Absorbed Q Ψ ν

  mahlo : {Q : Formers C D} {ν : Level} → Absorption Q ν → Mahlo Q
  mahlo absorption = record
    { reflect = λ Ψ → Absorbed.reflection (Absorption.absorb absorption Ψ)
    }

  absorbed-small : {Q : Formers C D} {Ψ : Operator D} {ν : Level} →
    Absorbed Q Ψ ν → Small-Least Q Ψ ν
  absorbed-small absorbed = record
    { carrier = D (Reflection.carrier (Absorbed.reflection absorbed))
    ; closure = Reflection.closure (Absorbed.reflection absorbed)
    ; induction = Absorbed.induction absorbed
    }

  absorbed-named : {Q : Formers C D} {Ψ : Operator D} {ν : Level}
    (absorbed : Absorbed Q Ψ ν) →
    D (Reflection.carrier (Absorbed.reflection absorbed))
      ＝ Small-Least.carrier (absorbed-small absorbed)
  absorbed-named absorbed = refl

  -- A least closure on the decoding of a name is absorbed.
  carried : {Q : Formers C D} {Ψ : Operator D} {ν : Level} {X : Set ℓ}
    (c : C) → D c ＝ X → (L : Closure Q Ψ X) → Induction L ν →
    Absorbed Q Ψ ν
  carried c refl L induction = record
    { reflection = record { carrier = c ; closure = L }
    ; induction = induction
    }

  named : {Q : Formers C D} {Ψ : Operator D} {ν : Level}
    (small : Small-Least Q Ψ ν) (c : C) →
    D c ＝ Small-Least.carrier small → Absorbed Q Ψ ν
  named small c e =
    carried c e (Small-Least.closure small) (Small-Least.induction small)
