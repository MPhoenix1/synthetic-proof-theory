{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Residence.Inductive where

-- What induction–recursion contributes. The induction–recursive closure of
-- Mahlo.Relative has its codes at the level of the decodings, for names at
-- any level, and it is least (`inductive-least`): a small least closure for
-- every family and operator (`inductive-small`). Where every small type is
-- already the decoding of a name (`Naming`), naming is free and the small
-- closure is absorbed (`naming-absorbs`); the ambient family of all types
-- of a level is such a family (`ambient-naming`, `ambient-absorbs`).

open import SPT.Base
import SPT.Mahlo.Ambient as Ambient
open import SPT.Mahlo.Specification using (Operator; Formers)
import SPT.Mahlo.Relative as Relative
open import SPT.Mahlo.Residence.Absorption using
  (Methods; Induction; Small-Least; Absorption; named)

------------------------------------------------------------------------
-- The induction–recursive closure is least

-- Methods at the closure's codes are Relative's methods at its constructors:
-- each code of the closure is a constructor applied to the components of a
-- family.

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} where

  translate : (Q : Formers C D) (Ψ : Operator D) {ν : Level}
    (P : Relative.Generated Q Ψ → Set ν) →
    Methods (Relative.closure Q Ψ) P → Relative.Methods Q Ψ P
  translate Q Ψ P m = record
    { on-empty = Methods.on-empty m
    ; on-unit = Methods.on-unit m
    ; on-two = Methods.on-two m
    ; on-natural = Methods.on-natural m
    ; on-product = λ a b → Methods.on-product m (a , b)
    ; on-sum = λ a b → Methods.on-sum m (a , b)
    ; on-tree = λ a b → Methods.on-tree m (a , b)
    ; on-identity = λ a x y → Methods.on-identity m a x y
    ; on-result = λ a b → Methods.on-result m (a , b)
    ; on-branch = λ a b y → Methods.on-branch m (a , b) y
    }

  inductive-least : (Q : Formers C D) (Ψ : Operator D) (ν : Level) →
    Induction (Relative.closure Q Ψ) ν
  inductive-least Q Ψ ν = record
    { induction = λ P m → Relative.induction (translate Q Ψ P m)
    ; induction-empty = λ P m → refl
    ; induction-unit = λ P m → refl
    ; induction-two = λ P m → refl
    ; induction-natural = λ P m → refl
    ; induction-product = λ P m φ → refl
    ; induction-sum = λ P m φ → refl
    ; induction-tree = λ P m φ → refl
    ; induction-identity = λ P m a x y → refl
    ; induction-result = λ P m φ → refl
    ; induction-branch = λ P m φ y → refl
    }

  inductive-small : (Q : Formers C D) (Ψ : Operator D) (ν : Level) →
    Small-Least Q Ψ ν
  inductive-small Q Ψ ν = record
    { carrier = Relative.Generated Q Ψ
    ; closure = Relative.closure Q Ψ
    ; induction = inductive-least Q Ψ ν
    }

------------------------------------------------------------------------
-- Families naming every small type

-- Mathematical shape: Naming D = Π (X : Set ℓ). Σ (c : C). D c ＝ X. Such a
-- family names the induction–recursive closure of every operator.

module _ {κ ℓ : Level} {C : Set κ} where

  Naming : (C → Set ℓ) → Set (κ ⊔ lsuc ℓ)
  Naming D = (X : Set ℓ) → Σ C (λ c → D c ＝ X)

  naming-absorbs : {D : C → Set ℓ} (Q : Formers C D) → Naming D →
    (ν : Level) → Absorption Q ν
  naming-absorbs Q names ν = record
    { absorb = λ Ψ →
        named (inductive-small Q Ψ ν)
          (pr₁ (names (Relative.Generated Q Ψ)))
          (pr₂ (names (Relative.Generated Q Ψ)))
    }

-- The types of level ℓ, each its own name.
ambient-naming : (ℓ : Level) → Naming (λ (X : Set ℓ) → X)
ambient-naming ℓ X = X , refl

ambient-absorbs : (ℓ ν : Level) → Absorption (Ambient.formers ℓ) ν
ambient-absorbs ℓ ν =
  naming-absorbs (Ambient.formers ℓ) (ambient-naming ℓ) ν
