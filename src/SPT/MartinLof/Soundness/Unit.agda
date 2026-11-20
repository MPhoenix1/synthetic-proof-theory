{-# OPTIONS --safe --without-K --no-projection-like #-}

module SPT.MartinLof.Soundness.Unit where

-- Soundness of the rules of 1 (`sound`). The unit type and its point are
-- closed terms read along ε (`unit-typed`, `star-typed`); every term of
-- the unit type is the point by the model's η (`star-unique`).

open import SPT.Base hiding (Lift; _∘_; id; lift; lower; zero)
import SPT.MartinLof.Formers as Formers
open import SPT.MartinLof.Judgment using (Judgment)
import SPT.MartinLof.Rules.Unit as Block
open import SPT.MartinLof.Model.Empty using (Empty)
open import SPT.MartinLof.Model.Identity using (Identity)
open import SPT.MartinLof.Model.Lift using (Lift)
open import SPT.MartinLof.Model.Natural using (Natural)
open import SPT.MartinLof.Model.Subuniverse using
  (Operations; Subuniverse)
open import SPT.MartinLof.Model.Pi using (Pi)
open import SPT.MartinLof.Model.Russell using (Russell; closed-code)
open import SPT.MartinLof.Model.Sigma using (Sigma)
open import SPT.MartinLof.Model.Sum using (Sum)
open import SPT.MartinLof.Model.Unit using (Unit)
open import SPT.MartinLof.Model.WellFounded using (WellFounded)
import SPT.MartinLof.Soundness.Interpretation as Interpretation
import SPT.MartinLof.Soundness.Typing as Typing

module _ {ℓ : Level} {C : Set}
  (R : Russell ℓ) (let open Russell R)
  (lifting : Lift R) (let open Lift lifting)
  (products : Pi R) (let open Pi products)
  (pairs : Sigma R) (let open Sigma pairs)
  (paths : Identity R) (let open Identity paths)
  (trees : WellFounded R products) (let open WellFounded trees)
  (nothing : Empty R) (let open Empty nothing)
  (one : Unit R) (let open Unit one)
  (sums : Sum R) (let open Sum sums)
  (numbers : Natural R) (let open Natural numbers)
  (operations : Operations R) (let open Operations operations)
  (subuniverses : Subuniverse R products operations)
  (constant : C → Tm ◇)
  (let meaning = Interpretation.⟦_⟧ R lifting products pairs paths trees
                   nothing one sums numbers operations subuniverses constant)
  (let object = Interpretation.object R lifting products pairs paths trees
                  nothing one sums numbers operations subuniverses constant)
  (let values = Interpretation.values R lifting products pairs paths trees
                  nothing one sums numbers operations subuniverses constant)
  (let Typed = Interpretation.Typed R lifting products pairs paths trees
                 nothing one sums numbers operations subuniverses constant)
  (let Valid = Interpretation.Valid R lifting products pairs paths trees
                 nothing one sums numbers operations subuniverses constant)
  (let closed-stable = Typing.closed-stable R lifting products pairs paths
                         trees nothing one sums numbers operations subuniverses
                           constant)
  (let as-type = Typing.as-type R lifting products pairs paths trees nothing
                   one sums numbers operations subuniverses constant)
  (let term-type = Interpretation.Typed.term-type)
  where

  unit-typed :
    {n : ℕ} (X : Ob) (env : Vec (Tm X) n)
    → Typed X env (suc 0) Formers.unit (Formers.universe 0)
  unit-typed X env =
    as-type X env 0 Formers.unit (closed-stable unit X env)
      (closed-code R 0 unit (ε X) unit-type)

  star-typed :
    {n : ℕ} (X : Ob) (env : Vec (Tm X) n)
    → Typed X env 0 Formers.star Formers.unit
  star-typed X env = record
    { type-stable = closed-stable unit X env
    ; type-code = closed-code R 0 unit (ε X) unit-type
    ; term-stable = closed-stable star X env
    ; term-type =
        type-of-[] star (ε X) ∙ ap (λ s → s [ ε X ]) star-type
    }

  sound :
    {j : Judgment C} (r : Block.Rule C j)
    → ((i : Fin (length (Block.premises r)))
       → Valid (list-lookup (Block.premises r) i))
    → Valid j
  sound (Block.formation Γ) h = h fzero , unit-typed (object Γ) (values Γ)
  sound (Block.introduction Γ) h =
    h fzero , star-typed (object Γ) (values Γ)
  sound (Block.uniqueness Γ t) h =
    let (vΓ , Tt) = h fzero
    in vΓ
       , Tt
       , star-typed (object Γ) (values Γ)
       , star-unique (meaning t (object Γ) (values Γ)) (term-type Tt)
