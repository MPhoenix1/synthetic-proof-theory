{-# OPTIONS --safe --without-K --no-projection-like #-}

module SPT.MartinLof.Soundness.Constant where

-- Soundness of the rule of the constants (`sound`), for a model whose
-- value of each constant c has the value of c's statement as type, the
-- hypothesis the theory's axioms ask of a model. A closed expression has
-- the value of the expression at the empty context read along ε
-- (`closed-at`), so the statement, a closed type, is a stable type in
-- every context, and the constant read along ε is a stable term of it
-- (`constant-typed`).

open import SPT.Base hiding (Lift; _∘_; id; lift; lower; zero)
import SPT.MartinLof.Formers as Formers
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Judgment using (Judgment)
import SPT.MartinLof.Rules.Constant as Block
open import SPT.MartinLof.Model.Empty using (Empty)
open import SPT.MartinLof.Model.Identity using (Identity)
open import SPT.MartinLof.Model.Lift using (Lift)
open import SPT.MartinLof.Model.Natural using (Natural)
open import SPT.MartinLof.Model.Subuniverse using
  (Operations; Subuniverse)
open import SPT.MartinLof.Model.Pi using (Pi)
open import SPT.MartinLof.Model.Russell using (Russell; Code; code-[])
open import SPT.MartinLof.Model.Sigma using (Sigma)
open import SPT.MartinLof.Model.Sum using (Sum)
open import SPT.MartinLof.Model.Unit using (Unit)
open import SPT.MartinLof.Model.WellFounded using (WellFounded)
import SPT.MartinLof.Soundness.Environment as Environment
import SPT.MartinLof.Soundness.Instances as Instances
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
  (let _[_]ᵉ = Environment._[_]ᵉ R)
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
  (let closed-value = Instances.closed-value R lifting products pairs paths
                        trees nothing one sums numbers operations subuniverses
                          constant)
  (let closed-stable = Typing.closed-stable R lifting products pairs paths
                         trees nothing one sums numbers operations subuniverses
                           constant)
  (let term-stable = Interpretation.Typed.term-stable)
  (let term-type = Interpretation.Typed.term-type)
  where

  -- A closed expression, stable at the empty context, in scope n.
  closed-at :
    {n : ℕ} (S : Raw.Expression C 0) (Y : Ob) (env : Vec (Tm Y) n)
    → Environment.Stable R (meaning S) ◇ []
    → meaning (Formers.closed n S) Y env ＝ meaning S ◇ [] [ ε Y ]
  closed-at S Y env sS = closed-value S Y env ∙ sS Y (ε Y)

  constant-typed :
    {n : ℕ} (c : C) (l : ℕ) (S : Raw.Expression C 0)
    → type-of (constant c) ＝ meaning S ◇ []
    → (X : Ob) (env : Vec (Tm X) n)
    → Typed ◇ [] (suc l) S (Formers.universe l)
    → Typed X env l (Formers.constant c) (Formers.closed n S)
  constant-typed c l S tc X env TS =
    let s = meaning S ◇ []
        sS = term-stable TS
    in record
      { type-stable = λ Y τ →
          closed-at S Y (env [ τ ]ᵉ) sS ∙
            (closed-stable s X env Y τ ∙
              ap (λ t → t [ τ ]) (closed-at S X env sS ⁻¹))
      ; type-code =
          transport (Code R l) (closed-at S X env sS ⁻¹)
            (code-[] R l s (ε X) (term-type TS))
      ; term-stable = closed-stable (constant c) X env
      ; term-type =
          type-of-[] (constant c) (ε X) ∙
            (ap (λ t → t [ ε X ]) tc ∙
              closed-at S X env sS ⁻¹)
      }

  sound :
    (axioms : Block.Axioms C)
    → ((c : C)
       → type-of (constant c) ＝ meaning (Block.Axioms.statement axioms c) ◇ [])
    → {j : Judgment C} (r : Block.Rule C axioms j)
    → ((i : Fin (length (Block.premises r)))
       → Valid (list-lookup (Block.premises r) i))
    → Valid j
  sound axioms tc (Block.axiom Γ c) h =
    let (_ , TS) = h (fsuc fzero)
    in h fzero
       , constant-typed c (Block.Axioms.level axioms c)
           (Block.Axioms.statement axioms c) (tc c) (object Γ) (values Γ) TS
