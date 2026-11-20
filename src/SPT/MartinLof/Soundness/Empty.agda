{-# OPTIONS --safe --without-K --no-projection-like #-}

module SPT.MartinLof.Soundness.Empty where

-- Soundness of the rules of 0 (`sound`). The empty type is a closed type
-- read along ε (`empty-typed`). The eliminator's value is the model's
-- `absurd` at the motive read at the extension by the empty type
-- (`absurd-value`); it is stable by `absurd-[]`, the motive taken along
-- the extension of a substitution by the empty type over the new
-- context (`absurd-stable`), and has the motive's instance as type
-- (`absurd-typed`).

open import SPT.Base hiding (Lift; _∘_; id; lift; lower; zero)
import SPT.MartinLof.Formers as Formers
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Judgment using (Judgment)
import SPT.MartinLof.Rules.Empty as Block
open import SPT.MartinLof.Model.Empty using (Empty)
open import SPT.MartinLof.Model.Identity using (Identity)
open import SPT.MartinLof.Model.Lift using (Lift)
open import SPT.MartinLof.Model.Natural using (Natural)
open import SPT.MartinLof.Model.Subuniverse using
  (Operations; Subuniverse)
open import SPT.MartinLof.Model.Pi using (Pi)
open import SPT.MartinLof.Model.Russell using
  (Russell; Code; closed-code)
open import SPT.MartinLof.Model.Sigma using (Sigma)
open import SPT.MartinLof.Model.Sum using (Sum)
open import SPT.MartinLof.Model.Unit using (Unit)
open import SPT.MartinLof.Model.WellFounded using (WellFounded)
import SPT.MartinLof.Soundness.Environment as Environment
import SPT.MartinLof.Soundness.Instances as Instances
import SPT.MartinLof.Soundness.Interpretation as Interpretation
import SPT.MartinLof.Soundness.Transport as Transport
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
  (let ext = Environment.ext R)
  (let _[_]ᵉ = Environment._[_]ᵉ R)
  (let Stable = Environment.Stable R)
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
  (let bound-meaning = Transport.bound-meaning R lifting products pairs paths
                         trees nothing one sums numbers operations subuniverses
                           constant)
  (let instantiate-at = Instances.instantiate-at R lifting products pairs
                          paths trees nothing one sums numbers
                          operations subuniverses constant)
  (let closed-stable = Typing.closed-stable R lifting products pairs paths
                         trees nothing one sums numbers operations subuniverses
                           constant)
  (let as-type = Typing.as-type R lifting products pairs paths trees nothing
                   one sums numbers operations subuniverses constant)
  (let retype = Typing.retype R lifting products pairs paths trees nothing
                  one sums numbers operations subuniverses constant)
  (let lift-stable = Typing.lift-stable R lifting products pairs paths trees
                       nothing one sums numbers operations subuniverses
                         constant)
  (let instance-as-type = Typing.instance-as-type R lifting products pairs
                            paths trees nothing one sums numbers
                            operations subuniverses constant)
  (let instantiate-equal = Typing.instantiate-equal R lifting products pairs
                             paths trees nothing one sums numbers
                             operations subuniverses constant)
  (let type-stable = Interpretation.Typed.type-stable)
  (let type-code = Interpretation.Typed.type-code)
  (let term-stable = Interpretation.Typed.term-stable)
  (let term-type = Interpretation.Typed.term-type)
  where

  ----------------------------------------------------------------------
  -- The empty type

  empty-typed :
    {n : ℕ} (X : Ob) (env : Vec (Tm X) n)
    → Typed X env (suc 0) Formers.empty (Formers.universe 0)
  empty-typed X env =
    as-type X env 0 Formers.empty (closed-stable empty X env)
      (closed-code R 0 empty (ε X) empty-type)

  ----------------------------------------------------------------------
  -- The eliminator

  absurd-value :
    {n : ℕ} (k : ℕ) (M : Raw.Expression C (suc n)) (t : Raw.Expression C n)
    (X : Ob) (env : Vec (Tm X) n)
    → meaning (Formers.absurd k M t) X env
      ＝ absurd k (meaning M (X ▸ empty [ ε X ]) (ext (empty [ ε X ]) env))
          (meaning t X env)
  absurd-value k M t X env =
    ap (λ c → absurd k c (meaning t X env))
      (bound-meaning 1 M (X ▸ empty [ ε X ]) (ext (empty [ ε X ]) env))

  absurd-stable :
    {n : ℕ} (k : ℕ) (M : Raw.Expression C (suc n)) (t : Raw.Expression C n)
    (X : Ob) (env : Vec (Tm X) n)
    → Stable (meaning M) (X ▸ empty [ ε X ]) (ext (empty [ ε X ]) env)
    → Code R k (meaning M (X ▸ empty [ ε X ]) (ext (empty [ ε X ]) env))
    → Stable (meaning t) X env → type-of (meaning t X env) ＝ empty [ ε X ]
    → Stable (meaning (Formers.absurd k M t)) X env
  absurd-stable k M t X env sM cM st tt Y τ =
    let E = empty [ ε X ]
        E′ = empty [ ε Y ]
        e = q-type 0 E′ (closed-code R 0 empty (ε Y) empty-type) ∙
              (ap (λ s → s [ p ]) (closed-stable empty X env Y τ) ∙
                [∘] E τ p ⁻¹)
    in absurd-value k M t Y (env [ τ ]ᵉ) ∙
         (ap₂ (absurd k)
             (lift-stable (meaning M) 0 X E env
               (closed-code R 0 empty (ε X) empty-type) sM τ E′ (env [ τ ]ᵉ)
               e refl)
             (st Y τ) ∙
           (absurd-[] k (meaning M (X ▸ E) (ext E env)) (meaning t X env)
                 τ cM tt ⁻¹ ∙
             ap (λ s → s [ τ ]) (absurd-value k M t X env ⁻¹)))

  absurd-typed :
    {n : ℕ} (k : ℕ) (M : Raw.Expression C (suc n)) (t : Raw.Expression C n)
    (X : Ob) (env : Vec (Tm X) n)
    → Typed (X ▸ empty [ ε X ]) (ext (empty [ ε X ]) env) (suc k) M
        (Formers.universe k)
    → Typed X env 0 t Formers.empty
    → Typed X env k (Formers.absurd k M t) (Formers.instantiate M t)
  absurd-typed k M t X env TM Tt =
    let E = empty [ ε X ]
        T = instance-as-type 0 k Formers.empty M t X env TM Tt
    in record
      { type-stable = term-stable T
      ; type-code = term-type T
      ; term-stable =
          absurd-stable k M t X env (term-stable TM) (term-type TM)
            (term-stable Tt) (term-type Tt)
      ; term-type =
          ap type-of (absurd-value k M t X env) ∙
            (absurd-type k (meaning M (X ▸ E) (ext E env)) (meaning t X env)
                (term-type TM) (term-type Tt) ∙
              instantiate-at 0 M t X E env (term-stable TM)
                  (term-stable Tt) (term-type Tt)
                  (closed-code R 0 empty (ε X) empty-type) ⁻¹)
      }

  ----------------------------------------------------------------------
  -- The rules of 0

  sound :
    {j : Judgment C} (r : Block.Rule C j)
    → ((i : Fin (length (Block.premises r)))
       → Valid (list-lookup (Block.premises r) i))
    → Valid j
  sound (Block.formation Γ) h =
    h fzero , empty-typed (object Γ) (values Γ)
  sound (Block.elimination Γ k M t) h =
    let (_ , TM) = h fzero
        (vΓ , Tt) = h (fsuc fzero)
    in vΓ , absurd-typed k M t (object Γ) (values Γ) TM Tt
  sound (Block.elimination-equal Γ k M M′ t t′) h =
    let (_ , TM , TM′ , eM) = h fzero
        (vΓ , Tt , Tt′ , et) = h (fsuc fzero)
        X = object Γ
        env = values Γ
        TL = absurd-typed k M t X env TM Tt
    in vΓ
       , TL
       , retype X env k (Formers.absurd k M′ t′) (Formers.instantiate M t)
           (Formers.instantiate M′ t′)
           (absurd-typed k M′ t′ X env TM′ Tt′)
           (type-stable TL) (type-code TL)
           (instantiate-equal 0 Formers.empty Formers.empty M′ M t′ t X env
             (term-stable TM′) (term-stable TM) Tt′ Tt refl (eM ⁻¹)
             (et ⁻¹))
       , absurd-value k M t X env ∙
           (ap₂ (absurd k) eM et ∙
             absurd-value k M′ t′ X env ⁻¹)
