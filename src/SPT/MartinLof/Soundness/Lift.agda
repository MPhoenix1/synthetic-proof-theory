{-# OPTIONS --safe --without-K --no-projection-like #-}

module SPT.MartinLof.Soundness.Lift where

-- Soundness of the universes' rule and of the rules of Lift (`universe`,
-- `sound`). The value of each Lift former is the model's operation at the
-- values of its children; it is stable by the operation's stability law
-- (`lifted-stable`, `lift-stable`, `lower-stable`), and has its type by
-- the typing law (`lifted-typed`, `lift-typed`, `lower-typed`). The
-- computation rules are the model's laws; congruences retype the primed
-- side along the equal types.

open import SPT.Base hiding (Lift; _∘_; id; lift; lower; zero)
import SPT.MartinLof.Formers as Formers
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Judgment using (Judgment)
import SPT.MartinLof.Rules.Lift as Block
import SPT.MartinLof.Rules.Universe as Universe
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
  (let closed-stable = Typing.closed-stable R lifting products pairs paths
                         trees nothing one sums numbers operations subuniverses
                           constant)
  (let as-type = Typing.as-type R lifting products pairs paths trees nothing
                   one sums numbers operations subuniverses constant)
  (let retype = Typing.retype R lifting products pairs paths trees nothing
                  one sums numbers operations subuniverses constant)
  where

  ----------------------------------------------------------------------
  -- Universes

  universe-sound :
    {j : Judgment C} (r : Universe.Rule C j)
    → ((i : Fin (length (Universe.premises r)))
       → Valid (list-lookup (Universe.premises r) i))
    → Valid j
  universe-sound (Universe.formation Γ l) h =
    h fzero
    , as-type (object Γ) (values Γ) (suc l) (Formers.universe l)
        (closed-stable (universe l) (object Γ) (values Γ))
        (closed-code R (suc l) (universe l) (ε (object Γ)) (universe-type l))

  ----------------------------------------------------------------------
  -- Lift

  lifted-stable :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n) (X : Ob) (env : Vec (Tm X) n)
    → Stable (meaning A) X env → Code R m (meaning A X env)
    → Stable (meaning (Formers.lifted m k A)) X env
  lifted-stable m k A X env sA cA Y τ =
    ap (lifted m k) (sA Y τ) ∙
      lifted-[] m k (meaning A X env) τ cA ⁻¹

  lift-stable :
    {n : ℕ} (m k : ℕ) (A a : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Stable (meaning A) X env → Code R m (meaning A X env)
    → Stable (meaning a) X env → type-of (meaning a X env) ＝ meaning A X env
    → Stable (meaning (Formers.lift m k A a)) X env
  lift-stable m k A a X env sA cA sa ta Y τ =
    ap₂ (lift m k) (sA Y τ) (sa Y τ) ∙
      lift-[] m k (meaning A X env) (meaning a X env) τ cA ta ⁻¹

  lower-stable :
    {n : ℕ} (m k : ℕ) (A y : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Stable (meaning A) X env → Code R m (meaning A X env)
    → Stable (meaning y) X env
    → type-of (meaning y X env) ＝ lifted m k (meaning A X env)
    → Stable (meaning (Formers.lower m k A y)) X env
  lower-stable m k A y X env sA cA sy ty Y τ =
    ap₂ (lower m k) (sA Y τ) (sy Y τ) ∙
      lower-[] m k (meaning A X env) (meaning y X env) τ cA ty ⁻¹

  lifted-typed :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n) (X : Ob) (env : Vec (Tm X) n)
    → Stable (meaning A) X env → Code R m (meaning A X env)
    → Typed X env (suc (m ⊔ℕ k)) (Formers.lifted m k A)
        (Formers.universe (m ⊔ℕ k))
  lifted-typed m k A X env sA cA =
    as-type X env (m ⊔ℕ k) (Formers.lifted m k A)
      (lifted-stable m k A X env sA cA)
      (lifted-type m k (meaning A X env) cA)

  lift-typed :
    {n : ℕ} (m k : ℕ) (A a : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Stable (meaning A) X env → Code R m (meaning A X env)
    → Stable (meaning a) X env → type-of (meaning a X env) ＝ meaning A X env
    → Typed X env (m ⊔ℕ k) (Formers.lift m k A a) (Formers.lifted m k A)
  lift-typed m k A a X env sA cA sa ta = record
    { type-stable = lifted-stable m k A X env sA cA
    ; type-code = lifted-type m k (meaning A X env) cA
    ; term-stable = lift-stable m k A a X env sA cA sa ta
    ; term-type = lift-type m k (meaning A X env) (meaning a X env) cA ta
    }

  lower-typed :
    {n : ℕ} (m k : ℕ) (A y : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Stable (meaning A) X env → Code R m (meaning A X env)
    → Stable (meaning y) X env
    → type-of (meaning y X env) ＝ lifted m k (meaning A X env)
    → Typed X env m (Formers.lower m k A y) A
  lower-typed m k A y X env sA cA sy ty = record
    { type-stable = sA
    ; type-code = cA
    ; term-stable = lower-stable m k A y X env sA cA sy ty
    ; term-type = lower-type m k (meaning A X env) (meaning y X env) cA ty
    }

  sound :
    {j : Judgment C} (r : Block.Rule C j)
    → ((i : Fin (length (Block.premises r)))
       → Valid (list-lookup (Block.premises r) i))
    → Valid j
  sound (Block.formation Γ m k A) h =
    let (vΓ , TA) = h fzero
    in vΓ
       , lifted-typed m k A (object Γ) (values Γ)
           (Interpretation.Typed.term-stable TA)
           (Interpretation.Typed.term-type TA)
  sound (Block.introduction Γ m k A a) h =
    let (vΓ , TA) = h fzero
        (_ , Ta) = h (fsuc fzero)
    in vΓ
       , lift-typed m k A a (object Γ) (values Γ)
           (Interpretation.Typed.term-stable TA)
           (Interpretation.Typed.term-type TA)
           (Interpretation.Typed.term-stable Ta)
           (Interpretation.Typed.term-type Ta)
  sound (Block.elimination Γ m k A y) h =
    let (vΓ , TA) = h fzero
        (_ , Ty) = h (fsuc fzero)
    in vΓ
       , lower-typed m k A y (object Γ) (values Γ)
           (Interpretation.Typed.term-stable TA)
           (Interpretation.Typed.term-type TA)
           (Interpretation.Typed.term-stable Ty)
           (Interpretation.Typed.term-type Ty)
  sound (Block.computation Γ m k A a) h =
    let (vΓ , TA) = h fzero
        (_ , Ta) = h (fsuc fzero)
        X = object Γ
        env = values Γ
        sA = Interpretation.Typed.term-stable TA
        cA = Interpretation.Typed.term-type TA
        sa = Interpretation.Typed.term-stable Ta
        ta = Interpretation.Typed.term-type Ta
    in vΓ
       , lower-typed m k A (Formers.lift m k A a) X env sA cA
           (lift-stable m k A a X env sA cA sa ta)
           (lift-type m k (meaning A X env) (meaning a X env) cA ta)
       , Ta
       , lower-lift m k (meaning A X env) (meaning a X env) cA ta
  sound (Block.uniqueness Γ m k A y) h =
    let (vΓ , TA) = h fzero
        (_ , Ty) = h (fsuc fzero)
        X = object Γ
        env = values Γ
        sA = Interpretation.Typed.term-stable TA
        cA = Interpretation.Typed.term-type TA
        sy = Interpretation.Typed.term-stable Ty
        ty = Interpretation.Typed.term-type Ty
    in vΓ
       , lift-typed m k A (Formers.lower m k A y) X env sA cA
           (lower-stable m k A y X env sA cA sy ty)
           (lower-type m k (meaning A X env) (meaning y X env) cA ty)
       , Ty
       , lift-lower m k (meaning A X env) (meaning y X env) cA ty
  sound (Block.formation-equal Γ m k A A′) h =
    let (vΓ , TA , TA′ , eA) = h fzero
        X = object Γ
        env = values Γ
    in vΓ
       , lifted-typed m k A X env (Interpretation.Typed.term-stable TA)
           (Interpretation.Typed.term-type TA)
       , lifted-typed m k A′ X env (Interpretation.Typed.term-stable TA′)
           (Interpretation.Typed.term-type TA′)
       , ap (lifted m k) eA
  sound (Block.introduction-equal Γ m k A A′ a a′) h =
    let (vΓ , TA , TA′ , eA) = h fzero
        (_ , Ta , Ta′ , ea) = h (fsuc fzero)
        X = object Γ
        env = values Γ
        sA = Interpretation.Typed.term-stable TA
        cA = Interpretation.Typed.term-type TA
        sA′ = Interpretation.Typed.term-stable TA′
        cA′ = Interpretation.Typed.term-type TA′
    in vΓ
       , lift-typed m k A a X env sA cA (Interpretation.Typed.term-stable Ta)
           (Interpretation.Typed.term-type Ta)
       , retype X env (m ⊔ℕ k) (Formers.lift m k A′ a′) (Formers.lifted m k A)
           (Formers.lifted m k A′)
           (lift-typed m k A′ a′ X env sA′ cA′
             (Interpretation.Typed.term-stable Ta′)
             (Interpretation.Typed.term-type Ta′ ∙ eA))
           (lifted-stable m k A X env sA cA)
           (lifted-type m k (meaning A X env) cA)
           (ap (lifted m k) (eA ⁻¹))
       , ap₂ (lift m k) eA ea
  sound (Block.elimination-equal Γ m k A A′ y y′) h =
    let (vΓ , TA , TA′ , eA) = h fzero
        (_ , Ty , Ty′ , ey) = h (fsuc fzero)
        X = object Γ
        env = values Γ
        sA = Interpretation.Typed.term-stable TA
        cA = Interpretation.Typed.term-type TA
        sA′ = Interpretation.Typed.term-stable TA′
        cA′ = Interpretation.Typed.term-type TA′
    in vΓ
       , lower-typed m k A y X env sA cA (Interpretation.Typed.term-stable Ty)
           (Interpretation.Typed.term-type Ty)
       , retype X env m (Formers.lower m k A′ y′) A A′
           (lower-typed m k A′ y′ X env sA′ cA′
             (Interpretation.Typed.term-stable Ty′)
             (Interpretation.Typed.term-type Ty′ ∙
               ap (lifted m k) eA))
           sA cA (eA ⁻¹)
       , ap₂ (lower m k) eA ey
