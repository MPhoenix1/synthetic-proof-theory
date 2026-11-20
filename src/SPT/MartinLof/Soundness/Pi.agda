{-# OPTIONS --safe --without-K --no-projection-like #-}

module SPT.MartinLof.Soundness.Pi where

-- Soundness of the rules of Π (`sound`). The value of each Π-former is
-- the model's operation at the values of its children, the codomain read
-- at the extension by the domain (`pi-value`, `lambda-value`,
-- `application-value`). It is stable by the stability laws
-- (`pi-stable`, `lambda-stable`, `application-stable`) and has its type by
-- the typing laws (`pi-typed`, `lambda-typed`, `application-typed`). β is
-- the model's β with the instance lemma (`beta-value`). η: the
-- η-expansion has the value of f at every context where the premises
-- hold (`eta-value`), so it is stable with f (`eta-typed`).

open import SPT.Base hiding (Lift; _∘_; id; lift; lower; zero)
open import SPT.Foundation.Vectors.Tabulation using (tabulate-lookup)
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Tree as Tree
import SPT.Foundation.Tree.Binding as Binding
import SPT.MartinLof.Formers as Formers
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Judgment using (Judgment)
import SPT.MartinLof.Rules.Pi as Block
open import SPT.MartinLof.Model.Empty using (Empty)
open import SPT.MartinLof.Model.Identity using (Identity)
open import SPT.MartinLof.Model.Lift using (Lift)
open import SPT.MartinLof.Model.Natural using (Natural)
open import SPT.MartinLof.Model.Subuniverse using
  (Operations; Subuniverse)
open import SPT.MartinLof.Model.Pi using (Pi)
open import SPT.MartinLof.Model.Russell using (Russell; Code; under-type)
open import SPT.MartinLof.Model.Sigma using (Sigma)
open import SPT.MartinLof.Model.Sum using (Sum)
open import SPT.MartinLof.Model.Unit using (Unit)
open import SPT.MartinLof.Model.WellFounded using (WellFounded)
import SPT.MartinLof.Soundness.Environment as Environment
import SPT.MartinLof.Soundness.Instances as Instances
import SPT.MartinLof.Soundness.Interpretation as Interpretation
import SPT.MartinLof.Soundness.Transport as Transport
open import SPT.MartinLof.Soundness.Transport using (ap₃)
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
  (let rename-value = Instances.rename-value R lifting products pairs paths
                        trees nothing one sums numbers operations subuniverses
                          constant)
  (let weaken-at = Instances.weaken-at R lifting products pairs paths trees
                     nothing one sums numbers operations subuniverses constant)
  (let instantiate-at = Instances.instantiate-at R lifting products pairs
                          paths trees nothing one sums numbers
                          operations subuniverses constant)
  (let as-type = Typing.as-type R lifting products pairs paths trees nothing
                   one sums numbers operations subuniverses constant)
  (let under-stable = Typing.under-stable R lifting products pairs paths
                        trees nothing one sums numbers operations subuniverses
                          constant)
  (let instance-as-type = Typing.instance-as-type R lifting products pairs
                            paths trees nothing one sums numbers
                            operations subuniverses constant)
  (let instance-typed = Typing.instance-typed R lifting products pairs paths
                          trees nothing one sums numbers operations
                            subuniverses constant)
  (let retype = Typing.retype R lifting products pairs paths trees nothing
                  one sums numbers operations subuniverses constant)
  (let typed-[] = Typing.typed-[] R lifting products pairs paths trees
                    nothing one sums numbers operations subuniverses constant)
  (let typed-under = Typing.typed-under R lifting products pairs paths trees
                       nothing one sums numbers operations subuniverses
                         constant)
  (let typed-along = Typing.typed-along R lifting products pairs paths trees
                       nothing one sums numbers operations subuniverses
                         constant)
  (let type-stable = Interpretation.Typed.type-stable)
  (let type-code = Interpretation.Typed.type-code)
  (let term-stable = Interpretation.Typed.term-stable)
  (let term-type = Interpretation.Typed.term-type)
  where

  ----------------------------------------------------------------------
  -- Values

  pi-value :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (X : Ob) (env : Vec (Tm X) n)
    → meaning (Formers.pi m k A B) X env
      ＝ pi m k (meaning A X env)
          (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
  pi-value m k A B X env =
    ap (pi m k (meaning A X env))
      (bound-meaning 1 B (X ▸ meaning A X env) (ext (meaning A X env) env))

  lambda-value :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B t : Raw.Expression C (suc n)) (X : Ob) (env : Vec (Tm X) n)
    → meaning (Formers.lambda m k A B t) X env
      ＝ lambda m k (meaning A X env)
          (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
          (meaning t (X ▸ meaning A X env) (ext (meaning A X env) env))
  lambda-value m k A B t X env =
    ap₂ (lambda m k (meaning A X env))
      (bound-meaning 1 B (X ▸ meaning A X env) (ext (meaning A X env) env))
      (bound-meaning 1 t (X ▸ meaning A X env) (ext (meaning A X env) env))

  application-value :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (f a : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → meaning (Formers.application m k A B f a) X env
      ＝ application m k (meaning A X env)
          (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
          (meaning f X env) (meaning a X env)
  application-value m k A B f a X env =
    ap (λ b → application m k (meaning A X env) b (meaning f X env)
                  (meaning a X env))
      (bound-meaning 1 B (X ▸ meaning A X env) (ext (meaning A X env) env))

  ----------------------------------------------------------------------
  -- Stability

  pi-stable :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (X : Ob) (env : Vec (Tm X) n)
    → Stable (meaning A) X env → (cA : Code R m (meaning A X env))
    → Stable (meaning B) (X ▸ meaning A X env) (ext (meaning A X env) env)
    → Code R k (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
    → Stable (meaning (Formers.pi m k A B)) X env
  pi-stable m k A B X env sA cA sB cB Y τ =
    let a = meaning A X env
        b = meaning B (X ▸ a) (ext a env)
    in pi-value m k A B Y (env [ τ ]ᵉ) ∙
         (ap (λ x → pi m k x (meaning B (Y ▸ x) (ext x (env [ τ ]ᵉ))))
             (sA Y τ) ∙
           (ap (pi m k (a [ τ ])) (under-stable m B X a env cA sB τ) ∙
             (pi-[] m k a b τ cA cB ⁻¹ ∙
               ap (λ s → s [ τ ]) (pi-value m k A B X env ⁻¹))))

  lambda-stable :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B t : Raw.Expression C (suc n)) (X : Ob) (env : Vec (Tm X) n)
    → Stable (meaning A) X env → (cA : Code R m (meaning A X env))
    → Stable (meaning B) (X ▸ meaning A X env) (ext (meaning A X env) env)
    → Code R k (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
    → Stable (meaning t) (X ▸ meaning A X env) (ext (meaning A X env) env)
    → type-of (meaning t (X ▸ meaning A X env) (ext (meaning A X env) env))
      ＝ meaning B (X ▸ meaning A X env) (ext (meaning A X env) env)
    → Stable (meaning (Formers.lambda m k A B t)) X env
  lambda-stable m k A B t X env sA cA sB cB st tt Y τ =
    let a = meaning A X env
        b = meaning B (X ▸ a) (ext a env)
        u = meaning t (X ▸ a) (ext a env)
    in lambda-value m k A B t Y (env [ τ ]ᵉ) ∙
         (ap
             (λ x → lambda m k x (meaning B (Y ▸ x) (ext x (env [ τ ]ᵉ)))
                      (meaning t (Y ▸ x) (ext x (env [ τ ]ᵉ))))
             (sA Y τ) ∙
           (ap₂ (lambda m k (a [ τ ])) (under-stable m B X a env cA sB τ)
               (under-stable m t X a env cA st τ) ∙
             (lambda-[] m k a b u τ cA cB tt ⁻¹ ∙
               ap (λ s → s [ τ ]) (lambda-value m k A B t X env ⁻¹))))

  application-stable :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (f x : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Stable (meaning A) X env → (cA : Code R m (meaning A X env))
    → Stable (meaning B) (X ▸ meaning A X env) (ext (meaning A X env) env)
    → Code R k (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
    → Stable (meaning f) X env
    → type-of (meaning f X env)
      ＝ pi m k (meaning A X env)
          (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
    → Stable (meaning x) X env → type-of (meaning x X env) ＝ meaning A X env
    → Stable (meaning (Formers.application m k A B f x)) X env
  application-stable m k A B f x X env sA cA sB cB sf tf sx tx Y τ =
    let a = meaning A X env
        b = meaning B (X ▸ a) (ext a env)
    in application-value m k A B f x Y (env [ τ ]ᵉ) ∙
         (ap
             (λ y → application m k y (meaning B (Y ▸ y) (ext y (env [ τ ]ᵉ)))
                      (meaning f Y (env [ τ ]ᵉ)) (meaning x Y (env [ τ ]ᵉ)))
             (sA Y τ) ∙
           (ap₃ (application m k (a [ τ ]))
               (under-stable m B X a env cA sB τ) (sf Y τ) (sx Y τ) ∙
             (application-[] m k a b (meaning f X env) (meaning x X env)
                      τ cA cB tf tx ⁻¹ ∙
               ap (λ s → s [ τ ])
                 (application-value m k A B f x X env ⁻¹))))

  ----------------------------------------------------------------------
  -- Typing

  pi-typed :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (X : Ob) (env : Vec (Tm X) n)
    → Typed X env (suc m) A (Formers.universe m)
    → Typed (X ▸ meaning A X env) (ext (meaning A X env) env) (suc k) B
        (Formers.universe k)
    → Typed X env (suc (m ⊔ℕ k)) (Formers.pi m k A B)
        (Formers.universe (m ⊔ℕ k))
  pi-typed m k A B X env TA TB =
    let a = meaning A X env
        cA = Interpretation.Typed.term-type TA
        cB = Interpretation.Typed.term-type TB
    in as-type X env (m ⊔ℕ k) (Formers.pi m k A B)
         (pi-stable m k A B X env (Interpretation.Typed.term-stable TA) cA
           (Interpretation.Typed.term-stable TB) cB)
         (transport (Code R (m ⊔ℕ k)) (pi-value m k A B X env ⁻¹)
           (pi-type m k a (meaning B (X ▸ a) (ext a env)) cA cB))

  lambda-typed :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B t : Raw.Expression C (suc n)) (X : Ob) (env : Vec (Tm X) n)
    → Typed X env (suc m) A (Formers.universe m)
    → Typed (X ▸ meaning A X env) (ext (meaning A X env) env) (suc k) B
        (Formers.universe k)
    → Typed (X ▸ meaning A X env) (ext (meaning A X env) env) k t B
    → Typed X env (m ⊔ℕ k) (Formers.lambda m k A B t) (Formers.pi m k A B)
  lambda-typed m k A B t X env TA TB Tt =
    let a = meaning A X env
        b = meaning B (X ▸ a) (ext a env)
        sA = Interpretation.Typed.term-stable TA
        cA = Interpretation.Typed.term-type TA
        sB = Interpretation.Typed.term-stable TB
        cB = Interpretation.Typed.term-type TB
        T = pi-typed m k A B X env TA TB
    in record
      { type-stable = Interpretation.Typed.term-stable T
      ; type-code = Interpretation.Typed.term-type T
      ; term-stable =
          lambda-stable m k A B t X env sA cA sB cB
            (Interpretation.Typed.term-stable Tt)
            (Interpretation.Typed.term-type Tt)
      ; term-type =
          ap type-of (lambda-value m k A B t X env) ∙
            (lambda-type m k a b (meaning t (X ▸ a) (ext a env)) cA cB
                (Interpretation.Typed.term-type Tt) ∙
              pi-value m k A B X env ⁻¹)
      }

  application-typed :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (f x : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Typed X env (suc m) A (Formers.universe m)
    → Typed (X ▸ meaning A X env) (ext (meaning A X env) env) (suc k) B
        (Formers.universe k)
    → Typed X env (m ⊔ℕ k) f (Formers.pi m k A B)
    → Typed X env m x A
    → Typed X env k (Formers.application m k A B f x)
        (Formers.instantiate B x)
  application-typed m k A B f x X env TA TB Tf Tx =
    let a = meaning A X env
        b = meaning B (X ▸ a) (ext a env)
        sA = Interpretation.Typed.term-stable TA
        cA = Interpretation.Typed.term-type TA
        sB = Interpretation.Typed.term-stable TB
        cB = Interpretation.Typed.term-type TB
        sx = Interpretation.Typed.term-stable Tx
        tx = Interpretation.Typed.term-type Tx
        tf = Interpretation.Typed.term-type Tf ∙ pi-value m k A B X env
        e = instantiate-at m B x X a env sB sx tx cA
        T = instance-as-type m k A B x X env TB Tx
    in record
      { type-stable = Interpretation.Typed.term-stable T
      ; type-code = Interpretation.Typed.term-type T
      ; term-stable =
          application-stable m k A B f x X env sA cA sB cB
            (Interpretation.Typed.term-stable Tf) tf sx tx
      ; term-type =
          ap type-of (application-value m k A B f x X env) ∙
            (application-type m k a b (meaning f X env) (meaning x X env)
                cA cB tf tx ∙
              e ⁻¹)
      }

  ----------------------------------------------------------------------
  -- β and η

  beta-value :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B t : Raw.Expression C (suc n)) (x : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Typed X env (suc m) A (Formers.universe m)
    → Typed (X ▸ meaning A X env) (ext (meaning A X env) env) (suc k) B
        (Formers.universe k)
    → Typed (X ▸ meaning A X env) (ext (meaning A X env) env) k t B
    → Typed X env m x A
    → meaning
        (Formers.application m k A B (Formers.lambda m k A B t) x) X env
      ＝ meaning (Formers.instantiate t x) X env
  beta-value m k A B t x X env TA TB Tt Tx =
    let a = meaning A X env
        b = meaning B (X ▸ a) (ext a env)
        u = meaning t (X ▸ a) (ext a env)
        cA = Interpretation.Typed.term-type TA
        cB = Interpretation.Typed.term-type TB
        sx = Interpretation.Typed.term-stable Tx
        tx = Interpretation.Typed.term-type Tx
    in application-value m k A B (Formers.lambda m k A B t) x X env ∙
         (ap (λ g → application m k a b g (meaning x X env))
             (lambda-value m k A B t X env) ∙
           (application-lambda m k a b u (meaning x X env) cA cB
               (Interpretation.Typed.term-type Tt) tx ∙
             instantiate-at m t x X a env
                 (Interpretation.Typed.term-stable Tt) sx tx cA ⁻¹))

  -- The body of the η-expansion of f.
  eta-body :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (f : Raw.Expression C n)
    → Raw.Expression C (suc n)
  eta-body {n} m k A B f =
    Formers.application m k (Formers.weaken A) (Formers.weaken-past n 1 1 B)
      (Formers.weaken f) (Tree.hole fzero)

  -- B weakened past its bound variable, at the extension by a [ p ].
  weakened-codomain :
    {n : ℕ} (m : ℕ) (B : Raw.Expression C (suc n)) (X : Ob) (a : Tm X)
    (env : Vec (Tm X) n) (cA : Code R m a)
    → Stable (meaning B) (X ▸ a) (ext a env)
    → meaning (Formers.weaken-past n 1 1 B) (X ▸ a ▸ a [ p ])
        (ext (a [ p ]) (ext a env))
      ＝ meaning B (X ▸ a) (ext a env) [ p ∘ p ⨾ q (a [ p ]) ]
  weakened-codomain {n} m B X a env cA sB =
    let e = under-type R m a p cA
        σ = extend a (p ∘ p) (q (a [ p ])) e
    in rename-value
           (Binding.lift (Raw.binding C) 1 (λ (y : Fin n) → 1 ↑ʳ y)) B
           (X ▸ a ▸ a [ p ]) (ext (a [ p ]) (ext a env)) ∙
         (ap (λ es → meaning B (X ▸ a ▸ a [ p ]) (q (a [ p ]) ∷ es))
             (tabulate-lookup (env [ p ]ᵉ [ p ]ᵉ) ∙
               Environment.[]ᵉ-∘ R env p p ⁻¹) ∙
           (ap (meaning B (X ▸ a ▸ a [ p ]))
               (Environment.ext-extend R m a env (p ∘ p) (q (a [ p ])) e
                      cA ⁻¹) ∙
             (sB (X ▸ a ▸ a [ p ]) σ ∙
               [⨾] a (meaning B (X ▸ a) (ext a env)) (p ∘ p)
                      (q (a [ p ])) e ⁻¹)))

  eta-value :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (f : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Typed X env (suc m) A (Formers.universe m)
    → Typed (X ▸ meaning A X env) (ext (meaning A X env) env) (suc k) B
        (Formers.universe k)
    → Typed X env (m ⊔ℕ k) f (Formers.pi m k A B)
    → meaning (Formers.lambda m k A B (eta-body m k A B f)) X env
      ＝ meaning f X env
  eta-value {n} m k A B f X env TA TB Tf =
    let a = meaning A X env
        b = meaning B (X ▸ a) (ext a env)
        sA = term-stable TA
        cA = term-type TA
        sB = term-stable TB
        cB = term-type TB
        tf = term-type Tf ∙ pi-value m k A B X env
        f′ = meaning (Formers.weaken f) (X ▸ a) (ext a env)
    in lambda-value m k A B (eta-body m k A B f) X env ∙
         (ap (lambda m k a b)
             (application-value m k (Formers.weaken A)
                 (Formers.weaken-past n 1 1 B) (Formers.weaken f)
                 (Tree.hole fzero) (X ▸ a) (ext a env) ∙
               (ap
                   (λ x → application m k x
                            (meaning (Formers.weaken-past n 1 1 B) (X ▸ a ▸ x)
                              (ext x (ext a env)))
                            f′ (q a))
                   (weaken-at A X a env sA) ∙
                 ap₂ (λ c g → application m k (a [ p ]) c g (q a))
                   (weakened-codomain m B X a env cA sB)
                   (weaken-at f X a env (term-stable Tf)))) ∙
           lambda-application m k a b (meaning f X env) cA cB tf)

  eta-typed :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (f : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Typed X env (suc m) A (Formers.universe m)
    → Typed (X ▸ meaning A X env) (ext (meaning A X env) env) (suc k) B
        (Formers.universe k)
    → Typed X env (m ⊔ℕ k) f (Formers.pi m k A B)
    → Typed X env (m ⊔ℕ k) (Formers.lambda m k A B (eta-body m k A B f))
        (Formers.pi m k A B)
  eta-typed m k A B f X env TA TB Tf = record
    { type-stable = type-stable Tf
    ; type-code = type-code Tf
    ; term-stable = λ Y τ →
        eta-value m k A B f Y (env [ τ ]ᵉ)
            (typed-[] X env (suc m) A (Formers.universe m) TA τ)
            (typed-under X env m (suc k) A B (Formers.universe k)
              (term-stable TA) (term-type TA) TB τ)
            (typed-[] X env (m ⊔ℕ k) f (Formers.pi m k A B) Tf τ) ∙
          (term-stable Tf Y τ ∙
            ap (λ s → s [ τ ]) (eta-value m k A B f X env TA TB Tf ⁻¹))
    ; term-type =
        ap type-of (eta-value m k A B f X env TA TB Tf) ∙ term-type Tf
    }

  ----------------------------------------------------------------------
  -- Congruence

  pi-equal :
    {n : ℕ} (m k : ℕ) (A A′ : Raw.Expression C n)
    (B B′ : Raw.Expression C (suc n)) (X : Ob) (env : Vec (Tm X) n)
    → meaning A X env ＝ meaning A′ X env
    → meaning B (X ▸ meaning A X env) (ext (meaning A X env) env)
      ＝ meaning B′ (X ▸ meaning A X env) (ext (meaning A X env) env)
    → meaning (Formers.pi m k A B) X env ＝ meaning (Formers.pi m k A′ B′) X env
  pi-equal m k A A′ B B′ X env eA eB =
    pi-value m k A B X env ∙
      (ap (pi m k (meaning A X env)) eB ∙
        (ap (λ x → pi m k x (meaning B′ (X ▸ x) (ext x env))) eA ∙
          pi-value m k A′ B′ X env ⁻¹))

  ----------------------------------------------------------------------
  -- The rules of Π

  sound :
    {j : Judgment C} (r : Block.Rule C j)
    → ((i : Fin (length (Block.premises r)))
       → Valid (list-lookup (Block.premises r) i))
    → Valid j
  sound (Block.formation Γ m k A B) h =
    let (vΓ , TA) = h fzero
        (_ , TB) = h (fsuc fzero)
    in vΓ , pi-typed m k A B (object Γ) (values Γ) TA TB
  sound (Block.introduction Γ m k A B t) h =
    let (vΓ , TA) = h fzero
        (_ , TB) = h (fsuc fzero)
        (_ , Tt) = h (fsuc (fsuc fzero))
    in vΓ , lambda-typed m k A B t (object Γ) (values Γ) TA TB Tt
  sound (Block.elimination Γ m k A B f a) h =
    let (vΓ , TA) = h fzero
        (_ , TB) = h (fsuc fzero)
        (_ , Tf) = h (fsuc (fsuc fzero))
        (_ , Ta) = h (fsuc (fsuc (fsuc fzero)))
    in vΓ , application-typed m k A B f a (object Γ) (values Γ) TA TB Tf Ta
  sound (Block.computation Γ m k A B t a) h =
    let (vΓ , TA) = h fzero
        (_ , TB) = h (fsuc fzero)
        (_ , Tt) = h (fsuc (fsuc fzero))
        (_ , Ta) = h (fsuc (fsuc (fsuc fzero)))
        X = object Γ
        env = values Γ
    in vΓ
       , application-typed m k A B (Formers.lambda m k A B t) a X env TA TB
           (lambda-typed m k A B t X env TA TB Tt) Ta
       , instance-typed m k A B t a X env TB Tt Ta
       , beta-value m k A B t a X env TA TB Tt Ta
  sound (Block.uniqueness Γ m k A B f) h =
    let (vΓ , TA) = h fzero
        (_ , TB) = h (fsuc fzero)
        (_ , Tf) = h (fsuc (fsuc fzero))
        X = object Γ
        env = values Γ
    in vΓ
       , eta-typed m k A B f X env TA TB Tf
       , Tf
       , eta-value m k A B f X env TA TB Tf
  sound (Block.formation-equal Γ m k A A′ B B′) h =
    let (vΓ , TA , TA′ , eA) = h fzero
        (_ , TB , TB′ , eB) = h (fsuc fzero)
        X = object Γ
        env = values Γ
    in vΓ
       , pi-typed m k A B X env TA TB
       , pi-typed m k A′ B′ X env TA′
           (typed-along X env (suc k) B′ (Formers.universe k) eA TB′)
       , pi-equal m k A A′ B B′ X env eA eB
  sound (Block.introduction-equal Γ m k A A′ B B′ t t′) h =
    let (vΓ , TA , TA′ , eA) = h fzero
        (_ , TB , TB′ , eB) = h (fsuc fzero)
        (_ , Tt , Tt′ , et) = h (fsuc (fsuc fzero))
        X = object Γ
        env = values Γ
        a = meaning A X env
        TP = pi-typed m k A B X env TA TB
        Tt″ = retype (X ▸ a) (ext a env) k t′ B′ B Tt′ (term-stable TB′)
                (term-type TB′) eB
    in vΓ
       , lambda-typed m k A B t X env TA TB Tt
       , retype X env (m ⊔ℕ k) (Formers.lambda m k A′ B′ t′)
           (Formers.pi m k A B) (Formers.pi m k A′ B′)
           (lambda-typed m k A′ B′ t′ X env TA′
             (typed-along X env (suc k) B′ (Formers.universe k) eA TB′)
             (typed-along X env k t′ B′ eA Tt″))
           (term-stable TP) (term-type TP)
           (pi-equal m k A A′ B B′ X env eA eB ⁻¹)
       , lambda-value m k A B t X env ∙
           (ap₂ (lambda m k a) eB et ∙
             (ap
                 (λ x → lambda m k x (meaning B′ (X ▸ x) (ext x env))
                          (meaning t′ (X ▸ x) (ext x env)))
                 eA ∙
               lambda-value m k A′ B′ t′ X env ⁻¹))
  sound (Block.elimination-equal Γ m k A A′ B B′ f f′ a a′) h =
    let (vΓ , TA , TA′ , eA) = h fzero
        (_ , TB , TB′ , eB) = h (fsuc fzero)
        (_ , Tf , Tf′ , ef) = h (fsuc (fsuc fzero))
        (_ , Ta , Ta′ , ea) = h (fsuc (fsuc (fsuc fzero)))
        X = object Γ
        env = values Γ
        α = meaning A X env
        TB″ = typed-along X env (suc k) B′ (Formers.universe k) eA TB′
        TP′ = pi-typed m k A′ B′ X env TA′ TB″
        T = application-typed m k A′ B′ f′ a′ X env TA′ TB″
              (retype X env (m ⊔ℕ k) f′ (Formers.pi m k A′ B′)
                (Formers.pi m k A B) Tf′ (term-stable TP′) (term-type TP′)
                (pi-equal m k A A′ B B′ X env eA eB))
              (retype X env m a′ A′ A Ta′ (term-stable TA′) (term-type TA′)
                eA)
        TL = application-typed m k A B f a X env TA TB Tf Ta
        sx = term-stable Ta
        tx = term-type Ta
        sx′ = term-stable Ta′
        tx′ = term-type Ta′ ∙ eA
    in vΓ
       , TL
       , retype X env k (Formers.application m k A′ B′ f′ a′)
           (Formers.instantiate B a) (Formers.instantiate B′ a′) T
           (type-stable TL) (type-code TL)
           (instantiate-at m B′ a′ X (meaning A′ X env) env
               (term-stable TB″) sx′ tx′ (term-type TA′) ∙
             (ap₂
                 (λ y z → meaning B′ (X ▸ y) (ext y env) [ id ⨾ z ])
                 (eA ⁻¹) (ea ⁻¹) ∙
               (ap (λ c → c [ id ⨾ meaning a X env ]) (eB ⁻¹) ∙
                 instantiate-at m B a X α env (term-stable TB) sx tx
                     (term-type TA) ⁻¹)))
       , application-value m k A B f a X env ∙
           (ap₃ (application m k α) eB ef ea ∙
             (ap
                 (λ y → application m k y (meaning B′ (X ▸ y) (ext y env))
                          (meaning f′ X env) (meaning a′ X env))
                 eA ∙
               application-value m k A′ B′ f′ a′ X env ⁻¹))
