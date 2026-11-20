{-# OPTIONS --safe --without-K --no-projection-like #-}

module SPT.MartinLof.Soundness.Sum where

-- Soundness of the rules of + (`sound`). The values of A + B, inl and inr
-- are the model's operations at the values of their children; case's
-- value reads the motive at the extension by the sum and the methods at
-- the extensions by the summands (`case-value`). Each is stable by its
-- stability law (`sum-stable`, `left-stable`, `right-stable`,
-- `case-stable`) and has its type by its typing law. The methods' types
-- M (inl x) and M (inr y) have the values the model's laws ask for
-- (`on-left-value`, `on-right-value`), since inl and inr of the variable
-- are stable (`left-variable-stable`, `right-variable-stable`). At inl a
-- and inr b, case computes by the model's β; the instance of a method has
-- the motive's instance as type (`left-instance-value`,
-- `right-instance-value`).

open import SPT.Base hiding (Lift; _∘_; id; lift; lower; zero)
open import SPT.Foundation.Vectors.Tabulation using (tabulate-lookup)
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Tree as Tree
import SPT.MartinLof.Formers as Formers
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Judgment using (Judgment)
import SPT.MartinLof.Rules.Sum as Block
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
  (let weaken-stable = Instances.weaken-stable R lifting products pairs paths
                         trees nothing one sums numbers operations subuniverses
                           constant)
  (let weaken-at = Instances.weaken-at R lifting products pairs paths trees
                     nothing one sums numbers operations subuniverses constant)
  (let instantiate-value = Instances.instantiate-value R lifting products
                             pairs paths trees nothing one sums numbers
                             operations subuniverses constant)
  (let instantiate-past-value = Instances.instantiate-past-value R lifting
                                  products pairs paths trees nothing one sums
                                  numbers operations subuniverses constant)
  (let instantiate-at = Instances.instantiate-at R lifting products pairs
                          paths trees nothing one sums numbers
                          operations subuniverses constant)
  (let as-type = Typing.as-type R lifting products pairs paths trees nothing
                   one sums numbers operations subuniverses constant)
  (let retype = Typing.retype R lifting products pairs paths trees nothing
                  one sums numbers operations subuniverses constant)
  (let typed-along = Typing.typed-along R lifting products pairs paths trees
                       nothing one sums numbers operations subuniverses
                         constant)
  (let under-stable = Typing.under-stable R lifting products pairs paths
                        trees nothing one sums numbers operations subuniverses
                          constant)
  (let stable-extend = Typing.stable-extend R lifting products pairs paths
                         trees nothing one sums numbers operations subuniverses
                           constant)
  (let lift-stable = Typing.lift-stable R lifting products pairs paths trees
                       nothing one sums numbers operations subuniverses
                         constant)
  (let weaken-cons = Typing.weaken-cons R lifting products pairs paths trees
                       nothing one sums numbers operations subuniverses
                         constant)
  (let instance-as-type = Typing.instance-as-type R lifting products pairs
                            paths trees nothing one sums numbers
                            operations subuniverses constant)
  (let instance-typed = Typing.instance-typed R lifting products pairs paths
                          trees nothing one sums numbers operations
                            subuniverses constant)
  (let instantiate-equal = Typing.instantiate-equal R lifting products pairs
                             paths trees nothing one sums numbers
                             operations subuniverses constant)
  (let type-stable = Interpretation.Typed.type-stable)
  (let type-code = Interpretation.Typed.type-code)
  (let term-stable = Interpretation.Typed.term-stable)
  (let term-type = Interpretation.Typed.term-type)
  where

  ----------------------------------------------------------------------
  -- Values

  case-value :
    {n : ℕ} (m k l : ℕ) (A B : Raw.Expression C n)
    (M c d : Raw.Expression C (suc n)) (s : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → meaning (Formers.case m k l A B M c d s) X env
      ＝ case m k l (meaning A X env) (meaning B X env)
          (meaning M (X ▸ sum m k (meaning A X env) (meaning B X env))
            (ext (sum m k (meaning A X env) (meaning B X env)) env))
          (meaning c (X ▸ meaning A X env) (ext (meaning A X env) env))
          (meaning d (X ▸ meaning B X env) (ext (meaning B X env) env))
          (meaning s X env)
  case-value m k l A B M c d s X env =
    let a = meaning A X env
        b = meaning B X env
        w = sum m k a b
    in ap₃ (λ N c′ d′ → case m k l a b N c′ d′ (meaning s X env))
         (bound-meaning 1 M (X ▸ w) (ext w env))
         (bound-meaning 1 c (X ▸ a) (ext a env))
         (bound-meaning 1 d (X ▸ b) (ext b env))

  ----------------------------------------------------------------------
  -- Stability

  sum-stable :
    {n : ℕ} (m k : ℕ) (A B : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Stable (meaning A) X env → Code R m (meaning A X env)
    → Stable (meaning B) X env → Code R k (meaning B X env)
    → Stable (meaning (Formers.sum m k A B)) X env
  sum-stable m k A B X env sA cA sB cB Y τ =
    ap₂ (sum m k) (sA Y τ) (sB Y τ) ∙
      sum-[] m k (meaning A X env) (meaning B X env) τ cA cB ⁻¹

  left-stable :
    {n : ℕ} (m k : ℕ) (A B x : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Stable (meaning A) X env → Code R m (meaning A X env)
    → Stable (meaning B) X env → Code R k (meaning B X env)
    → Stable (meaning x) X env → type-of (meaning x X env) ＝ meaning A X env
    → Stable (meaning (Formers.left m k A B x)) X env
  left-stable m k A B x X env sA cA sB cB sx tx Y τ =
    ap₃ (left m k) (sA Y τ) (sB Y τ) (sx Y τ) ∙
      left-[] m k (meaning A X env) (meaning B X env) (meaning x X env) τ
          cA cB tx ⁻¹

  right-stable :
    {n : ℕ} (m k : ℕ) (A B y : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Stable (meaning A) X env → Code R m (meaning A X env)
    → Stable (meaning B) X env → Code R k (meaning B X env)
    → Stable (meaning y) X env → type-of (meaning y X env) ＝ meaning B X env
    → Stable (meaning (Formers.right m k A B y)) X env
  right-stable m k A B y X env sA cA sB cB sy ty Y τ =
    ap₃ (right m k) (sA Y τ) (sB Y τ) (sy Y τ) ∙
      right-[] m k (meaning A X env) (meaning B X env) (meaning y X env) τ
          cA cB ty ⁻¹

  case-stable :
    {n : ℕ} (m k l : ℕ) (A B : Raw.Expression C n)
    (M c d : Raw.Expression C (suc n)) (s : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Stable (meaning A) X env → (cA : Code R m (meaning A X env))
    → Stable (meaning B) X env → (cB : Code R k (meaning B X env))
    → Stable (meaning M) (X ▸ sum m k (meaning A X env) (meaning B X env))
        (ext (sum m k (meaning A X env) (meaning B X env)) env)
    → Code R l
        (meaning M (X ▸ sum m k (meaning A X env) (meaning B X env))
          (ext (sum m k (meaning A X env) (meaning B X env)) env))
    → Stable (meaning c) (X ▸ meaning A X env) (ext (meaning A X env) env)
    → type-of (meaning c (X ▸ meaning A X env) (ext (meaning A X env) env))
      ＝ meaning M (X ▸ sum m k (meaning A X env) (meaning B X env))
          (ext (sum m k (meaning A X env) (meaning B X env)) env)
          [ p ⨾ left m k (meaning A X env [ p ]) (meaning B X env [ p ])
                  (q (meaning A X env)) ]
    → Stable (meaning d) (X ▸ meaning B X env) (ext (meaning B X env) env)
    → type-of (meaning d (X ▸ meaning B X env) (ext (meaning B X env) env))
      ＝ meaning M (X ▸ sum m k (meaning A X env) (meaning B X env))
          (ext (sum m k (meaning A X env) (meaning B X env)) env)
          [ p ⨾ right m k (meaning A X env [ p ]) (meaning B X env [ p ])
                  (q (meaning B X env)) ]
    → Stable (meaning s) X env
    → type-of (meaning s X env) ＝ sum m k (meaning A X env) (meaning B X env)
    → Stable (meaning (Formers.case m k l A B M c d s)) X env
  case-stable m k l A B M c d s X env sA cA sB cB sM cM sc tc sd td ss ts
    Y τ =
    let a = meaning A X env
        b = meaning B X env
        w = sum m k a b
        w′ = sum m k (a [ τ ]) (b [ τ ])
        e = q-type (m ⊔ℕ k) w′
                (sum-type m k (a [ τ ]) (b [ τ ]) (code-[] R m a τ cA)
                  (code-[] R k b τ cB)) ∙
              (ap (λ t → t [ p ]) (sum-[] m k a b τ cA cB ⁻¹) ∙
                [∘] w τ p ⁻¹)
        M₀ = meaning M (X ▸ w) (ext w env)
        c₀ = meaning c (X ▸ a) (ext a env)
        d₀ = meaning d (X ▸ b) (ext b env)
        envτ = env [ τ ]ᵉ
    in case-value m k l A B M c d s Y envτ ∙
         (ap₂
             (λ x y → case m k l x y
                (meaning M (Y ▸ sum m k x y) (ext (sum m k x y) envτ))
                (meaning c (Y ▸ x) (ext x envτ))
                (meaning d (Y ▸ y) (ext y envτ)) (meaning s Y envτ))
             (sA Y τ) (sB Y τ) ∙
           (ap₂
               (λ N c′ → case m k l (a [ τ ]) (b [ τ ]) N c′
                           (meaning d (Y ▸ b [ τ ]) (ext (b [ τ ]) envτ))
                           (meaning s Y envτ))
               (lift-stable (meaning M) (m ⊔ℕ k) X w env
                 (sum-type m k a b cA cB) sM τ w′ envτ e refl)
               (under-stable m c X a env cA sc τ) ∙
             (ap₂
                 (case m k l (a [ τ ]) (b [ τ ]) (M₀ [ τ ∘ p ⨾ q w′ ])
                   (c₀ [ τ ∘ p ⨾ q (a [ τ ]) ]))
                 (under-stable k d X b env cB sd τ) (ss Y τ) ∙
               (case-[] m k l a b M₀ c₀ d₀ (meaning s X env) τ cA cB cM
                     tc td ts ⁻¹ ∙
                 ap (λ t → t [ τ ])
                   (case-value m k l A B M c d s X env ⁻¹)))))

  ----------------------------------------------------------------------
  -- Typing

  sum-typed :
    {n : ℕ} (m k : ℕ) (A B : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Typed X env (suc m) A (Formers.universe m)
    → Typed X env (suc k) B (Formers.universe k)
    → Typed X env (suc (m ⊔ℕ k)) (Formers.sum m k A B)
        (Formers.universe (m ⊔ℕ k))
  sum-typed m k A B X env TA TB =
    as-type X env (m ⊔ℕ k) (Formers.sum m k A B)
      (sum-stable m k A B X env (term-stable TA) (term-type TA)
        (term-stable TB) (term-type TB))
      (sum-type m k (meaning A X env) (meaning B X env) (term-type TA)
        (term-type TB))

  left-typed :
    {n : ℕ} (m k : ℕ) (A B x : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Typed X env (suc m) A (Formers.universe m)
    → Typed X env (suc k) B (Formers.universe k)
    → Typed X env m x A
    → Typed X env (m ⊔ℕ k) (Formers.left m k A B x) (Formers.sum m k A B)
  left-typed m k A B x X env TA TB Tx =
    let T = sum-typed m k A B X env TA TB
    in record
      { type-stable = term-stable T
      ; type-code = term-type T
      ; term-stable =
          left-stable m k A B x X env (term-stable TA) (term-type TA)
            (term-stable TB) (term-type TB) (term-stable Tx) (term-type Tx)
      ; term-type =
          left-type m k (meaning A X env) (meaning B X env) (meaning x X env)
            (term-type TA) (term-type TB) (term-type Tx)
      }

  right-typed :
    {n : ℕ} (m k : ℕ) (A B y : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Typed X env (suc m) A (Formers.universe m)
    → Typed X env (suc k) B (Formers.universe k)
    → Typed X env k y B
    → Typed X env (m ⊔ℕ k) (Formers.right m k A B y) (Formers.sum m k A B)
  right-typed m k A B y X env TA TB Ty =
    let T = sum-typed m k A B X env TA TB
    in record
      { type-stable = term-stable T
      ; type-code = term-type T
      ; term-stable =
          right-stable m k A B y X env (term-stable TA) (term-type TA)
            (term-stable TB) (term-type TB) (term-stable Ty) (term-type Ty)
      ; term-type =
          right-type m k (meaning A X env) (meaning B X env) (meaning y X env)
            (term-type TA) (term-type TB) (term-type Ty)
      }

  ----------------------------------------------------------------------
  -- The methods' types

  -- inl of the variable of the extension by A, and inr of that by B.
  left-variable-stable :
    {n : ℕ} (m k : ℕ) (A B : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Stable (meaning A) X env → Code R m (meaning A X env)
    → Stable (meaning B) X env → Code R k (meaning B X env)
    → Stable
        (meaning
          (Formers.left m k (Formers.weaken A) (Formers.weaken B)
            (Tree.hole fzero)))
        (X ▸ meaning A X env) (ext (meaning A X env) env)
  left-variable-stable m k A B X env sA cA sB cB =
    let a = meaning A X env
        b = meaning B X env
        eA = weaken-at A X a env sA
        eB = weaken-at B X a env sB
    in left-stable m k (Formers.weaken A) (Formers.weaken B)
         (Tree.hole fzero) (X ▸ a) (ext a env)
         (weaken-stable A X a env sA)
         (transport (Code R m) (eA ⁻¹) (code-[] R m a p cA))
         (weaken-stable B X a env sB)
         (transport (Code R k) (eB ⁻¹) (code-[] R k b p cB))
         (Environment.stable-lookup R fzero (X ▸ a) (ext a env))
         (q-type m a cA ∙ eA ⁻¹)

  right-variable-stable :
    {n : ℕ} (m k : ℕ) (A B : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Stable (meaning A) X env → Code R m (meaning A X env)
    → Stable (meaning B) X env → Code R k (meaning B X env)
    → Stable
        (meaning
          (Formers.right m k (Formers.weaken A) (Formers.weaken B)
            (Tree.hole fzero)))
        (X ▸ meaning B X env) (ext (meaning B X env) env)
  right-variable-stable m k A B X env sA cA sB cB =
    let a = meaning A X env
        b = meaning B X env
        eA = weaken-at A X b env sA
        eB = weaken-at B X b env sB
    in right-stable m k (Formers.weaken A) (Formers.weaken B)
         (Tree.hole fzero) (X ▸ b) (ext b env)
         (weaken-stable A X b env sA)
         (transport (Code R m) (eA ⁻¹) (code-[] R m a p cA))
         (weaken-stable B X b env sB)
         (transport (Code R k) (eB ⁻¹) (code-[] R k b p cB))
         (Environment.stable-lookup R fzero (X ▸ b) (ext b env))
         (q-type k b cB ∙ eB ⁻¹)

  on-left-value :
    {n : ℕ} (m k : ℕ) (A B : Raw.Expression C n)
    (M : Raw.Expression C (suc n)) (X : Ob) (env : Vec (Tm X) n)
    → Stable (meaning A) X env → Code R m (meaning A X env)
    → Stable (meaning B) X env → Code R k (meaning B X env)
    → Stable (meaning M) (X ▸ sum m k (meaning A X env) (meaning B X env))
        (ext (sum m k (meaning A X env) (meaning B X env)) env)
    → meaning (Block.on-left m k A B M) (X ▸ meaning A X env)
        (ext (meaning A X env) env)
      ＝ meaning M (X ▸ sum m k (meaning A X env) (meaning B X env))
          (ext (sum m k (meaning A X env) (meaning B X env)) env)
          [ p ⨾ left m k (meaning A X env [ p ]) (meaning B X env [ p ])
                  (q (meaning A X env)) ]
  on-left-value m k A B M X env sA cA sB cB sM =
    let a = meaning A X env
        b = meaning B X env
        w = sum m k a b
        L = Formers.left m k (Formers.weaken A) (Formers.weaken B)
              (Tree.hole fzero)
        tL = left-type m k (a [ p ]) (b [ p ]) (q a) (code-[] R m a p cA)
                 (code-[] R k b p cB) (q-type m a cA) ∙
               sum-[] m k a b p cA cB ⁻¹
    in instantiate-past-value 1 M L (X ▸ a) (ext a env)
           (left-variable-stable m k A B X env sA cA sB cB) ∙
         (ap₂ (λ x es → meaning M (X ▸ a) (x ∷ es))
             (ap₂ (λ u v → left m k u v (q a)) (weaken-at A X a env sA)
               (weaken-at B X a env sB))
             (tabulate-lookup (env [ p ]ᵉ)) ∙
           stable-extend (meaning M) (m ⊔ℕ k) X w env (sum-type m k a b cA cB)
             sM p (left m k (a [ p ]) (b [ p ]) (q a)) tL)

  on-right-value :
    {n : ℕ} (m k : ℕ) (A B : Raw.Expression C n)
    (M : Raw.Expression C (suc n)) (X : Ob) (env : Vec (Tm X) n)
    → Stable (meaning A) X env → Code R m (meaning A X env)
    → Stable (meaning B) X env → Code R k (meaning B X env)
    → Stable (meaning M) (X ▸ sum m k (meaning A X env) (meaning B X env))
        (ext (sum m k (meaning A X env) (meaning B X env)) env)
    → meaning (Block.on-right m k A B M) (X ▸ meaning B X env)
        (ext (meaning B X env) env)
      ＝ meaning M (X ▸ sum m k (meaning A X env) (meaning B X env))
          (ext (sum m k (meaning A X env) (meaning B X env)) env)
          [ p ⨾ right m k (meaning A X env [ p ]) (meaning B X env [ p ])
                  (q (meaning B X env)) ]
  on-right-value m k A B M X env sA cA sB cB sM =
    let a = meaning A X env
        b = meaning B X env
        w = sum m k a b
        L = Formers.right m k (Formers.weaken A) (Formers.weaken B)
              (Tree.hole fzero)
        tL = right-type m k (a [ p ]) (b [ p ]) (q b) (code-[] R m a p cA)
                 (code-[] R k b p cB) (q-type k b cB) ∙
               sum-[] m k a b p cA cB ⁻¹
    in instantiate-past-value 1 M L (X ▸ b) (ext b env)
           (right-variable-stable m k A B X env sA cA sB cB) ∙
         (ap₂ (λ y es → meaning M (X ▸ b) (y ∷ es))
             (ap₂ (λ u v → right m k u v (q b)) (weaken-at A X b env sA)
               (weaken-at B X b env sB))
             (tabulate-lookup (env [ p ]ᵉ)) ∙
           stable-extend (meaning M) (m ⊔ℕ k) X w env (sum-type m k a b cA cB)
             sM p (right m k (a [ p ]) (b [ p ]) (q b)) tL)

  left-method :
    {n : ℕ} (m k l : ℕ) (A B : Raw.Expression C n)
    (M c : Raw.Expression C (suc n)) (X : Ob) (env : Vec (Tm X) n)
    → Typed X env (suc m) A (Formers.universe m)
    → Typed X env (suc k) B (Formers.universe k)
    → Typed (X ▸ sum m k (meaning A X env) (meaning B X env))
        (ext (sum m k (meaning A X env) (meaning B X env)) env) (suc l) M
        (Formers.universe l)
    → Typed (X ▸ meaning A X env) (ext (meaning A X env) env) l c
        (Block.on-left m k A B M)
    → type-of (meaning c (X ▸ meaning A X env) (ext (meaning A X env) env))
      ＝ meaning M (X ▸ sum m k (meaning A X env) (meaning B X env))
          (ext (sum m k (meaning A X env) (meaning B X env)) env)
          [ p ⨾ left m k (meaning A X env [ p ]) (meaning B X env [ p ])
                  (q (meaning A X env)) ]
  left-method m k l A B M c X env TA TB TM Tc =
    term-type Tc ∙
      on-left-value m k A B M X env (term-stable TA) (term-type TA)
        (term-stable TB) (term-type TB) (term-stable TM)

  right-method :
    {n : ℕ} (m k l : ℕ) (A B : Raw.Expression C n)
    (M d : Raw.Expression C (suc n)) (X : Ob) (env : Vec (Tm X) n)
    → Typed X env (suc m) A (Formers.universe m)
    → Typed X env (suc k) B (Formers.universe k)
    → Typed (X ▸ sum m k (meaning A X env) (meaning B X env))
        (ext (sum m k (meaning A X env) (meaning B X env)) env) (suc l) M
        (Formers.universe l)
    → Typed (X ▸ meaning B X env) (ext (meaning B X env) env) l d
        (Block.on-right m k A B M)
    → type-of (meaning d (X ▸ meaning B X env) (ext (meaning B X env) env))
      ＝ meaning M (X ▸ sum m k (meaning A X env) (meaning B X env))
          (ext (sum m k (meaning A X env) (meaning B X env)) env)
          [ p ⨾ right m k (meaning A X env [ p ]) (meaning B X env [ p ])
                  (q (meaning B X env)) ]
  right-method m k l A B M d X env TA TB TM Td =
    term-type Td ∙
      on-right-value m k A B M X env (term-stable TA) (term-type TA)
        (term-stable TB) (term-type TB) (term-stable TM)

  ----------------------------------------------------------------------
  -- Case analysis

  case-typed :
    {n : ℕ} (m k l : ℕ) (A B : Raw.Expression C n)
    (M c d : Raw.Expression C (suc n)) (s : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Typed X env (suc m) A (Formers.universe m)
    → Typed X env (suc k) B (Formers.universe k)
    → Typed (X ▸ sum m k (meaning A X env) (meaning B X env))
        (ext (sum m k (meaning A X env) (meaning B X env)) env) (suc l) M
        (Formers.universe l)
    → Stable (meaning c) (X ▸ meaning A X env) (ext (meaning A X env) env)
    → type-of (meaning c (X ▸ meaning A X env) (ext (meaning A X env) env))
      ＝ meaning M (X ▸ sum m k (meaning A X env) (meaning B X env))
          (ext (sum m k (meaning A X env) (meaning B X env)) env)
          [ p ⨾ left m k (meaning A X env [ p ]) (meaning B X env [ p ])
                  (q (meaning A X env)) ]
    → Stable (meaning d) (X ▸ meaning B X env) (ext (meaning B X env) env)
    → type-of (meaning d (X ▸ meaning B X env) (ext (meaning B X env) env))
      ＝ meaning M (X ▸ sum m k (meaning A X env) (meaning B X env))
          (ext (sum m k (meaning A X env) (meaning B X env)) env)
          [ p ⨾ right m k (meaning A X env [ p ]) (meaning B X env [ p ])
                  (q (meaning B X env)) ]
    → Typed X env (m ⊔ℕ k) s (Formers.sum m k A B)
    → Typed X env l (Formers.case m k l A B M c d s) (Formers.instantiate M s)
  case-typed m k l A B M c d s X env TA TB TM sc tc sd td Ts =
    let a = meaning A X env
        b = meaning B X env
        w = sum m k a b
        cA = term-type TA
        cB = term-type TB
        T = instance-as-type (m ⊔ℕ k) l (Formers.sum m k A B) M s X env TM Ts
    in record
      { type-stable = term-stable T
      ; type-code = term-type T
      ; term-stable =
          case-stable m k l A B M c d s X env (term-stable TA) cA
            (term-stable TB) cB (term-stable TM) (term-type TM) sc tc sd td
            (term-stable Ts) (term-type Ts)
      ; term-type =
          ap type-of (case-value m k l A B M c d s X env) ∙
            (case-type m k l a b (meaning M (X ▸ w) (ext w env))
                (meaning c (X ▸ a) (ext a env)) (meaning d (X ▸ b) (ext b env))
                (meaning s X env) cA cB (term-type TM) tc td (term-type Ts) ∙
              instantiate-at (m ⊔ℕ k) M s X w env (term-stable TM)
                  (term-stable Ts) (term-type Ts) (sum-type m k a b cA cB) ⁻¹)
      }

  -- The left method's instance at x has the motive's type at inl x.
  left-instance-value :
    {n : ℕ} (m k : ℕ) (A B : Raw.Expression C n)
    (M : Raw.Expression C (suc n)) (x : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Stable (meaning A) X env → Code R m (meaning A X env)
    → Stable (meaning B) X env → Code R k (meaning B X env)
    → Stable (meaning x) X env → type-of (meaning x X env) ＝ meaning A X env
    → meaning (Formers.instantiate (Block.on-left m k A B M) x) X env
      ＝ meaning (Formers.instantiate M (Formers.left m k A B x)) X env
  left-instance-value m k A B M x X env sA cA sB cB sx tx =
    let a = meaning A X env
        x′ = meaning x X env
        L = Formers.left m k (Formers.weaken A) (Formers.weaken B)
              (Tree.hole fzero)
    in instantiate-value (Block.on-left m k A B M) x X env sx ∙
         (instantiate-past-value 1 M L X (x′ ∷ env)
             (Environment.stable-section R m (meaning L) a x′ env tx cA
               (left-variable-stable m k A B X env sA cA sB cB)) ∙
           (ap₂ (λ y es → meaning M X (y ∷ es))
               (ap₂ (λ u v → left m k u v x′) (weaken-cons A X x′ env)
                 (weaken-cons B X x′ env))
               (tabulate-lookup env) ∙
             instantiate-value M (Formers.left m k A B x) X env
                 (left-stable m k A B x X env sA cA sB cB sx tx) ⁻¹))

  right-instance-value :
    {n : ℕ} (m k : ℕ) (A B : Raw.Expression C n)
    (M : Raw.Expression C (suc n)) (y : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Stable (meaning A) X env → Code R m (meaning A X env)
    → Stable (meaning B) X env → Code R k (meaning B X env)
    → Stable (meaning y) X env → type-of (meaning y X env) ＝ meaning B X env
    → meaning (Formers.instantiate (Block.on-right m k A B M) y) X env
      ＝ meaning (Formers.instantiate M (Formers.right m k A B y)) X env
  right-instance-value m k A B M y X env sA cA sB cB sy ty =
    let b = meaning B X env
        y′ = meaning y X env
        L = Formers.right m k (Formers.weaken A) (Formers.weaken B)
              (Tree.hole fzero)
    in instantiate-value (Block.on-right m k A B M) y X env sy ∙
         (instantiate-past-value 1 M L X (y′ ∷ env)
             (Environment.stable-section R k (meaning L) b y′ env ty cB
               (right-variable-stable m k A B X env sA cA sB cB)) ∙
           (ap₂ (λ z es → meaning M X (z ∷ es))
               (ap₂ (λ u v → right m k u v y′) (weaken-cons A X y′ env)
                 (weaken-cons B X y′ env))
               (tabulate-lookup env) ∙
             instantiate-value M (Formers.right m k A B y) X env
                 (right-stable m k A B y X env sA cA sB cB sy ty) ⁻¹))

  ----------------------------------------------------------------------
  -- The rules of +

  sound :
    {j : Judgment C} (r : Block.Rule C j)
    → ((i : Fin (length (Block.premises r)))
       → Valid (list-lookup (Block.premises r) i))
    → Valid j
  sound (Block.formation Γ m k A B) h =
    let (vΓ , TA) = h fzero
        (_ , TB) = h (fsuc fzero)
    in vΓ , sum-typed m k A B (object Γ) (values Γ) TA TB
  sound (Block.left-introduction Γ m k A B x) h =
    let (vΓ , TA) = h fzero
        (_ , TB) = h (fsuc fzero)
        (_ , Tx) = h (fsuc (fsuc fzero))
    in vΓ , left-typed m k A B x (object Γ) (values Γ) TA TB Tx
  sound (Block.right-introduction Γ m k A B y) h =
    let (vΓ , TA) = h fzero
        (_ , TB) = h (fsuc fzero)
        (_ , Ty) = h (fsuc (fsuc fzero))
    in vΓ , right-typed m k A B y (object Γ) (values Γ) TA TB Ty
  sound (Block.elimination Γ m k l A B M c d s) h =
    let (vΓ , TA) = h fzero
        (_ , TB) = h (fsuc fzero)
        (_ , TM) = h (fsuc (fsuc fzero))
        (_ , Tc) = h (fsuc (fsuc (fsuc fzero)))
        (_ , Td) = h (fsuc (fsuc (fsuc (fsuc fzero))))
        (_ , Ts) = h (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))
        X = object Γ
        env = values Γ
    in vΓ
       , case-typed m k l A B M c d s X env TA TB TM (term-stable Tc)
           (left-method m k l A B M c X env TA TB TM Tc) (term-stable Td)
           (right-method m k l A B M d X env TA TB TM Td) Ts
  sound (Block.left-computation Γ m k l A B M c d x) h =
    let (vΓ , TA) = h fzero
        (_ , TB) = h (fsuc fzero)
        (_ , TM) = h (fsuc (fsuc fzero))
        (_ , Tc) = h (fsuc (fsuc (fsuc fzero)))
        (_ , Td) = h (fsuc (fsuc (fsuc (fsuc fzero))))
        (_ , Tx) = h (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))
        X = object Γ
        env = values Γ
        a = meaning A X env
        b = meaning B X env
        w = sum m k a b
        cA = term-type TA
        cB = term-type TB
        tc = left-method m k l A B M c X env TA TB TM Tc
        td = right-method m k l A B M d X env TA TB TM Td
        T = case-typed m k l A B M c d (Formers.left m k A B x) X env TA TB TM
              (term-stable Tc) tc (term-stable Td) td
              (left-typed m k A B x X env TA TB Tx)
        TC = as-type (X ▸ a) (ext a env) l (Block.on-left m k A B M)
               (type-stable Tc) (type-code Tc)
    in vΓ
       , T
       , retype X env l (Formers.instantiate c x)
           (Formers.instantiate M (Formers.left m k A B x))
           (Formers.instantiate (Block.on-left m k A B M) x)
           (instance-typed m l A (Block.on-left m k A B M) c x X env TC Tc Tx)
           (type-stable T) (type-code T)
           (left-instance-value m k A B M x X env (term-stable TA) cA
             (term-stable TB) cB (term-stable Tx) (term-type Tx))
       , case-value m k l A B M c d (Formers.left m k A B x) X env ∙
           (case-left m k l a b (meaning M (X ▸ w) (ext w env))
               (meaning c (X ▸ a) (ext a env)) (meaning d (X ▸ b) (ext b env))
               (meaning x X env) cA cB (term-type TM) tc td (term-type Tx) ∙
             instantiate-at m c x X a env (term-stable Tc) (term-stable Tx)
                 (term-type Tx) cA ⁻¹)
  sound (Block.right-computation Γ m k l A B M c d y) h =
    let (vΓ , TA) = h fzero
        (_ , TB) = h (fsuc fzero)
        (_ , TM) = h (fsuc (fsuc fzero))
        (_ , Tc) = h (fsuc (fsuc (fsuc fzero)))
        (_ , Td) = h (fsuc (fsuc (fsuc (fsuc fzero))))
        (_ , Ty) = h (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))
        X = object Γ
        env = values Γ
        a = meaning A X env
        b = meaning B X env
        w = sum m k a b
        cA = term-type TA
        cB = term-type TB
        tc = left-method m k l A B M c X env TA TB TM Tc
        td = right-method m k l A B M d X env TA TB TM Td
        T = case-typed m k l A B M c d (Formers.right m k A B y) X env TA TB
              TM (term-stable Tc) tc (term-stable Td) td
              (right-typed m k A B y X env TA TB Ty)
        TD = as-type (X ▸ b) (ext b env) l (Block.on-right m k A B M)
               (type-stable Td) (type-code Td)
    in vΓ
       , T
       , retype X env l (Formers.instantiate d y)
           (Formers.instantiate M (Formers.right m k A B y))
           (Formers.instantiate (Block.on-right m k A B M) y)
           (instance-typed k l B (Block.on-right m k A B M) d y X env TD Td Ty)
           (type-stable T) (type-code T)
           (right-instance-value m k A B M y X env (term-stable TA) cA
             (term-stable TB) cB (term-stable Ty) (term-type Ty))
       , case-value m k l A B M c d (Formers.right m k A B y) X env ∙
           (case-right m k l a b (meaning M (X ▸ w) (ext w env))
               (meaning c (X ▸ a) (ext a env)) (meaning d (X ▸ b) (ext b env))
               (meaning y X env) cA cB (term-type TM) tc td (term-type Ty) ∙
             instantiate-at k d y X b env (term-stable Td) (term-stable Ty)
                 (term-type Ty) cB ⁻¹)
  sound (Block.formation-equal Γ m k A A′ B B′) h =
    let (vΓ , TA , TA′ , eA) = h fzero
        (_ , TB , TB′ , eB) = h (fsuc fzero)
        X = object Γ
        env = values Γ
    in vΓ
       , sum-typed m k A B X env TA TB
       , sum-typed m k A′ B′ X env TA′ TB′
       , ap₂ (sum m k) eA eB
  sound (Block.left-introduction-equal Γ m k A A′ B B′ x x′) h =
    let (vΓ , TA , TA′ , eA) = h fzero
        (_ , TB , TB′ , eB) = h (fsuc fzero)
        (_ , Tx , Tx′ , ex) = h (fsuc (fsuc fzero))
        X = object Γ
        env = values Γ
        TS = sum-typed m k A B X env TA TB
    in vΓ
       , left-typed m k A B x X env TA TB Tx
       , retype X env (m ⊔ℕ k) (Formers.left m k A′ B′ x′) (Formers.sum m k A B)
           (Formers.sum m k A′ B′)
           (left-typed m k A′ B′ x′ X env TA′ TB′
             (retype X env m x′ A′ A Tx′ (term-stable TA′) (term-type TA′) eA))
           (term-stable TS) (term-type TS) (ap₂ (sum m k) eA eB ⁻¹)
       , ap₃ (left m k) eA eB ex
  sound (Block.right-introduction-equal Γ m k A A′ B B′ y y′) h =
    let (vΓ , TA , TA′ , eA) = h fzero
        (_ , TB , TB′ , eB) = h (fsuc fzero)
        (_ , Ty , Ty′ , ey) = h (fsuc (fsuc fzero))
        X = object Γ
        env = values Γ
        TS = sum-typed m k A B X env TA TB
    in vΓ
       , right-typed m k A B y X env TA TB Ty
       , retype X env (m ⊔ℕ k) (Formers.right m k A′ B′ y′)
           (Formers.sum m k A B) (Formers.sum m k A′ B′)
           (right-typed m k A′ B′ y′ X env TA′ TB′
             (retype X env k y′ B′ B Ty′ (term-stable TB′) (term-type TB′) eB))
           (term-stable TS) (term-type TS) (ap₂ (sum m k) eA eB ⁻¹)
       , ap₃ (right m k) eA eB ey
  sound (Block.elimination-equal Γ m k l A A′ B B′ M M′ c c′ d d′ s s′) h =
    let (vΓ , TA , TA′ , eA) = h fzero
        (_ , TB , TB′ , eB) = h (fsuc fzero)
        (_ , TM , TM′ , eM) = h (fsuc (fsuc fzero))
        (_ , Tc , Tc′ , ec) = h (fsuc (fsuc (fsuc fzero)))
        (_ , Td , Td′ , ed) = h (fsuc (fsuc (fsuc (fsuc fzero))))
        (_ , Ts , Ts′ , es) =
          h (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))
        X = object Γ
        env = values Γ
        a = meaning A X env
        b = meaning B X env
        w = sum m k a b
        eS = ap₂ (sum m k) eA eB
        TM″ = typed-along X env (suc l) M′ (Formers.universe l) eS TM′
        TS′ = sum-typed m k A′ B′ X env TA′ TB′
        Ts″ = retype X env (m ⊔ℕ k) s′ (Formers.sum m k A′ B′)
                (Formers.sum m k A B) Ts′ (term-stable TS′) (term-type TS′) eS
        tc′ = transport₂
                (λ x y → type-of (meaning c′ (X ▸ x) (ext x env))
                         ＝ meaning M′ (X ▸ sum m k x y) (ext (sum m k x y) env)
                             [ p ⨾ left m k (x [ p ]) (y [ p ]) (q x) ])
                eA eB
                (left-method m k l A B M c′ X env TA TB TM Tc′ ∙
                  ap (λ N → N [ p ⨾ left m k (a [ p ]) (b [ p ]) (q a) ])
                    eM)
        td′ = transport₂
                (λ x y → type-of (meaning d′ (X ▸ y) (ext y env))
                         ＝ meaning M′ (X ▸ sum m k x y) (ext (sum m k x y) env)
                             [ p ⨾ right m k (x [ p ]) (y [ p ]) (q y) ])
                eA eB
                (right-method m k l A B M d′ X env TA TB TM Td′ ∙
                  ap (λ N → N [ p ⨾ right m k (a [ p ]) (b [ p ]) (q b) ])
                    eM)
        sc′ = transport (λ x → Stable (meaning c′) (X ▸ x) (ext x env)) eA
                (term-stable Tc′)
        sd′ = transport (λ y → Stable (meaning d′) (X ▸ y) (ext y env)) eB
                (term-stable Td′)
        TL = case-typed m k l A B M c d s X env TA TB TM (term-stable Tc)
               (left-method m k l A B M c X env TA TB TM Tc) (term-stable Td)
               (right-method m k l A B M d X env TA TB TM Td) Ts
    in vΓ
       , TL
       , retype X env l (Formers.case m k l A′ B′ M′ c′ d′ s′)
           (Formers.instantiate M s) (Formers.instantiate M′ s′)
           (case-typed m k l A′ B′ M′ c′ d′ s′ X env TA′ TB′ TM″ sc′ tc′ sd′
             td′ Ts″)
           (type-stable TL) (type-code TL)
           (instantiate-equal (m ⊔ℕ k) (Formers.sum m k A B)
               (Formers.sum m k A′ B′) M M′ s s′ X env (term-stable TM)
               (term-stable TM″) Ts Ts″ eS eM es ⁻¹)
       , case-value m k l A B M c d s X env ∙
           (ap₂
               (λ N c″ → case m k l a b N c″ (meaning d (X ▸ b) (ext b env))
                           (meaning s X env))
               eM ec ∙
             (ap₂
                 (case m k l a b (meaning M′ (X ▸ w) (ext w env))
                   (meaning c′ (X ▸ a) (ext a env)))
                 ed es ∙
               (ap₂
                   (λ x y → case m k l x y
                      (meaning M′ (X ▸ sum m k x y) (ext (sum m k x y) env))
                      (meaning c′ (X ▸ x) (ext x env))
                      (meaning d′ (X ▸ y) (ext y env)) (meaning s′ X env))
                   eA eB ∙
                 case-value m k l A′ B′ M′ c′ d′ s′ X env ⁻¹)))
