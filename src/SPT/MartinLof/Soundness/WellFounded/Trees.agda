{-# OPTIONS --safe --without-K --no-projection-like #-}

module SPT.MartinLof.Soundness.WellFounded.Trees where

-- W-types and their suprema in the soundness of the core theory. The
-- values of W A B and of sup are the model's operations at the values of
-- their children, the position type read at the extension by the shape
-- type (`tree-value`, `supremum-value`); they are stable (`tree-stable`,
-- `supremum-stable`) and typed (`tree-typed`, `supremum-typed`). The
-- children's type B a → W A B of sup has the value the model's laws ask
-- for (`children-at`). The value of induction is the model's generic
-- induction term at the values of the motive and the method, with its
-- variable replaced by the tree (`induction-value`).

open import SPT.Base hiding (Lift; _∘_; id; lift; lower; zero)
import SPT.Foundation.Tree.Binding as Binding
import SPT.MartinLof.Formers as Formers
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Model.Empty using (Empty)
open import SPT.MartinLof.Model.Identity using (Identity)
open import SPT.MartinLof.Model.Lift using (Lift)
open import SPT.MartinLof.Model.Natural using (Natural)
open import SPT.MartinLof.Model.Subuniverse using
  (Operations; Subuniverse)
open import SPT.MartinLof.Model.Pi using (Pi)
open import SPT.MartinLof.Model.Russell using (Russell; Code)
open import SPT.MartinLof.Model.Sigma using (Sigma)
open import SPT.MartinLof.Model.Sum using (Sum)
open import SPT.MartinLof.Model.Unit using (Unit)
open import SPT.MartinLof.Model.WellFounded using
  (WellFounded; children-type; hypotheses-type)
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
  (let Typed = Interpretation.Typed R lifting products pairs paths trees
                 nothing one sums numbers operations subuniverses constant)
  (let bound-meaning = Transport.bound-meaning R lifting products pairs paths
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
  (let term-stable = Interpretation.Typed.term-stable)
  (let term-type = Interpretation.Typed.term-type)
  where

  ----------------------------------------------------------------------
  -- Values

  tree-value :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (X : Ob) (env : Vec (Tm X) n)
    → meaning (Formers.tree m k A B) X env
      ＝ tree m k (meaning A X env)
          (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
  tree-value m k A B X env =
    ap (tree m k (meaning A X env))
      (bound-meaning 1 B (X ▸ meaning A X env) (ext (meaning A X env) env))

  supremum-value :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (a f : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → meaning (Formers.supremum m k A B a f) X env
      ＝ supremum m k (meaning A X env)
          (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
          (meaning a X env) (meaning f X env)
  supremum-value m k A B a f X env =
    ap
      (λ b → supremum m k (meaning A X env) b (meaning a X env)
               (meaning f X env))
      (bound-meaning 1 B (X ▸ meaning A X env) (ext (meaning A X env) env))

  -- Induction: the generic term at the motive and the method, at the tree.
  induction-value :
    {n : ℕ} (m k l : ℕ) (A : Raw.Expression C n)
    (B M : Raw.Expression C (suc n))
    (c : Raw.Expression C (suc (suc (suc n)))) (t : Raw.Expression C n)
    (X : Ob) (env : Vec (Tm X) n)
    → let α = meaning A X env
          β = meaning B (X ▸ α) (ext α env)
          w = tree m k α β
          N = meaning M (X ▸ w) (ext w env)
          F = children-type R products m k α β w
          H = hypotheses-type R products m k l α β w N
      in meaning (Formers.tree-induction m k l A B M c t) X env
         ＝ tree-induction m k l α β N
             (meaning c (X ▸ α ▸ F ▸ H) (ext H (ext F (ext α env))))
             [ id ⨾ meaning t X env ]
  induction-value {n} m k l A B M c t X env =
    let α = meaning A X env
        u = meaning t X env
        b̃ = meaning (Binding.bound (Raw.binding C) n 1 B) (X ▸ α) (ext α env)
        w̃ = tree m k α b̃
        F̃ = children-type R products m k α b̃ w̃
        Ñ = meaning (Binding.bound (Raw.binding C) n 1 M) (X ▸ w̃) (ext w̃ env)
        H̃ = hypotheses-type R products m k l α b̃ w̃ Ñ
    in ap (λ c′ → tree-induction m k l α b̃ Ñ c′ [ id ⨾ u ])
           (bound-meaning 3 c (X ▸ α ▸ F̃ ▸ H̃) (ext H̃ (ext F̃ (ext α env)))) ∙
         (ap
             (λ N′ →
                let H′ = hypotheses-type R products m k l α b̃ w̃ N′
                in tree-induction m k l α b̃ N′
                     (meaning c (X ▸ α ▸ F̃ ▸ H′) (ext H′ (ext F̃ (ext α env))))
                     [ id ⨾ u ])
             (bound-meaning 1 M (X ▸ w̃) (ext w̃ env)) ∙
           ap
             (λ b →
                let w′ = tree m k α b
                    F′ = children-type R products m k α b w′
                    N′ = meaning M (X ▸ w′) (ext w′ env)
                    H′ = hypotheses-type R products m k l α b w′ N′
                in tree-induction m k l α b N′
                     (meaning c (X ▸ α ▸ F′ ▸ H′) (ext H′ (ext F′ (ext α env))))
                     [ id ⨾ u ])
             (bound-meaning 1 B (X ▸ α) (ext α env)))

  ----------------------------------------------------------------------
  -- Stability

  tree-stable :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (X : Ob) (env : Vec (Tm X) n)
    → Stable (meaning A) X env → (cA : Code R m (meaning A X env))
    → Stable (meaning B) (X ▸ meaning A X env) (ext (meaning A X env) env)
    → Code R k (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
    → Stable (meaning (Formers.tree m k A B)) X env
  tree-stable m k A B X env sA cA sB cB Y τ =
    let α = meaning A X env
        β = meaning B (X ▸ α) (ext α env)
    in tree-value m k A B Y (env [ τ ]ᵉ) ∙
         (ap (λ x → tree m k x (meaning B (Y ▸ x) (ext x (env [ τ ]ᵉ))))
             (sA Y τ) ∙
           (ap (tree m k (α [ τ ])) (under-stable m B X α env cA sB τ) ∙
             (tree-[] m k α β τ cA cB ⁻¹ ∙
               ap (λ s → s [ τ ]) (tree-value m k A B X env ⁻¹))))

  supremum-stable :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (a f : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Stable (meaning A) X env → (cA : Code R m (meaning A X env))
    → Stable (meaning B) (X ▸ meaning A X env) (ext (meaning A X env) env)
    → Code R k (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
    → Stable (meaning a) X env → type-of (meaning a X env) ＝ meaning A X env
    → Stable (meaning f) X env
    → type-of (meaning f X env)
      ＝ pi k (m ⊔ℕ k)
          (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env)
             [ id ⨾ meaning a X env ])
          (tree m k (meaning A X env)
             (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
             [ p ])
    → Stable (meaning (Formers.supremum m k A B a f)) X env
  supremum-stable m k A B a f X env sA cA sB cB sa ta sf tf Y τ =
    let α = meaning A X env
        β = meaning B (X ▸ α) (ext α env)
        envτ = env [ τ ]ᵉ
    in supremum-value m k A B a f Y envτ ∙
         (ap
             (λ x → supremum m k x (meaning B (Y ▸ x) (ext x envτ))
                      (meaning a Y envτ) (meaning f Y envτ))
             (sA Y τ) ∙
           (ap₃ (supremum m k (α [ τ ]))
               (under-stable m B X α env cA sB τ) (sa Y τ) (sf Y τ) ∙
             (supremum-[] m k α β (meaning a X env) (meaning f X env) τ cA
                   cB ta tf ⁻¹ ∙
               ap (λ s → s [ τ ])
                 (supremum-value m k A B a f X env ⁻¹))))

  ----------------------------------------------------------------------
  -- Typing

  tree-typed :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (X : Ob) (env : Vec (Tm X) n)
    → Typed X env (suc m) A (Formers.universe m)
    → Typed (X ▸ meaning A X env) (ext (meaning A X env) env) (suc k) B
        (Formers.universe k)
    → Typed X env (suc (m ⊔ℕ k)) (Formers.tree m k A B)
        (Formers.universe (m ⊔ℕ k))
  tree-typed m k A B X env TA TB =
    let α = meaning A X env
    in as-type X env (m ⊔ℕ k) (Formers.tree m k A B)
         (tree-stable m k A B X env (term-stable TA) (term-type TA)
           (term-stable TB) (term-type TB))
         (transport (Code R (m ⊔ℕ k)) (tree-value m k A B X env ⁻¹)
           (tree-type m k α (meaning B (X ▸ α) (ext α env)) (term-type TA)
             (term-type TB)))

  -- The type B a → W A B of the children of sup at a.
  children-at :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (a : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Stable (meaning A) X env → Code R m (meaning A X env)
    → Stable (meaning B) (X ▸ meaning A X env) (ext (meaning A X env) env)
    → Code R k (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
    → Stable (meaning a) X env → type-of (meaning a X env) ＝ meaning A X env
    → meaning
        (Formers.pi k (m ⊔ℕ k) (Formers.instantiate B a)
          (Formers.weaken (Formers.tree m k A B)))
        X env
      ＝ pi k (m ⊔ℕ k)
          (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env)
             [ id ⨾ meaning a X env ])
          (tree m k (meaning A X env)
             (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
             [ p ])
  children-at m k A B a X env sA cA sB cB sa ta =
    let α = meaning A X env
        β = meaning B (X ▸ α) (ext α env)
        T = Formers.tree m k A B
        b = meaning (Formers.instantiate B a) X env
    in ap (pi k (m ⊔ℕ k) b)
           (bound-meaning 1 (Formers.weaken T) (X ▸ b) (ext b env) ∙
             (weaken-at T X b env (tree-stable m k A B X env sA cA sB cB) ∙
               ap (λ s → s [ p ]) (tree-value m k A B X env))) ∙
         ap (λ e → pi k (m ⊔ℕ k) e (tree m k α β [ p ]))
           (instantiate-at m B a X α env sB sa ta cA)

  supremum-typed :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (a f : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Typed X env (suc m) A (Formers.universe m)
    → Typed (X ▸ meaning A X env) (ext (meaning A X env) env) (suc k) B
        (Formers.universe k)
    → Typed X env m a A
    → Typed X env (k ⊔ℕ (m ⊔ℕ k)) f
        (Formers.pi k (m ⊔ℕ k) (Formers.instantiate B a)
          (Formers.weaken (Formers.tree m k A B)))
    → Typed X env (m ⊔ℕ k) (Formers.supremum m k A B a f)
        (Formers.tree m k A B)
  supremum-typed m k A B a f X env TA TB Ta Tf =
    let α = meaning A X env
        β = meaning B (X ▸ α) (ext α env)
        sA = term-stable TA
        cA = term-type TA
        sB = term-stable TB
        cB = term-type TB
        tf = term-type Tf ∙
               children-at m k A B a X env sA cA sB cB (term-stable Ta)
                 (term-type Ta)
        T = tree-typed m k A B X env TA TB
    in record
      { type-stable = term-stable T
      ; type-code = term-type T
      ; term-stable =
          supremum-stable m k A B a f X env sA cA sB cB (term-stable Ta)
            (term-type Ta) (term-stable Tf) tf
      ; term-type =
          ap type-of (supremum-value m k A B a f X env) ∙
            (supremum-type m k α β (meaning a X env) (meaning f X env) cA cB
                (term-type Ta) tf ∙
              tree-value m k A B X env ⁻¹)
      }
