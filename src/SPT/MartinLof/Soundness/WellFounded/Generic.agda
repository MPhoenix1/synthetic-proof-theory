{-# OPTIONS --safe --without-K --no-projection-like #-}

module SPT.MartinLof.Soundness.WellFounded.Generic where

-- The generic induction term of a W-structure in the soundness of the
-- core theory. The model's induction is given at the generic tree, a
-- term over the extension by the W-type (Model.WellFounded); the value of
-- induction at a tree replaces its variable by the tree
-- (Trees' `induction-value`).
--
-- The model calculus of the method's context under a substitution τ: a
-- Π with a constant codomain (`arrow-[]`), the children's type taken under
-- the binder of the shape type (`children-[]`), and the hypotheses' type
-- along the substitution lifted past the children (`hypotheses-[]`, with
-- the type of its application `hypotheses-application-type` and its code
-- `hypotheses-code`); replacing the variable of a lifted substitution
-- (`⨾-lift`).
--
-- The premises of induction at a context and an environment, read at the
-- model's method context (`Premises`): the shape, position and motive
-- types are stable types, and the method is stable with the model's
-- method type. From them, the generic term read at τ is the generic term
-- with its variable replaced along τ (`generic-stable`); this is the
-- stability law of the model, read at the values of the premises. The
-- generic term of the weakened premises is the generic term of the
-- premises at the environment past its first entry
-- (`weakened-induction-value`).

open import SPT.Base hiding (Lift; _∘_; id; lift; lower; zero)
open import SPT.Foundation.Vectors.Tabulation using (tabulate-lookup)
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
open import SPT.MartinLof.Model.Russell using
  (Russell; Code; code-[]; under; under-type)
open import SPT.MartinLof.Model.Sigma using (Sigma)
open import SPT.MartinLof.Model.Sum using (Sum)
open import SPT.MartinLof.Model.Unit using (Unit)
open import SPT.MartinLof.Model.WellFounded using
  (WellFounded; children-type; hypotheses-type)
import SPT.MartinLof.Soundness.Environment as Environment
import SPT.MartinLof.Soundness.Instances as Instances
import SPT.MartinLof.Soundness.Interpretation as Interpretation
open import SPT.MartinLof.Soundness.Transport using (ap₃)
import SPT.MartinLof.Soundness.Typing as Typing
import SPT.MartinLof.Soundness.WellFounded.Trees as Trees

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
  (let rename-value = Instances.rename-value R lifting products pairs paths
                        trees nothing one sums numbers operations subuniverses
                          constant)
  (let under-stable = Typing.under-stable R lifting products pairs paths
                        trees nothing one sums numbers operations subuniverses
                          constant)
  (let p-⨾ = Typing.p-⨾ R lifting products pairs paths trees nothing one
               sums numbers operations subuniverses constant)
  (let p-under = Typing.p-under R lifting products pairs paths trees nothing
                   one sums numbers operations subuniverses constant)
  (let ⨾-code = Typing.⨾-code R lifting products pairs paths trees nothing
                  one sums numbers operations subuniverses constant)
  (let lift-stable = Typing.lift-stable R lifting products pairs paths trees
                       nothing one sums numbers operations subuniverses
                         constant)
  (let binder-type = Typing.binder-type R lifting products pairs paths trees
                       nothing one sums numbers operations subuniverses
                         constant)
  (let ext-lift = Typing.ext-lift R lifting products pairs paths trees
                    nothing one sums numbers operations subuniverses constant)
  (let weaken-cons = Typing.weaken-cons R lifting products pairs paths trees
                       nothing one sums numbers operations subuniverses
                         constant)
  (let induction-value = Trees.induction-value R lifting products pairs
                           paths trees nothing one sums numbers
                           operations subuniverses constant)
  where

  ----------------------------------------------------------------------
  -- The method's context under a substitution

  -- A Π whose codomain does not use its variable, substituted.
  arrow-[] :
    {Y Z : Ob} (j i : ℕ) (b u : Tm Z) (σ : Hom Y Z) → Code R j b
    → Code R i u
    → pi j i b (u [ p ]) [ σ ] ＝ pi j i (b [ σ ]) (u [ σ ] [ p ])
  arrow-[] j i b u σ cb cu =
    let e = q-type j (b [ σ ]) (code-[] R j b σ cb) ∙
              [∘] b σ p ⁻¹
    in pi-[] j i b (u [ p ]) σ cb (code-[] R i u p cu) ∙
         ap (pi j i (b [ σ ]))
           (p-⨾ b u (σ ∘ p) (q (b [ σ ])) e ∙ [∘] u σ p)

  -- The children's type, under the binder of the shape type.
  children-[] :
    {X Y : Ob} (m k : ℕ) (a : Tm X) (b : Tm (X ▸ a)) (w : Tm X)
    (τ : Hom Y X) (ta : Code R m a) → Code R k b → Code R (m ⊔ℕ k) w
    → (w′ : Tm Y) → w [ τ ] ＝ w′
    → children-type R products m k a b w [ under R m a τ ta ]
      ＝ children-type R products m k (a [ τ ])
          (b [ τ ∘ p ⨾ q (a [ τ ]) ]) w′
  children-[] m k a b w τ ta tb tw w′ ew =
    let σ = under R m a τ ta
        b′ = b [ τ ∘ p ⨾ q (a [ τ ]) ]
        eb = Environment.⨾-under R m a b τ ta
        cb′ = transport (Code R k) eb (code-[] R k b σ tb)
        e = binder-type k b σ b′ cb′ eb
    in pi-[] k (m ⊔ℕ k) b (w [ p ] [ p ]) σ tb
           (code-[] R (m ⊔ℕ k) (w [ p ]) p (code-[] R (m ⊔ℕ k) w p tw)) ∙
         (ap (λ b″ → pi k (m ⊔ℕ k) b″ (w [ p ] [ p ] [ σ ∘ p ⨾ q b″ ])) eb ∙
           ap (pi k (m ⊔ℕ k) b′)
             (p-⨾ b (w [ p ]) (σ ∘ p) (q b′) e ∙
               ([∘] (w [ p ]) σ p ∙
                 ap (λ s → s [ p ])
                   (p-under m a w τ ta ∙ ap (λ s → s [ p ]) ew))))

  -- The application f y of the hypotheses' type, and its type.
  hypotheses-application-type :
    {X : Ob} (m k : ℕ) (a : Tm X) (b : Tm (X ▸ a)) (w : Tm X)
    → Code R k b → Code R (m ⊔ℕ k) w
    → type-of
        (application k (m ⊔ℕ k) (b [ p ] [ p ]) (w [ p ] [ p ] [ p ] [ p ])
          (q (children-type R products m k a b w) [ p ]) (q (b [ p ])))
      ＝ w [ p ∘ p ∘ p ]
  hypotheses-application-type m k a b w tb tw =
    let F = children-type R products m k a b w
        cbp = code-[] R k b p tb
        cbpp = code-[] R k (b [ p ]) p cbp
        cwp = code-[] R (m ⊔ℕ k) w p tw
        cwpp = code-[] R (m ⊔ℕ k) (w [ p ]) p cwp
        cwppp = code-[] R (m ⊔ℕ k) (w [ p ] [ p ]) p cwpp
        cF = pi-type k (m ⊔ℕ k) b (w [ p ] [ p ]) tb
               (code-[] R (m ⊔ℕ k) (w [ p ]) p cwp)
        tf = type-of-[] (q F) p ∙
               (ap (λ s → s [ p ]) (q-type (k ⊔ℕ (m ⊔ℕ k)) F cF) ∙
                 (ap (λ s → s [ p ]) (arrow-[] k (m ⊔ℕ k) b (w [ p ]) p
                                                 tb cwp) ∙
                   arrow-[] k (m ⊔ℕ k) (b [ p ]) (w [ p ] [ p ]) p cbp cwpp))
    in application-type k (m ⊔ℕ k) (b [ p ] [ p ])
           (w [ p ] [ p ] [ p ] [ p ]) (q F [ p ]) (q (b [ p ])) cbpp
           (code-[] R (m ⊔ℕ k) (w [ p ] [ p ] [ p ]) p cwppp) tf
           (q-type k (b [ p ]) cbp) ∙
         (p-⨾ (b [ p ] [ p ]) (w [ p ] [ p ] [ p ]) id (q (b [ p ]))
             (q-type k (b [ p ]) cbp ∙ [id] (b [ p ] [ p ]) ⁻¹) ∙
           ([id] (w [ p ] [ p ] [ p ]) ∙
             ([∘] w p (p ∘ p) ∙ [∘] (w [ p ]) p p) ⁻¹))

  hypotheses-code :
    {X : Ob} (m k l : ℕ) (a : Tm X) (b : Tm (X ▸ a)) (w : Tm X)
    (M : Tm (X ▸ w)) → Code R k b → Code R (m ⊔ℕ k) w → Code R l M
    → Code R (k ⊔ℕ l) (hypotheses-type R products m k l a b w M)
  hypotheses-code m k l a b w M tb tw tM =
    pi-type k l (b [ p ])
      (M [ p ∘ p ∘ p
         ⨾ application k (m ⊔ℕ k) (b [ p ] [ p ]) (w [ p ] [ p ] [ p ] [ p ])
             (q (children-type R products m k a b w) [ p ]) (q (b [ p ])) ])
      (code-[] R k b p tb)
      (⨾-code l w M (p ∘ p ∘ p)
        (application k (m ⊔ℕ k) (b [ p ] [ p ]) (w [ p ] [ p ] [ p ] [ p ])
          (q (children-type R products m k a b w) [ p ]) (q (b [ p ])))
        (hypotheses-application-type m k a b w tb tw) tM)

  -- Replacing the variable of σ taken under a binder, then the new one.
  ⨾-lift :
    {X Y Z : Ob} (l l′ : ℕ) (a : Tm X) (a′ : Tm Y) (M : Tm (X ▸ a))
    (σ : Hom Y X) (ρ : Hom Z Y) (t : Tm Z) → Code R l a → Code R l′ a′
    → (e₁ : type-of (q a′) ＝ a [ σ ∘ p ]) → (e₂ : type-of t ＝ a′ [ ρ ])
    → (e₃ : type-of t ＝ a [ σ ∘ ρ ])
    → M [ σ ∘ p ⨾ q a′ ] [ ρ ⨾ t ] ＝ M [ σ ∘ ρ ⨾ t ]
  ⨾-lift l l′ a a′ M σ ρ t ta ta′ e₁ e₂ e₃ =
    let E₁ = extend a (σ ∘ p) (q a′) e₁
        E₂ = extend a′ ρ t e₂
        E₃ = extend a (σ ∘ ρ) t e₃
        ep = associative p E₁ E₂ ⁻¹ ∙
               (ap (λ ν → ν ∘ E₂) (p-extend a (σ ∘ p) (q a′) e₁) ∙
                 (associative σ p E₂ ∙
                   (ap (λ ν → σ ∘ ν) (p-extend a′ ρ t e₂) ∙
                     p-extend a (σ ∘ ρ) t e₃ ⁻¹)))
        eq = [∘] (q a) E₁ E₂ ∙
               (ap (λ s → s [ E₂ ]) (q-extend l a (σ ∘ p) (q a′) e₁ ta) ∙
                 (q-extend l′ a′ ρ t e₂ ta′ ∙
                   q-extend l a (σ ∘ ρ) t e₃ ta ⁻¹))
    in ap (λ s → s [ ρ ⨾ t ]) ([⨾] a M (σ ∘ p) (q a′) e₁) ∙
         ([⨾] a′ (M [ E₁ ]) ρ t e₂ ∙
           ([∘] M E₁ E₂ ⁻¹ ∙
             (ap (λ ν → M [ ν ]) (extend-unique a (E₁ ∘ E₂) E₃ ep eq) ∙
               [⨾] a M (σ ∘ ρ) t e₃ ⁻¹)))

  -- The hypotheses' type along the substitution lifted past the children.
  hypotheses-[] :
    {X Y : Ob} (m k l : ℕ) (a : Tm X) (b : Tm (X ▸ a)) (w : Tm X)
    (M : Tm (X ▸ w)) (τ : Hom Y X) (ta : Code R m a) → Code R k b
    → Code R (m ⊔ℕ k) w → Code R l M → (w′ : Tm Y) → w [ τ ] ＝ w′
    → (e : type-of
             (q (children-type R products m k (a [ τ ])
                  (b [ τ ∘ p ⨾ q (a [ τ ]) ]) w′))
           ＝ children-type R products m k a b w [ under R m a τ ta ∘ p ])
    → hypotheses-type R products m k l a b w M
        [ extend (children-type R products m k a b w)
            (under R m a τ ta ∘ p)
            (q (children-type R products m k (a [ τ ])
                 (b [ τ ∘ p ⨾ q (a [ τ ]) ]) w′))
            e ]
      ＝ hypotheses-type R products m k l (a [ τ ])
          (b [ τ ∘ p ⨾ q (a [ τ ]) ]) w′ (M [ τ ∘ p ⨾ q w′ ])
  hypotheses-[] m k l a b w M τ ta tb tw tM w′ ew e =
    let σ = under R m a τ ta
        b′ = b [ τ ∘ p ⨾ q (a [ τ ]) ]
        F = children-type R products m k a b w
        F′ = children-type R products m k (a [ τ ]) b′ w′
        ρ₃ = extend F (σ ∘ p) (q F′) e
        eb = Environment.⨾-under R m a b τ ta
        cb′ = transport (Code R k) eb (code-[] R k b σ tb)
        cw′ = transport (Code R (m ⊔ℕ k)) ew (code-[] R (m ⊔ℕ k) w τ tw)
        cbp = code-[] R k b p tb
        cbpp = code-[] R k (b [ p ]) p cbp
        cwp = code-[] R (m ⊔ℕ k) w p tw
        cwpp = code-[] R (m ⊔ℕ k) (w [ p ]) p cwp
        cwppp = code-[] R (m ⊔ℕ k) (w [ p ] [ p ]) p cwpp
        cF = pi-type k (m ⊔ℕ k) b (w [ p ] [ p ]) tb
               (code-[] R (m ⊔ℕ k) (w [ p ]) p cwp)
        w₄ = w [ p ] [ p ] [ p ] [ p ]
        app = application k (m ⊔ℕ k) (b [ p ] [ p ]) w₄ (q F [ p ])
                (q (b [ p ]))
        app′ = application k (m ⊔ℕ k) (b′ [ p ] [ p ])
                 (w′ [ p ] [ p ] [ p ] [ p ]) (q F′ [ p ]) (q (b′ [ p ]))
        e-app = hypotheses-application-type m k a b w tb tw
        e-app′ = hypotheses-application-type m k (a [ τ ]) b′ w′ cb′ cw′
        K = M [ p ∘ p ∘ p ⨾ app ]
        eb₃ = [∘] b p ρ₃ ⁻¹ ∙
                (ap (λ ν → b [ ν ]) (p-extend F (σ ∘ p) (q F′) e) ∙
                  ([∘] b σ p ∙ ap (λ s → s [ p ]) eb))
        cb′p = code-[] R k b′ p cb′
        e₄ = binder-type k (b [ p ]) ρ₃ (b′ [ p ]) cb′p eb₃
        ν = extend (b [ p ]) (ρ₃ ∘ p) (q (b′ [ p ])) e₄
        pν = p-extend (b [ p ]) (ρ₃ ∘ p) (q (b′ [ p ])) e₄
        pρ₃ = p-extend F (σ ∘ p) (q F′) e
        pσ = p-extend a (τ ∘ p) (q (a [ τ ])) (under-type R m a τ ta)
        e-hom =
          associative p (p ∘ p) ν ∙
            (ap (λ μ → p ∘ μ) (associative p p ν) ∙
              (ap (λ μ → p ∘ (p ∘ μ)) pν ∙
                (ap (λ μ → p ∘ μ) (associative p ρ₃ p ⁻¹) ∙
                  (ap (λ μ → p ∘ (μ ∘ p)) pρ₃ ∙
                    (associative p (σ ∘ p) p ⁻¹ ∙
                      (ap (λ μ → μ ∘ p) (associative p σ p ⁻¹) ∙
                        (ap (λ μ → (μ ∘ p) ∘ p) pσ ∙
                          (ap (λ μ → μ ∘ p) (associative τ p p) ∙
                            (associative τ (p ∘ p) p ∙
                              ap (λ μ → τ ∘ μ) (associative p p p))))))))))
        ebpp = [∘] (b [ p ]) p ν ⁻¹ ∙
                 (ap (λ μ → b [ p ] [ μ ]) pν ∙
                   ([∘] (b [ p ]) ρ₃ p ∙ ap (λ s → s [ p ]) eb₃))
        e₅ = binder-type k (b [ p ] [ p ]) ν (b′ [ p ] [ p ])
               (code-[] R k (b′ [ p ]) p cb′p) ebpp
        ew₃ = [∘] (w [ p ] [ p ]) p ν ⁻¹ ∙
                (ap (λ μ → w [ p ] [ p ] [ μ ]) pν ∙
                  ([∘] (w [ p ] [ p ]) ρ₃ p ∙
                    ap (λ s → s [ p ])
                      ([∘] (w [ p ]) p ρ₃ ⁻¹ ∙
                        (ap (λ μ → w [ p ] [ μ ]) pρ₃ ∙
                          ([∘] (w [ p ]) σ p ∙
                            ap (λ s → s [ p ])
                              (p-under m a w τ ta ∙
                                ap (λ s → s [ p ]) ew))))))
        ecod = p-⨾ (b [ p ] [ p ]) (w [ p ] [ p ] [ p ]) (ν ∘ p)
                   (q (b′ [ p ] [ p ])) e₅ ∙
                 ([∘] (w [ p ] [ p ] [ p ]) ν p ∙
                   ap (λ s → s [ p ]) ew₃)
        eqF = [∘] (q F) p ν ⁻¹ ∙
                (ap (λ μ → q F [ μ ]) pν ∙
                  ([∘] (q F) ρ₃ p ∙
                    ap (λ s → s [ p ])
                      (q-extend (k ⊔ℕ (m ⊔ℕ k)) F (σ ∘ p) (q F′) e cF)))
        eqb = q-extend k (b [ p ]) (ρ₃ ∘ p) (q (b′ [ p ])) e₄ cbp
        tf = type-of-[] (q F) p ∙
               (ap (λ s → s [ p ]) (q-type (k ⊔ℕ (m ⊔ℕ k)) F cF) ∙
                 (ap (λ s → s [ p ])
                     (arrow-[] k (m ⊔ℕ k) b (w [ p ]) p tb cwp) ∙
                   arrow-[] k (m ⊔ℕ k) (b [ p ]) (w [ p ] [ p ]) p cbp cwpp))
        e-app-ν =
          application-[] k (m ⊔ℕ k) (b [ p ] [ p ]) w₄ (q F [ p ])
              (q (b [ p ])) ν cbpp
              (code-[] R (m ⊔ℕ k) (w [ p ] [ p ] [ p ]) p cwppp) tf
              (q-type k (b [ p ]) cbp) ∙
            (ap
                (λ x → application k (m ⊔ℕ k) x (w₄ [ ν ∘ p ⨾ q x ])
                   (q F [ p ] [ ν ]) (q (b [ p ]) [ ν ]))
                ebpp ∙
              ap₃ (application k (m ⊔ℕ k) (b′ [ p ] [ p ])) ecod eqF eqb)
        e₁ = binder-type (m ⊔ℕ k) w τ w′ cw′ ew
        e₃ = e-app′ ∙
               (ap (λ s → s [ p ∘ p ∘ p ]) (ew ⁻¹) ∙
                 [∘] w τ (p ∘ p ∘ p) ⁻¹)
        eK = [⨾] (b [ p ]) K (ρ₃ ∘ p) (q (b′ [ p ])) e₄ ∙
               (Environment.⨾-[] R (m ⊔ℕ k) w M (p ∘ p ∘ p) app ν tw e-app ∙
                 (ap₂ (λ μ s → M [ μ ⨾ s ]) e-hom e-app-ν ∙
                   ⨾-lift (m ⊔ℕ k) (m ⊔ℕ k) w w′ M τ (p ∘ p ∘ p) app′ tw cw′
                       e₁ e-app′ e₃ ⁻¹))
    in pi-[] k l (b [ p ]) K ρ₃ cbp
           (⨾-code l w M (p ∘ p ∘ p) app e-app tM) ∙
         (ap (λ x → pi k l x (K [ ρ₃ ∘ p ⨾ q x ])) eb₃ ∙
           ap (pi k l (b′ [ p ])) eK)

  ----------------------------------------------------------------------
  -- The premises of induction

  -- The values of the premises at X and env: stable types, and the method
  -- stable with the model's method type.
  record Premises
    {n : ℕ} (m k l : ℕ) (A : Raw.Expression C n)
    (B M : Raw.Expression C (suc n))
    (c : Raw.Expression C (suc (suc (suc n)))) (X : Ob)
    (env : Vec (Tm X) n) : Set ℓ where
    field
      shape-stable : Stable (meaning A) X env
      shape-code : Code R m (meaning A X env)
      position-stable :
        let α = meaning A X env
        in Stable (meaning B) (X ▸ α) (ext α env)
      position-code :
        let α = meaning A X env
        in Code R k (meaning B (X ▸ α) (ext α env))
      motive-stable :
        let α = meaning A X env
            w = tree m k α (meaning B (X ▸ α) (ext α env))
        in Stable (meaning M) (X ▸ w) (ext w env)
      motive-code :
        let α = meaning A X env
            w = tree m k α (meaning B (X ▸ α) (ext α env))
        in Code R l (meaning M (X ▸ w) (ext w env))
      method-stable :
        let α = meaning A X env
            β = meaning B (X ▸ α) (ext α env)
            w = tree m k α β
            F = children-type R products m k α β w
            H = hypotheses-type R products m k l α β w
                  (meaning M (X ▸ w) (ext w env))
        in Stable (meaning c) (X ▸ α ▸ F ▸ H) (ext H (ext F (ext α env)))
      method-typed :
        let α = meaning A X env
            β = meaning B (X ▸ α) (ext α env)
            w = tree m k α β
            N = meaning M (X ▸ w) (ext w env)
            F = children-type R products m k α β w
            H = hypotheses-type R products m k l α β w N
        in type-of (meaning c (X ▸ α ▸ F ▸ H) (ext H (ext F (ext α env))))
           ＝ N [ p ∘ p ∘ p
               ⨾ supremum m k (α [ p ] [ p ] [ p ])
                   (β [ (p ∘ p ∘ p) ∘ p ⨾ q (α [ p ] [ p ] [ p ]) ])
                   (q α [ p ] [ p ]) (q F [ p ]) ]

  ----------------------------------------------------------------------
  -- Stability of the generic term

  generic-stable :
    {n : ℕ} (m k l : ℕ) (A : Raw.Expression C n)
    (B M : Raw.Expression C (suc n))
    (c : Raw.Expression C (suc (suc (suc n)))) (X : Ob)
    (env : Vec (Tm X) n) → Premises m k l A B M c X env
    → {Y : Ob} (τ : Hom Y X) (u : Tm Y)
    → let α = meaning A X env
          β = meaning B (X ▸ α) (ext α env)
          w = tree m k α β
          N = meaning M (X ▸ w) (ext w env)
          F = children-type R products m k α β w
          H = hypotheses-type R products m k l α β w N
          envτ = env [ τ ]ᵉ
          α′ = meaning A Y envτ
          β′ = meaning B (Y ▸ α′) (ext α′ envτ)
          w′ = tree m k α′ β′
          N′ = meaning M (Y ▸ w′) (ext w′ envτ)
          F′ = children-type R products m k α′ β′ w′
          H′ = hypotheses-type R products m k l α′ β′ w′ N′
      in type-of u ＝ w [ τ ]
      → tree-induction m k l α′ β′ N′
          (meaning c (Y ▸ α′ ▸ F′ ▸ H′) (ext H′ (ext F′ (ext α′ envτ))))
          [ id ⨾ u ]
        ＝ tree-induction m k l α β N
            (meaning c (X ▸ α ▸ F ▸ H) (ext H (ext F (ext α env))))
            [ τ ⨾ u ]
  generic-stable m k l A B M c X env P {Y} τ u tu =
    let α = meaning A X env
        β = meaning B (X ▸ α) (ext α env)
        w = tree m k α β
        N = meaning M (X ▸ w) (ext w env)
        F = children-type R products m k α β w
        H = hypotheses-type R products m k l α β w N
        c₀ = meaning c (X ▸ α ▸ F ▸ H) (ext H (ext F (ext α env)))
        G = tree-induction m k l α β N c₀
        envτ = env [ τ ]ᵉ
        sA = Premises.shape-stable P
        cA = Premises.shape-code P
        sB = Premises.position-stable P
        cB = Premises.position-code P
        sM = Premises.motive-stable P
        cM = Premises.motive-code P
        sc = Premises.method-stable P
        tc = Premises.method-typed P
        cw = tree-type m k α β cA cB
        σ = under R m α τ cA
        βτ = β [ τ ∘ p ⨾ q (α [ τ ]) ]
        cβτ = ⨾-code k α β (τ ∘ p) (q (α [ τ ])) (under-type R m α τ cA) cB
        wτ = tree m k (α [ τ ]) βτ
        cwτ = tree-type m k (α [ τ ]) βτ (code-[] R m α τ cA) cβτ
        ew = tree-[] m k α β τ cA cB
        e-w = binder-type (m ⊔ℕ k) w τ wτ cwτ ew
        Nτ = N [ τ ∘ p ⨾ q wτ ]
        cNτ = ⨾-code l w N (τ ∘ p) (q wτ) e-w cM
        Fτ = children-type R products m k (α [ τ ]) βτ wτ
        cF = pi-type k (m ⊔ℕ k) β (w [ p ] [ p ]) cB
               (code-[] R (m ⊔ℕ k) (w [ p ]) p (code-[] R (m ⊔ℕ k) w p cw))
        cFτ = pi-type k (m ⊔ℕ k) βτ (wτ [ p ] [ p ]) cβτ
                (code-[] R (m ⊔ℕ k) (wτ [ p ]) p (code-[] R (m ⊔ℕ k) wτ p cwτ))
        eF = binder-type (k ⊔ℕ (m ⊔ℕ k)) F σ Fτ cFτ
               (children-[] m k α β w τ cA cB cw wτ ew)
        ρ₃ = extend F (σ ∘ p) (q Fτ) eF
        Hτ = hypotheses-type R products m k l (α [ τ ]) βτ wτ Nτ
        eH = binder-type (k ⊔ℕ l) H ρ₃ Hτ
               (hypotheses-code m k l (α [ τ ]) βτ wτ Nτ cβτ cwτ cNτ)
               (hypotheses-[] m k l α β w N τ cA cB cw cM wτ ew eF)
        eenv₃ = ext-lift (k ⊔ℕ (m ⊔ℕ k)) F (ext α env) σ Fτ
                  (ext (α [ τ ]) envτ) eF cF
                  (Environment.ext-under R m α env τ cA)
    in ap
           (λ x →
              let b′ = meaning B (Y ▸ x) (ext x envτ)
                  w″ = tree m k x b′
                  N″ = meaning M (Y ▸ w″) (ext w″ envτ)
                  F″ = children-type R products m k x b′ w″
                  H″ = hypotheses-type R products m k l x b′ w″ N″
              in tree-induction m k l x b′ N″
                   (meaning c (Y ▸ x ▸ F″ ▸ H″)
                     (ext H″ (ext F″ (ext x envτ))))
                   [ id ⨾ u ])
           (sA Y τ) ∙
         (ap
             (λ b′ →
                let w″ = tree m k (α [ τ ]) b′
                    N″ = meaning M (Y ▸ w″) (ext w″ envτ)
                    F″ = children-type R products m k (α [ τ ]) b′ w″
                    H″ = hypotheses-type R products m k l (α [ τ ]) b′ w″ N″
                in tree-induction m k l (α [ τ ]) b′ N″
                     (meaning c (Y ▸ α [ τ ] ▸ F″ ▸ H″)
                       (ext H″ (ext F″ (ext (α [ τ ]) envτ))))
                     [ id ⨾ u ])
             (under-stable m B X α env cA sB τ) ∙
           (ap
               (λ N″ →
                  let H″ = hypotheses-type R products m k l (α [ τ ]) βτ wτ N″
                  in tree-induction m k l (α [ τ ]) βτ N″
                       (meaning c (Y ▸ α [ τ ] ▸ Fτ ▸ H″)
                         (ext H″ (ext Fτ (ext (α [ τ ]) envτ))))
                       [ id ⨾ u ])
               (lift-stable (meaning M) (m ⊔ℕ k) X w env cw sM τ wτ envτ e-w
                 refl) ∙
             (ap
                 (λ c′ → tree-induction m k l (α [ τ ]) βτ Nτ c′ [ id ⨾ u ])
                 (lift-stable (meaning c) (k ⊔ℕ l) (X ▸ α ▸ F) H
                   (ext F (ext α env))
                   (hypotheses-code m k l α β w N cB cw cM)
                   sc ρ₃ Hτ (ext Fτ (ext (α [ τ ]) envτ)) eH eenv₃) ∙
               (ap (λ s → s [ id ⨾ u ])
                   (tree-induction-[] m k l α β N c₀ τ cA cB cM tc eF ⁻¹) ∙
                 (⨾-lift (m ⊔ℕ k) (m ⊔ℕ k) w wτ G τ id u cw cwτ e-w
                     (tu ∙ (ew ∙ [id] wτ ⁻¹))
                     (tu ∙ ap (λ μ → w [ μ ]) (id-right τ ⁻¹)) ∙
                   ap (λ μ → G [ μ ⨾ u ]) (id-right τ))))))

  ----------------------------------------------------------------------
  -- Induction at weakened premises

  -- B weakened past one variable under its binder, read at an extension.
  weaken-under :
    {n : ℕ} (B : Raw.Expression C (suc n)) (Z : Ob) (v : Tm Z)
    (E : Vec (Tm Z) n) (x : Tm Z)
    → meaning (Formers.weaken-past n 1 1 B) (Z ▸ x) (ext x (v ∷ E))
      ＝ meaning B (Z ▸ x) (ext x E)
  weaken-under {n} B Z v E x =
    rename-value (Binding.lift (Raw.binding C) 1 (λ (y : Fin n) → 1 ↑ʳ y))
        B (Z ▸ x) (ext x (v ∷ E)) ∙
      ap (λ es → meaning B (Z ▸ x) (q x ∷ es)) (tabulate-lookup (E [ p ]ᵉ))

  weakened-induction-value :
    {n : ℕ} (m k l : ℕ) (A : Raw.Expression C n)
    (B M : Raw.Expression C (suc n))
    (c : Raw.Expression C (suc (suc (suc n))))
    (t : Raw.Expression C (suc n)) (Z : Ob) (v : Tm Z) (E : Vec (Tm Z) n)
    → let α = meaning A Z E
          β = meaning B (Z ▸ α) (ext α E)
          w = tree m k α β
          N = meaning M (Z ▸ w) (ext w E)
          F = children-type R products m k α β w
          H = hypotheses-type R products m k l α β w N
      in meaning
           (Formers.tree-induction m k l (Formers.weaken A)
             (Formers.weaken-past n 1 1 B) (Formers.weaken-past n 1 1 M)
             (Formers.weaken-past n 3 1 c) t)
           Z (v ∷ E)
         ＝ tree-induction m k l α β N
             (meaning c (Z ▸ α ▸ F ▸ H) (ext H (ext F (ext α E))))
             [ id ⨾ meaning t Z (v ∷ E) ]
  weakened-induction-value {n} m k l A B M c t Z v E =
    let α = meaning A Z E
        β = meaning B (Z ▸ α) (ext α E)
        w = tree m k α β
        N = meaning M (Z ▸ w) (ext w E)
        F = children-type R products m k α β w
        H = hypotheses-type R products m k l α β w N
        B₁ = Formers.weaken-past n 1 1 B
        M₁ = Formers.weaken-past n 1 1 M
        c₁ = Formers.weaken-past n 3 1 c
        E₁ = v ∷ E
        u = meaning t Z E₁
    in induction-value m k l (Formers.weaken A) B₁ M₁ c₁ t Z E₁ ∙
         (ap
             (λ x →
                let b′ = meaning B₁ (Z ▸ x) (ext x E₁)
                    w″ = tree m k x b′
                    N″ = meaning M₁ (Z ▸ w″) (ext w″ E₁)
                    F″ = children-type R products m k x b′ w″
                    H″ = hypotheses-type R products m k l x b′ w″ N″
                in tree-induction m k l x b′ N″
                     (meaning c₁ (Z ▸ x ▸ F″ ▸ H″)
                       (ext H″ (ext F″ (ext x E₁))))
                     [ id ⨾ u ])
             (weaken-cons A Z v E) ∙
           (ap
               (λ b′ →
                  let w″ = tree m k α b′
                      N″ = meaning M₁ (Z ▸ w″) (ext w″ E₁)
                      F″ = children-type R products m k α b′ w″
                      H″ = hypotheses-type R products m k l α b′ w″ N″
                  in tree-induction m k l α b′ N″
                       (meaning c₁ (Z ▸ α ▸ F″ ▸ H″)
                         (ext H″ (ext F″ (ext α E₁))))
                       [ id ⨾ u ])
               (weaken-under B Z v E α) ∙
             (ap
                 (λ N″ →
                    let H″ = hypotheses-type R products m k l α β w N″
                    in tree-induction m k l α β N″
                         (meaning c₁ (Z ▸ α ▸ F ▸ H″)
                           (ext H″ (ext F (ext α E₁))))
                         [ id ⨾ u ])
                 (weaken-under M Z v E w) ∙
               ap (λ c′ → tree-induction m k l α β N c′ [ id ⨾ u ])
                 (rename-value
                     (Binding.lift (Raw.binding C) 3
                       (λ (y : Fin n) → 1 ↑ʳ y))
                     c (Z ▸ α ▸ F ▸ H) (ext H (ext F (ext α E₁))) ∙
                   ap
                     (λ es → meaning c (Z ▸ α ▸ F ▸ H)
                               (q H ∷ q F [ p ] ∷ q α [ p ] [ p ] ∷ es))
                     (tabulate-lookup (E [ p ]ᵉ [ p ]ᵉ [ p ]ᵉ))))))
