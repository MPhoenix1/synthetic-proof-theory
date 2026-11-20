{-# OPTIONS --safe --without-K --no-projection-like #-}

module SPT.MartinLof.Soundness.WellFounded.Induction where

-- W-induction in the soundness of the core theory. The method premise is
-- typed at the method context of the syntax, whose types have the values
-- of the model's method context (`children-model`, `hypotheses-model`), so
-- it is typed there (`method-model`), with the model's method type
-- (`method-type-model`); with the shape, position and motive premises it
-- gives the premises of the model's induction (`premises`), and equal
-- premises give them for equal data (`premises-equal`). Induction is then
-- stable (`induction-stable`, from Generic's `generic-stable`) and has the
-- motive's instance at the tree as type (`induction-typed`).

open import SPT.Base hiding (Lift; _∘_; id; lift; lower; zero)
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.MartinLof.Formers as Formers
import SPT.MartinLof.Raw as Raw
import SPT.MartinLof.Rules.WellFounded as Block
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
open import SPT.MartinLof.Model.WellFounded using
  (WellFounded; children-type; hypotheses-type)
import SPT.Foundation.Tree as Tree
import SPT.MartinLof.Soundness.Environment as Environment
import SPT.MartinLof.Soundness.Instances as Instances
import SPT.MartinLof.Soundness.Interpretation as Interpretation
import SPT.MartinLof.Soundness.Typing as Typing
import SPT.MartinLof.Soundness.WellFounded.Generic as Generic
import SPT.MartinLof.Soundness.WellFounded.Method as Method
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
  (let Typed = Interpretation.Typed R lifting products pairs paths trees
                 nothing one sums numbers operations subuniverses constant)
  (let instantiate-at = Instances.instantiate-at R lifting products pairs
                          paths trees nothing one sums numbers
                          operations subuniverses constant)
  (let typed-along = Typing.typed-along R lifting products pairs paths trees
                       nothing one sums numbers operations subuniverses
                         constant)
  (let ⨾-type = Typing.⨾-type R lifting products pairs paths trees nothing
                  one sums numbers operations subuniverses constant)
  (let stable-extend = Typing.stable-extend R lifting products pairs paths
                         trees nothing one sums numbers operations subuniverses
                           constant)
  (let binder-type = Typing.binder-type R lifting products pairs paths trees
                       nothing one sums numbers operations subuniverses
                         constant)
  (let ⨾-code = Typing.⨾-code R lifting products pairs paths trees nothing
                  one sums numbers operations subuniverses constant)
  (let lift-stable = Typing.lift-stable R lifting products pairs paths trees
                       nothing one sums numbers operations subuniverses
                         constant)
  (let stable-lift = Typing.stable-lift R lifting products pairs paths trees
                       nothing one sums numbers operations subuniverses
                         constant)
  (let instance-as-type = Typing.instance-as-type R lifting products pairs
                            paths trees nothing one sums numbers
                            operations subuniverses constant)
  (let tree-value = Trees.tree-value R lifting products pairs paths trees
                      nothing one sums numbers operations subuniverses constant)
  (let tree-stable = Trees.tree-stable R lifting products pairs paths trees
                       nothing one sums numbers operations subuniverses
                         constant)
  (let induction-value = Trees.induction-value R lifting products pairs
                           paths trees nothing one sums numbers
                           operations subuniverses constant)
  (let children-value = Method.children-value R lifting products pairs paths
                          trees nothing one sums numbers operations
                            subuniverses constant)
  (let hypotheses-value = Method.hypotheses-value R lifting products pairs
                            paths trees nothing one sums numbers
                            operations subuniverses constant)
  (let method-type-value = Method.method-type-value R lifting products pairs
                             paths trees nothing one sums numbers
                             operations subuniverses constant)
  (let arrow-[] = Generic.arrow-[] R lifting products pairs paths trees
                    nothing one sums numbers operations subuniverses constant)
  (let hypotheses-application-type = Generic.hypotheses-application-type R
                                       lifting products pairs paths trees
                                       nothing one sums numbers
                                       operations subuniverses constant)
  (let Premises = Generic.Premises R lifting products pairs paths trees
                    nothing one sums numbers operations subuniverses constant)
  (let generic-stable = Generic.generic-stable R lifting products pairs
                          paths trees nothing one sums numbers
                          operations subuniverses constant)
  (let type-code = Interpretation.Typed.type-code)
  (let term-stable = Interpretation.Typed.term-stable)
  (let term-type = Interpretation.Typed.term-type)
  where

  ----------------------------------------------------------------------
  -- Reading two and three binders deeper

  stable-p₂ :
    {k : ℕ} (μ : (Y : Ob) → Vec (Tm Y) k → Tm Y) (X : Ob)
    (env : Vec (Tm X) k) → Stable μ X env → (a : Tm X) (b : Tm (X ▸ a))
    → μ (X ▸ a ▸ b) (env [ p ]ᵉ [ p ]ᵉ) ＝ μ X env [ p ] [ p ]
  stable-p₂ μ X env s a b =
    ap (μ (X ▸ a ▸ b)) (Environment.[]ᵉ-∘ R env p p ⁻¹) ∙
      (s (X ▸ a ▸ b) (p ∘ p) ∙ [∘] (μ X env) p p)

  -- The environment, three binders deeper, as one substitution.
  env-p₃ :
    {k : ℕ} (X : Ob) (env : Vec (Tm X) k) (a : Tm X) (b : Tm (X ▸ a))
    (d : Tm (X ▸ a ▸ b))
    → _＝_ {A = Vec (Tm (X ▸ a ▸ b ▸ d)) k} (env [ p ∘ p ∘ p ]ᵉ)
        (env [ p ]ᵉ [ p ]ᵉ [ p ]ᵉ)
  env-p₃ X env a b d =
    Environment.[]ᵉ-∘ R env p (p ∘ p) ∙
      Environment.[]ᵉ-∘ R (env [ p ]ᵉ) p p

  stable-p₃ :
    {k : ℕ} (μ : (Y : Ob) → Vec (Tm Y) k → Tm Y) (X : Ob)
    (env : Vec (Tm X) k) → Stable μ X env → (a : Tm X) (b : Tm (X ▸ a))
    (d : Tm (X ▸ a ▸ b))
    → μ (X ▸ a ▸ b ▸ d) (env [ p ]ᵉ [ p ]ᵉ [ p ]ᵉ) ＝ μ X env [ p ] [ p ] [ p ]
  stable-p₃ μ X env s a b d =
    ap (μ (X ▸ a ▸ b ▸ d)) (env-p₃ X env a b d ⁻¹) ∙
      (s (X ▸ a ▸ b ▸ d) (p ∘ p ∘ p) ∙
        ([∘] (μ X env) p (p ∘ p) ∙ [∘] (μ X env [ p ]) p p))

  ----------------------------------------------------------------------
  -- The method context of the syntax, at the model's

  -- The children's type, at the extension by the shape type.
  children-model :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (X : Ob) (env : Vec (Tm X) n)
    → Stable (meaning A) X env → Code R m (meaning A X env)
    → Stable (meaning B) (X ▸ meaning A X env) (ext (meaning A X env) env)
    → Code R k (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
    → let α = meaning A X env
          β = meaning B (X ▸ α) (ext α env)
      in meaning
           (Formers.pi k (m ⊔ℕ k) B
             (Formers.weaken (Formers.weaken (Formers.tree m k A B))))
           (X ▸ α) (ext α env)
         ＝ children-type R products m k α β (tree m k α β)
  children-model m k A B X env sA cA sB cB =
    let α = meaning A X env
        β = meaning B (X ▸ α) (ext α env)
        T = Formers.tree m k A B
    in children-value m k A B (X ▸ α) (q α) (env [ p ]ᵉ) ∙
         ap (pi k (m ⊔ℕ k) β)
           (stable-p₂ (meaning T) X env
               (tree-stable m k A B X env sA cA sB cB) α β ∙
             ap (λ s → s [ p ] [ p ]) (tree-value m k A B X env))

  -- The hypotheses' type, at the extension by the children's type.
  hypotheses-model :
    {n : ℕ} (m k l : ℕ) (A : Raw.Expression C n)
    (B M : Raw.Expression C (suc n)) (X : Ob) (env : Vec (Tm X) n)
    → Stable (meaning A) X env → Code R m (meaning A X env)
    → Stable (meaning B) (X ▸ meaning A X env) (ext (meaning A X env) env)
    → Code R k (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
    → let α = meaning A X env
          β = meaning B (X ▸ α) (ext α env)
          w = tree m k α β
      in Stable (meaning M) (X ▸ w) (ext w env)
         → let F = children-type R products m k α β w
           in meaning
                (Formers.pi k l (Formers.weaken B)
                  (Formers.instantiate-past 3 M
                    (Formers.application k (m ⊔ℕ k)
                      (Formers.weaken (Formers.weaken B))
                      (Formers.weaken
                        (Formers.weaken
                          (Formers.weaken
                            (Formers.weaken (Formers.tree m k A B)))))
                      (Tree.hole (fsuc fzero)) (Tree.hole fzero))))
                (X ▸ α ▸ F) (ext F (ext α env))
              ＝ hypotheses-type R products m k l α β w
                  (meaning M (X ▸ w) (ext w env))
  hypotheses-model m k l A B M X env sA cA sB cB sM =
    let α = meaning A X env
        β = meaning B (X ▸ α) (ext α env)
        w = tree m k α β
        T = Formers.tree m k A B
        F = children-type R products m k α β w
        Z = X ▸ α ▸ F
        cw = tree-type m k α β cA cB
        cwp = code-[] R (m ⊔ℕ k) w p cw
        cwpp = code-[] R (m ⊔ℕ k) (w [ p ]) p cwp
        cF = pi-type k (m ⊔ℕ k) β (w [ p ] [ p ]) cB
               (code-[] R (m ⊔ℕ k) (w [ p ]) p cwp)
        sT = tree-stable m k A B X env sA cA sB cB
        b₁ = meaning B Z (q α [ p ] ∷ env [ p ]ᵉ [ p ]ᵉ)
        eb₁ = sB Z p
        v₂ = meaning T Z (env [ p ]ᵉ [ p ]ᵉ)
        ev₂ = stable-p₂ (meaning T) X env sT α F ∙
                ap (λ s → s [ p ] [ p ]) (tree-value m k A B X env)
        sT₂ = Environment.stable-[] R (meaning T) (X ▸ α) (env [ p ]ᵉ)
                (Environment.stable-[] R (meaning T) X env sT p) p
        tf₁ = q-type (k ⊔ℕ (m ⊔ℕ k)) F cF ∙
                (arrow-[] k (m ⊔ℕ k) β (w [ p ]) p cB cwp ∙
                  ap₂ (λ u v → pi k (m ⊔ℕ k) u (v [ p ])) eb₁ ev₂ ⁻¹)
        app = application k (m ⊔ℕ k) (β [ p ] [ p ])
                (w [ p ] [ p ] [ p ] [ p ]) (q F [ p ]) (q (β [ p ]))
    in hypotheses-value m k l A B M Z (q F) (q α [ p ]) (env [ p ]ᵉ [ p ]ᵉ)
           (Environment.stable-[] R (meaning B) (X ▸ α) (ext α env) sB p)
           (transport (Code R k) (eb₁ ⁻¹) (code-[] R k β p cB)) sT₂
           (transport (Code R (m ⊔ℕ k)) (ev₂ ⁻¹) cwpp) tf₁ ∙
         (ap₂
             (λ u v → pi k l u
                (meaning M (Z ▸ u)
                  (application k (m ⊔ℕ k) (u [ p ]) (v [ p ] [ p ]) (q F [ p ])
                     (q u)
                   ∷ env [ p ]ᵉ [ p ]ᵉ [ p ]ᵉ)))
             eb₁ ev₂ ∙
           ap (pi k l (β [ p ]))
             (ap (λ es → meaning M (Z ▸ β [ p ]) (app ∷ es))
                 (env-p₃ X env α F (β [ p ]) ⁻¹) ∙
               stable-extend (meaning M) (m ⊔ℕ k) X w env cw sM (p ∘ p ∘ p) app
                 (hypotheses-application-type m k α β w cB cw)))

  -- A term typed at the method context of the syntax, at the model's.
  method-model :
    {n : ℕ} (m k l : ℕ) (A : Raw.Expression C n)
    (B M : Raw.Expression C (suc n))
    (c : Raw.Expression C (suc (suc (suc n)))) (X : Ob)
    (env : Vec (Tm X) n)
    → Stable (meaning A) X env → Code R m (meaning A X env)
    → Stable (meaning B) (X ▸ meaning A X env) (ext (meaning A X env) env)
    → Code R k (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
    → let α = meaning A X env
          β = meaning B (X ▸ α) (ext α env)
          w = tree m k α β
          F = children-type R products m k α β w
          H = hypotheses-type R products m k l α β w
                (meaning M (X ▸ w) (ext w env))
          F′ = Formers.pi k (m ⊔ℕ k) B
                 (Formers.weaken (Formers.weaken (Formers.tree m k A B)))
          H′ = Formers.pi k l (Formers.weaken B)
                 (Formers.instantiate-past 3 M
                   (Formers.application k (m ⊔ℕ k)
                     (Formers.weaken (Formers.weaken B))
                     (Formers.weaken
                       (Formers.weaken
                         (Formers.weaken
                           (Formers.weaken (Formers.tree m k A B)))))
                     (Tree.hole (fsuc fzero)) (Tree.hole fzero)))
          Fs = meaning F′ (X ▸ α) (ext α env)
          Hs = meaning H′ (X ▸ α ▸ Fs) (ext Fs (ext α env))
      in Stable (meaning M) (X ▸ w) (ext w env)
         → Typed (X ▸ α ▸ Fs ▸ Hs) (ext Hs (ext Fs (ext α env))) l c
             (Block.method-type m k A B M)
         → Typed (X ▸ α ▸ F ▸ H) (ext H (ext F (ext α env))) l c
             (Block.method-type m k A B M)
  method-model m k l A B M c X env sA cA sB cB sM Tc =
    let α = meaning A X env
        F′ = Formers.pi k (m ⊔ℕ k) B
               (Formers.weaken (Formers.weaken (Formers.tree m k A B)))
        H′ = Formers.pi k l (Formers.weaken B)
               (Formers.instantiate-past 3 M
                 (Formers.application k (m ⊔ℕ k)
                   (Formers.weaken (Formers.weaken B))
                   (Formers.weaken
                     (Formers.weaken
                       (Formers.weaken
                         (Formers.weaken (Formers.tree m k A B)))))
                   (Tree.hole (fsuc fzero)) (Tree.hole fzero)))
        β = meaning B (X ▸ α) (ext α env)
        w = tree m k α β
        F = children-type R products m k α β w
    in typed-along (X ▸ α ▸ F) (ext F (ext α env)) l c
         (Block.method-type m k A B M)
         (hypotheses-model m k l A B M X env sA cA sB cB sM)
         (transport
           (λ G → Typed
              (X ▸ α ▸ G ▸ meaning H′ (X ▸ α ▸ G) (ext G (ext α env)))
              (ext (meaning H′ (X ▸ α ▸ G) (ext G (ext α env)))
                (ext G (ext α env)))
              l c (Block.method-type m k A B M))
           (children-model m k A B X env sA cA sB cB) Tc)

  -- The type of the children's variable, past one more binder K.
  children-variable-type :
    {X : Ob} (m k : ℕ) (a : Tm X) (b : Tm (X ▸ a)) (w : Tm X)
    → Code R k b → Code R (m ⊔ℕ k) w
    → (K : Tm (X ▸ a ▸ children-type R products m k a b w))
    → _＝_ {A = Tm (X ▸ a ▸ children-type R products m k a b w ▸ K)}
        (type-of (q (children-type R products m k a b w) [ p ]))
        (pi k (m ⊔ℕ k) (b [ p ] [ p ]) (w [ p ] [ p ] [ p ] [ p ]))
  children-variable-type m k a b w cb cw K =
    let F = children-type R products m k a b w
        cwp = code-[] R (m ⊔ℕ k) w p cw
        cF = pi-type k (m ⊔ℕ k) b (w [ p ] [ p ]) cb
               (code-[] R (m ⊔ℕ k) (w [ p ]) p cwp)
    in type-of-[] (q F) p ∙
         (ap (λ s → s [ p ]) (q-type (k ⊔ℕ (m ⊔ℕ k)) F cF) ∙
           (ap (λ s → s [ p ]) (arrow-[] k (m ⊔ℕ k) b (w [ p ]) p cb cwp) ∙
             arrow-[] k (m ⊔ℕ k) (b [ p ]) (w [ p ] [ p ]) p
               (code-[] R k b p cb) (code-[] R (m ⊔ℕ k) (w [ p ]) p cwp)))

  -- The method type of the syntax, at a context extending the extension
  -- by the shape type by a type G of children and one more type K.
  method-type-at :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B M : Raw.Expression C (suc n)) (X : Ob) (env : Vec (Tm X) n)
    → Stable (meaning A) X env → Code R m (meaning A X env)
    → Stable (meaning B) (X ▸ meaning A X env) (ext (meaning A X env) env)
    → Code R k (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
    → let α = meaning A X env
          β = meaning B (X ▸ α) (ext α env)
          w = tree m k α β
          N = meaning M (X ▸ w) (ext w env)
      in Stable (meaning M) (X ▸ w) (ext w env)
         → (G : Tm (X ▸ α)) (K : Tm (X ▸ α ▸ G))
         → _＝_ {A = Tm (X ▸ α ▸ G ▸ K)} (type-of (q G [ p ]))
             (pi k (m ⊔ℕ k) (β [ p ] [ p ]) (w [ p ] [ p ] [ p ] [ p ]))
         → meaning (Block.method-type m k A B M) (X ▸ α ▸ G ▸ K)
             (ext K (ext G (ext α env)))
           ＝ N [ p ∘ p ∘ p
               ⨾ supremum m k (α [ p ] [ p ] [ p ])
                   (β [ (p ∘ p ∘ p) ∘ p ⨾ q (α [ p ] [ p ] [ p ]) ])
                   (q α [ p ] [ p ]) (q G [ p ]) ]
  method-type-at m k A B M X env sA cA sB cB sM F H tF =
    let α = meaning A X env
        β = meaning B (X ▸ α) (ext α env)
        w = tree m k α β
        N = meaning M (X ▸ w) (ext w env)
        Z = X ▸ α ▸ F ▸ H
        T = Formers.tree m k A B
        E = env [ p ]ᵉ [ p ]ᵉ [ p ]ᵉ
        x = q α [ p ] [ p ]
        f = q F [ p ]
        αE = meaning A Z E
        βE = meaning B (Z ▸ αE) (ext αE E)
        cw = tree-type m k α β cA cB
        cαp = code-[] R m α p cA
        cαpp = code-[] R m (α [ p ]) p cαp
        cαppp = code-[] R m (α [ p ] [ p ]) p cαpp
        eα₃ = [∘] α p (p ∘ p) ∙ [∘] (α [ p ]) p p
        eαE = stable-p₃ (meaning A) X env sA α F H
        cαE = transport (Code R m) (eαE ⁻¹) cαppp
        eαE′ = eα₃ ∙ eαE ⁻¹
        eρ = binder-type m α (p ∘ p ∘ p) αE cαE eαE′
        sBE = stable-lift (meaning B) m X α env cA sB (p ∘ p ∘ p) αE E eρ
                (env-p₃ X env α F H)
        eβE = lift-stable (meaning B) m X α env cA sB (p ∘ p ∘ p) αE E eρ
                (env-p₃ X env α F H)
        cβE = transport (Code R k) (eβE ⁻¹)
                (⨾-code k α β ((p ∘ p ∘ p) ∘ p) (q αE) eρ cB)
        tx = type-of-[] (q α [ p ]) p ∙
               (ap (λ s → s [ p ]) (type-of-[] (q α) p) ∙
                 (ap (λ s → s [ p ] [ p ]) (q-type m α cA) ∙
                   eαE ⁻¹))
        eβx = stable-extend (meaning B) m Z αE E cαE sBE id x
                    (tx ∙ [id] αE ⁻¹) ⁻¹ ∙
                (ap (λ es → meaning B Z (x ∷ es)) (Environment.[]ᵉ-id R E) ∙
                  stable-p₂ (meaning B) (X ▸ α) (ext α env) sB F H)
        etE = tree-value m k A B Z E ⁻¹ ∙
                (stable-p₃ (meaning T) X env
                         (tree-stable m k A B X env sA cA sB cB) α F H ∙
                  ap (λ s → s [ p ] [ p ] [ p ])
                    (tree-value m k A B X env))
        tf = tF ∙
               ap₂ (λ u v → pi k (m ⊔ℕ k) u (v [ p ])) eβx etE ⁻¹
        S = supremum m k αE βE x f
        eα₃′ = [∘] w p (p ∘ p) ∙ [∘] (w [ p ]) p p
        eS = supremum-type m k αE βE x f cαE cβE tx tf ∙
               (etE ∙ eα₃′ ⁻¹)
        e₇ = binder-type m α (p ∘ p ∘ p) (α [ p ] [ p ] [ p ]) cαppp eα₃
        eβ₃ = ap
                  (λ es → meaning B (Z ▸ α [ p ] [ p ] [ p ])
                            (q (α [ p ] [ p ] [ p ]) ∷ es))
                  ((Environment.[]ᵉ-∘ R env (p ∘ p ∘ p) p ∙
                      ap (λ es → es [ p ]ᵉ) (env-p₃ X env α F H)) ⁻¹) ∙
                stable-extend (meaning B) m X α env cA sB ((p ∘ p ∘ p) ∘ p)
                  (q (α [ p ] [ p ] [ p ])) e₇
    in method-type-value m k A B M Z (q H) f x E
           (Environment.stable-[] R (meaning A) (X ▸ α ▸ F) (env [ p ]ᵉ [ p ]ᵉ)
             (Environment.stable-[] R (meaning A) (X ▸ α) (env [ p ]ᵉ)
               (Environment.stable-[] R (meaning A) X env sA p) p)
             p)
           cαE sBE cβE tx tf ∙
         (ap (λ es → meaning M Z (S ∷ es)) (env-p₃ X env α F H ⁻¹) ∙
           (stable-extend (meaning M) (m ⊔ℕ k) X w env cw sM (p ∘ p ∘ p) S eS ∙
             (ap
                 (λ u → N [ p ∘ p ∘ p
                          ⨾ supremum m k u (meaning B (Z ▸ u) (ext u E)) x f ])
                 eαE ∙
               ap
                 (λ v → N [ p ∘ p ∘ p
                          ⨾ supremum m k (α [ p ] [ p ] [ p ]) v x f ])
                 eβ₃)))

  -- The method type of the syntax, at the model's method context.
  method-type-model :
    {n : ℕ} (m k l : ℕ) (A : Raw.Expression C n)
    (B M : Raw.Expression C (suc n)) (X : Ob) (env : Vec (Tm X) n)
    → Stable (meaning A) X env → Code R m (meaning A X env)
    → Stable (meaning B) (X ▸ meaning A X env) (ext (meaning A X env) env)
    → Code R k (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
    → let α = meaning A X env
          β = meaning B (X ▸ α) (ext α env)
          w = tree m k α β
          N = meaning M (X ▸ w) (ext w env)
          F = children-type R products m k α β w
          H = hypotheses-type R products m k l α β w N
          Z = X ▸ α ▸ F ▸ H
      in Stable (meaning M) (X ▸ w) (ext w env)
         → meaning (Block.method-type m k A B M) Z
             (ext H (ext F (ext α env)))
           ＝ N [ p ∘ p ∘ p
               ⨾ supremum m k (α [ p ] [ p ] [ p ])
                   (β [ (p ∘ p ∘ p) ∘ p ⨾ q (α [ p ] [ p ] [ p ]) ])
                   (q α [ p ] [ p ]) (q F [ p ]) ]
  method-type-model m k l A B M X env sA cA sB cB sM =
    let α = meaning A X env
        β = meaning B (X ▸ α) (ext α env)
        w = tree m k α β
        N = meaning M (X ▸ w) (ext w env)
        F = children-type R products m k α β w
        H = hypotheses-type R products m k l α β w N
    in method-type-at m k A B M X env sA cA sB cB sM F H
         (children-variable-type m k α β w cB (tree-type m k α β cA cB) H)

  ----------------------------------------------------------------------
  -- The premises of the model's induction

  premises :
    {n : ℕ} (m k l : ℕ) (A : Raw.Expression C n)
    (B M : Raw.Expression C (suc n))
    (c : Raw.Expression C (suc (suc (suc n)))) (X : Ob)
    (env : Vec (Tm X) n)
    → Typed X env (suc m) A (Formers.universe m)
    → Typed (X ▸ meaning A X env) (ext (meaning A X env) env) (suc k) B
        (Formers.universe k)
    → Typed (X ▸ meaning (Formers.tree m k A B) X env)
        (ext (meaning (Formers.tree m k A B) X env) env) (suc l) M
        (Formers.universe l)
    → let α = meaning A X env
          F′ = Formers.pi k (m ⊔ℕ k) B
                 (Formers.weaken (Formers.weaken (Formers.tree m k A B)))
          H′ = Formers.pi k l (Formers.weaken B)
                 (Formers.instantiate-past 3 M
                   (Formers.application k (m ⊔ℕ k)
                     (Formers.weaken (Formers.weaken B))
                     (Formers.weaken
                       (Formers.weaken
                         (Formers.weaken
                           (Formers.weaken (Formers.tree m k A B)))))
                     (Tree.hole (fsuc fzero)) (Tree.hole fzero)))
          Fs = meaning F′ (X ▸ α) (ext α env)
          Hs = meaning H′ (X ▸ α ▸ Fs) (ext Fs (ext α env))
      in Typed (X ▸ α ▸ Fs ▸ Hs) (ext Hs (ext Fs (ext α env))) l c
           (Block.method-type m k A B M)
    → Premises m k l A B M c X env
  premises m k l A B M c X env TA TB TM Tc =
    let sA = term-stable TA
        cA = term-type TA
        sB = term-stable TB
        cB = term-type TB
        ew = tree-value m k A B X env
        sM = transport (λ v → Stable (meaning M) (X ▸ v) (ext v env)) ew
               (term-stable TM)
        Tm′ = method-model m k l A B M c X env sA cA sB cB sM Tc
    in record
      { shape-stable = sA
      ; shape-code = cA
      ; position-stable = sB
      ; position-code = cB
      ; motive-stable = sM
      ; motive-code =
          transport (λ v → Code R l (meaning M (X ▸ v) (ext v env))) ew
            (term-type TM)
      ; method-stable = term-stable Tm′
      ; method-typed =
          term-type Tm′ ∙
            method-type-model m k l A B M X env sA cA sB cB sM
      }

  -- The method's stability and type at the model's method context, moved
  -- along an equation of the values of the shape, position and motive
  -- types.
  method-moved :
    {n : ℕ} (m k l : ℕ) (c : Raw.Expression C (suc (suc (suc n)))) (X : Ob)
    (env : Vec (Tm X) n) (α : Tm X) (β : Tm (X ▸ α))
    (N : Tm (X ▸ tree m k α β)) (α′ : Tm X) (β′ : Tm (X ▸ α′))
    (N′ : Tm (X ▸ tree m k α′ β′))
    → _＝_ {A = Σ (Tm X) (λ x → Σ (Tm (X ▸ x)) (λ b → Tm (X ▸ tree m k x b)))}
        (α , β , N) (α′ , β′ , N′)
    → let F = children-type R products m k α β (tree m k α β)
          H = hypotheses-type R products m k l α β (tree m k α β) N
          F′ = children-type R products m k α′ β′ (tree m k α′ β′)
          H′ = hypotheses-type R products m k l α′ β′ (tree m k α′ β′) N′
      in Stable (meaning c) (X ▸ α ▸ F ▸ H) (ext H (ext F (ext α env)))
         × (type-of (meaning c (X ▸ α ▸ F ▸ H) (ext H (ext F (ext α env))))
           ＝ N [ p ∘ p ∘ p
               ⨾ supremum m k (α [ p ] [ p ] [ p ])
                   (β [ (p ∘ p ∘ p) ∘ p ⨾ q (α [ p ] [ p ] [ p ]) ])
                   (q α [ p ] [ p ]) (q F [ p ]) ])
      → Stable (meaning c) (X ▸ α′ ▸ F′ ▸ H′) (ext H′ (ext F′ (ext α′ env)))
        × (type-of (meaning c (X ▸ α′ ▸ F′ ▸ H′) (ext H′ (ext F′ (ext α′ env))))
          ＝ N′ [ p ∘ p ∘ p
               ⨾ supremum m k (α′ [ p ] [ p ] [ p ])
                   (β′ [ (p ∘ p ∘ p) ∘ p ⨾ q (α′ [ p ] [ p ] [ p ]) ])
                   (q α′ [ p ] [ p ]) (q F′ [ p ]) ])
  method-moved m k l c X env α β N .α .β .N refl s = s

  -- The premises of a method c, carried to equal shape, position and
  -- motive types.
  premises-equal :
    {n : ℕ} (m k l : ℕ) (A A′ : Raw.Expression C n)
    (B B′ M M′ : Raw.Expression C (suc n))
    (c : Raw.Expression C (suc (suc (suc n)))) (X : Ob)
    (env : Vec (Tm X) n)
    → Premises m k l A B M c X env
    → Stable (meaning A′) X env → Code R m (meaning A′ X env)
    → Stable (meaning B′) (X ▸ meaning A′ X env) (ext (meaning A′ X env) env)
    → Code R k
        (meaning B′ (X ▸ meaning A′ X env) (ext (meaning A′ X env) env))
    → let α′ = meaning A′ X env
          w′ = tree m k α′ (meaning B′ (X ▸ α′) (ext α′ env))
      in Stable (meaning M′) (X ▸ w′) (ext w′ env)
         → Code R l (meaning M′ (X ▸ w′) (ext w′ env))
         → let α = meaning A X env
               β = meaning B (X ▸ α) (ext α env)
               w = tree m k α β
           in meaning A X env ＝ α′
              → β ＝ meaning B′ (X ▸ α) (ext α env)
              → meaning M (X ▸ w) (ext w env)
                ＝ meaning M′ (X ▸ w) (ext w env)
              → Premises m k l A′ B′ M′ c X env
  premises-equal m k l A A′ B B′ M M′ c X env P sA′ cA′ sB′ cB′ sM′ cM′ eA eB
    eM =
    let α = meaning A X env
        β = meaning B (X ▸ α) (ext α env)
        w = tree m k α β
        α′ = meaning A′ X env
        β′ = meaning B′ (X ▸ α′) (ext α′ env)
        w′ = tree m k α′ β′
        eq : _＝_
               {A = Σ (Tm X)
                      (λ x → Σ (Tm (X ▸ x)) (λ b → Tm (X ▸ tree m k x b)))}
               (α , β , meaning M (X ▸ w) (ext w env))
               (α′ , β′ , meaning M′ (X ▸ w′) (ext w′ env))
        eq = ap (λ N″ → α , β , N″) eM ∙
               (ap
                   (λ b → α , b
                      , meaning M′ (X ▸ tree m k α b) (ext (tree m k α b) env))
                   eB ∙
                 ap
                   (λ x →
                      let b = meaning B′ (X ▸ x) (ext x env)
                      in x , b , meaning M′ (X ▸ tree m k x b)
                                   (ext (tree m k x b) env))
                   eA)
        sc = Generic.Premises.method-stable P
        tc = Generic.Premises.method-typed P
        moved = method-moved m k l c X env α β
                  (meaning M (X ▸ w) (ext w env)) α′ β′
                  (meaning M′ (X ▸ w′) (ext w′ env)) eq (sc , tc)
    in record
      { shape-stable = sA′
      ; shape-code = cA′
      ; position-stable = sB′
      ; position-code = cB′
      ; motive-stable = sM′
      ; motive-code = cM′
      ; method-stable = pr₁ moved
      ; method-typed = pr₂ moved
      }

  ----------------------------------------------------------------------
  -- Stability and typing of induction

  induction-stable :
    {n : ℕ} (m k l : ℕ) (A : Raw.Expression C n)
    (B M : Raw.Expression C (suc n))
    (c : Raw.Expression C (suc (suc (suc n)))) (t : Raw.Expression C n)
    (X : Ob) (env : Vec (Tm X) n)
    → Premises m k l A B M c X env → Stable (meaning t) X env
    → type-of (meaning t X env)
      ＝ tree m k (meaning A X env)
          (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
    → Stable (meaning (Formers.tree-induction m k l A B M c t)) X env
  induction-stable m k l A B M c t X env P st tt Y τ =
    let α = meaning A X env
        β = meaning B (X ▸ α) (ext α env)
        w = tree m k α β
        N = meaning M (X ▸ w) (ext w env)
        F = children-type R products m k α β w
        H = hypotheses-type R products m k l α β w N
        G = tree-induction m k l α β N
              (meaning c (X ▸ α ▸ F ▸ H) (ext H (ext F (ext α env))))
        envτ = env [ τ ]ᵉ
        α′ = meaning A Y envτ
        β′ = meaning B (Y ▸ α′) (ext α′ envτ)
        w′ = tree m k α′ β′
        N′ = meaning M (Y ▸ w′) (ext w′ envτ)
        F′ = children-type R products m k α′ β′ w′
        H′ = hypotheses-type R products m k l α′ β′ w′ N′
        G′ = tree-induction m k l α′ β′ N′
               (meaning c (Y ▸ α′ ▸ F′ ▸ H′) (ext H′ (ext F′ (ext α′ envτ))))
        u = meaning t X env
        cw = tree-type m k α β (Generic.Premises.shape-code P)
               (Generic.Premises.position-code P)
    in induction-value m k l A B M c t Y envτ ∙
         (ap (λ v → G′ [ id ⨾ v ]) (st Y τ) ∙
           (generic-stable m k l A B M c X env P τ (u [ τ ])
               (type-of-[] u τ ∙ ap (λ s → s [ τ ]) tt) ∙
             (ap (λ μ → G [ μ ⨾ u [ τ ] ]) (id-left τ ⁻¹) ∙
               (Environment.⨾-[] R (m ⊔ℕ k) w G id u τ cw
                     (tt ∙ [id] w ⁻¹) ⁻¹ ∙
                 ap (λ s → s [ τ ])
                   (induction-value m k l A B M c t X env ⁻¹)))))

  -- The model's typing law of the generic term, over variables: the
  -- method's type spelled at the extended context meets the law's
  -- spelling at the model's method context on small terms.
  generic-type :
    {X : Ob} (m k l : ℕ) (a : Tm X) (b : Tm (X ▸ a))
    (N : Tm (X ▸ tree m k a b))
    → let F = children-type R products m k a b (tree m k a b)
          H = hypotheses-type R products m k l a b (tree m k a b) N
      in (c : Tm (X ▸ a ▸ F ▸ H)) → Code R m a → Code R k b → Code R l N
         → type-of c
           ＝ N [ p ∘ p ∘ p
               ⨾ supremum m k (a [ p ] [ p ] [ p ])
                   (b [ (p ∘ p ∘ p) ∘ p ⨾ q (a [ p ] [ p ] [ p ]) ])
                   (q a [ p ] [ p ]) (q F [ p ]) ]
         → type-of (tree-induction m k l a b N c) ＝ N
  generic-type m k l a b N c ta tb tN tc =
    tree-induction-type m k l a b N c ta tb tN tc

  induction-typed :
    {n : ℕ} (m k l : ℕ) (A : Raw.Expression C n)
    (B M : Raw.Expression C (suc n))
    (c : Raw.Expression C (suc (suc (suc n)))) (t : Raw.Expression C n)
    (X : Ob) (env : Vec (Tm X) n)
    → Premises m k l A B M c X env
    → Typed (X ▸ meaning (Formers.tree m k A B) X env)
        (ext (meaning (Formers.tree m k A B) X env) env) (suc l) M
        (Formers.universe l)
    → Typed X env (m ⊔ℕ k) t (Formers.tree m k A B)
    → Typed X env l (Formers.tree-induction m k l A B M c t)
        (Formers.instantiate M t)
  induction-typed m k l A B M c t X env P TM Tt =
    let α = meaning A X env
        β = meaning B (X ▸ α) (ext α env)
        w = tree m k α β
        N = meaning M (X ▸ w) (ext w env)
        F = children-type R products m k α β w
        H = hypotheses-type R products m k l α β w N
        c₀ = meaning c (X ▸ α ▸ F ▸ H) (ext H (ext F (ext α env)))
        G = tree-induction m k l α β N c₀
        u = meaning t X env
        T = Formers.tree m k A B
        ew = tree-value m k A B X env
        tt = term-type Tt ∙ ew
        TI = instance-as-type (m ⊔ℕ k) l T M t X env TM Tt
        cA = Generic.Premises.shape-code P
        cB = Generic.Premises.position-code P
        cM = Generic.Premises.motive-code P
        tc = Generic.Premises.method-typed P
    in record
      { type-stable = term-stable TI
      ; type-code = term-type TI
      ; term-stable =
          induction-stable m k l A B M c t X env P (term-stable Tt) tt
      ; term-type =
          ap type-of (induction-value m k l A B M c t X env) ∙
            (⨾-type w N G id u (tt ∙ [id] w ⁻¹)
                (generic-type m k l α β N c₀ cA cB cM tc) ∙
              (ap (λ v → meaning M (X ▸ v) (ext v env) [ id ⨾ u ]) (ew ⁻¹) ∙
                instantiate-at (m ⊔ℕ k) M t X (meaning T X env) env
                    (term-stable TM) (term-stable Tt) (term-type Tt)
                    (type-code Tt) ⁻¹))
      }
