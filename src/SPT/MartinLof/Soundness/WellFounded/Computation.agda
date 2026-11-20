{-# OPTIONS --safe --without-K --no-projection-like #-}

module SPT.MartinLof.Soundness.WellFounded.Computation where

-- The β rule of W-types in the soundness of the core theory: induction at
-- sup a f is the method at a, f and the induction hypotheses
-- λ y. rec (f y) (Rules.WellFounded's `hypotheses`).
--
-- The child f y of sup a f, at the extension by B a, has the model's value
-- (`child-value`), is stable (`child-stable`) and is a tree
-- (`child-type`). The recursive call at the child is the generic term at
-- the child (`recursion-value`), stable since the generic term is
-- (`recursion-stable`). So the hypotheses have the value the model's β
-- law names (`hypotheses-value-at`), are stable (`hypotheses-stable`) and
-- have the model's hypotheses type at the section of a and f
-- (`hypotheses-type-at`). Induction at sup a f is then the method's
-- instance (`computation-value`, through the model's β law read over
-- variables, `generic-supremum`), and that instance is stable
-- (`instance₃-stable`).

open import SPT.Base hiding (Lift; _∘_; id; lift; lower; zero)
open import SPT.Foundation.Vectors.Tabulation using (tabulate-lookup)
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Tree as Tree
import SPT.Foundation.Tree.Binding as Binding
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
open import SPT.MartinLof.Model.Russell using
  (Russell; Code; code-[]; section)
open import SPT.MartinLof.Model.Sigma using (Sigma)
open import SPT.MartinLof.Model.Sum using (Sum)
open import SPT.MartinLof.Model.Unit using (Unit)
open import SPT.MartinLof.Model.WellFounded using
  (WellFounded; children-type; hypotheses-type)
import SPT.MartinLof.Soundness.Environment as Environment
import SPT.MartinLof.Soundness.Instances as Instances
import SPT.MartinLof.Soundness.Interpretation as Interpretation
import SPT.MartinLof.Soundness.Pi as Products
import SPT.MartinLof.Soundness.Transport as Transport
import SPT.MartinLof.Soundness.Typing as Typing
import SPT.MartinLof.Soundness.WellFounded.Generic as Generic
import SPT.MartinLof.Soundness.WellFounded.Induction as Induction
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
  (let bound-meaning = Transport.bound-meaning R lifting products pairs paths
                         trees nothing one sums numbers operations subuniverses
                           constant)
  (let weaken-at = Instances.weaken-at R lifting products pairs paths trees
                     nothing one sums numbers operations subuniverses constant)
  (let weaken-stable = Instances.weaken-stable R lifting products pairs paths
                         trees nothing one sums numbers operations subuniverses
                           constant)
  (let rename-value = Instances.rename-value R lifting products pairs paths
                        trees nothing one sums numbers operations subuniverses
                          constant)
  (let instantiate-value = Instances.instantiate-value R lifting products
                             pairs paths trees nothing one sums numbers
                             operations subuniverses constant)
  (let instantiate₃-value = Instances.instantiate₃-value R lifting products
                              pairs paths trees nothing one sums numbers
                              operations subuniverses constant)
  (let instantiate-at = Instances.instantiate-at R lifting products pairs
                          paths trees nothing one sums numbers
                          operations subuniverses constant)
  (let instantiate-stable = Instances.instantiate-stable R lifting products
                              pairs paths trees nothing one sums numbers
                              operations subuniverses constant)
  (let extended-stable = Instances.extended-stable R lifting products pairs
                           paths trees nothing one sums numbers
                           operations subuniverses constant)
  (let substitute-stable = Instances.substitute-stable R lifting products
                             pairs paths trees nothing one sums numbers
                             operations subuniverses constant)
  (let p-⨾ = Typing.p-⨾ R lifting products pairs paths trees nothing one
               sums numbers operations subuniverses constant)
  (let p-section = Typing.p-section R lifting products pairs paths trees
                     nothing one sums numbers operations subuniverses constant)
  (let ⨾-type = Typing.⨾-type R lifting products pairs paths trees nothing
                  one sums numbers operations subuniverses constant)
  (let ⨾-code = Typing.⨾-code R lifting products pairs paths trees nothing
                  one sums numbers operations subuniverses constant)
  (let instance-code = Typing.instance-code R lifting products pairs paths
                         trees nothing one sums numbers operations subuniverses
                           constant)
  (let stable-extend = Typing.stable-extend R lifting products pairs paths
                         trees nothing one sums numbers operations subuniverses
                           constant)
  (let stable-lift = Typing.stable-lift R lifting products pairs paths trees
                       nothing one sums numbers operations subuniverses
                         constant)
  (let binder-type = Typing.binder-type R lifting products pairs paths trees
                       nothing one sums numbers operations subuniverses
                         constant)
  (let ext-section₂ = Typing.ext-section₂ R lifting products pairs paths
                        trees nothing one sums numbers operations subuniverses
                          constant)
  (let rename-stable = Typing.rename-stable R lifting products pairs paths
                         trees nothing one sums numbers operations subuniverses
                           constant)
  (let lambda-value = Products.lambda-value R lifting products pairs paths
                        trees nothing one sums numbers operations subuniverses
                          constant)
  (let lambda-stable = Products.lambda-stable R lifting products pairs paths
                         trees nothing one sums numbers operations subuniverses
                           constant)
  (let application-stable = Products.application-stable R lifting products
                              pairs paths trees nothing one sums numbers
                              operations subuniverses constant)
  (let tree-value = Trees.tree-value R lifting products pairs paths trees
                      nothing one sums numbers operations subuniverses constant)
  (let tree-stable = Trees.tree-stable R lifting products pairs paths trees
                       nothing one sums numbers operations subuniverses
                         constant)
  (let supremum-value = Trees.supremum-value R lifting products pairs paths
                          trees nothing one sums numbers operations
                            subuniverses constant)
  (let induction-value = Trees.induction-value R lifting products pairs
                           paths trees nothing one sums numbers
                           operations subuniverses constant)
  (let hypotheses-value = Method.hypotheses-value R lifting products pairs
                            paths trees nothing one sums numbers
                            operations subuniverses constant)
  (let arrow-[] = Generic.arrow-[] R lifting products pairs paths trees
                    nothing one sums numbers operations subuniverses constant)
  (let Premises = Generic.Premises R lifting products pairs paths trees
                    nothing one sums numbers operations subuniverses constant)
  (let generic-stable = Generic.generic-stable R lifting products pairs
                          paths trees nothing one sums numbers
                          operations subuniverses constant)
  (let weakened-induction-value = Generic.weakened-induction-value R lifting
                                    products pairs paths trees nothing one
                                    sums numbers operations subuniverses
                                      constant)
  (let hypotheses-model = Induction.hypotheses-model R lifting products pairs
                            paths trees nothing one sums numbers
                            operations subuniverses constant)
  (let generic-type = Induction.generic-type R lifting products pairs paths
                        trees nothing one sums numbers operations subuniverses
                          constant)
  (let hypotheses-code = Generic.hypotheses-code R lifting products pairs
                           paths trees nothing one sums numbers
                           operations subuniverses constant)
  where

  ----------------------------------------------------------------------
  -- The model's β law and the child's type, over variables

  generic-supremum :
    {X : Ob} (m k l : ℕ) (a : Tm X) (b : Tm (X ▸ a))
    (N : Tm (X ▸ tree m k a b))
    → let F = children-type R products m k a b (tree m k a b)
          H = hypotheses-type R products m k l a b (tree m k a b) N
      in (c : Tm (X ▸ a ▸ F ▸ H)) (x f : Tm X) → Code R m a → Code R k b
         → Code R l N
         → type-of c
           ＝ N [ p ∘ p ∘ p
               ⨾ supremum m k (a [ p ] [ p ] [ p ])
                   (b [ (p ∘ p ∘ p) ∘ p ⨾ q (a [ p ] [ p ] [ p ]) ])
                   (q a [ p ] [ p ]) (q F [ p ]) ]
         → (tx : type-of x ＝ a)
         → type-of f ＝ pi k (m ⊔ℕ k) (b [ id ⨾ x ]) (tree m k a b [ p ])
         → (e : type-of f ＝ F [ section R a x tx ])
         → tree-induction m k l a b N c [ id ⨾ supremum m k a b x f ]
           ＝ c [ extend F (section R a x tx) f e
               ⨾ lambda k l (b [ id ⨾ x ])
                   (N [ p ⨾ application k (m ⊔ℕ k) (b [ id ⨾ x ] [ p ])
                              (tree m k a b [ p ] [ p ]) (f [ p ])
                              (q (b [ id ⨾ x ])) ])
                   (tree-induction m k l a b N c
                      [ p ⨾ application k (m ⊔ℕ k) (b [ id ⨾ x ] [ p ])
                              (tree m k a b [ p ] [ p ]) (f [ p ])
                              (q (b [ id ⨾ x ])) ]) ]
  generic-supremum m k l a b N c x f ta tb tN tc tx tf e =
    tree-induction-supremum m k l a b N c x f ta tb tN tc tx tf e

  -- f y at the new variable y of b: a term of w past the binder.
  child-type :
    {X : Ob} (m k : ℕ) (b w f : Tm X) → Code R k b → Code R (m ⊔ℕ k) w
    → type-of f ＝ pi k (m ⊔ℕ k) b (w [ p ])
    → type-of
        (application k (m ⊔ℕ k) (b [ p ]) (w [ p ] [ p ]) (f [ p ]) (q b))
      ＝ w [ p ]
  child-type m k b w f cb cw tf =
    let cbp = code-[] R k b p cb
        cwp = code-[] R (m ⊔ℕ k) w p cw
    in application-type k (m ⊔ℕ k) (b [ p ]) (w [ p ] [ p ]) (f [ p ]) (q b)
           cbp (code-[] R (m ⊔ℕ k) (w [ p ]) p cwp)
           (type-of-[] f p ∙
             (ap (λ s → s [ p ]) tf ∙ arrow-[] k (m ⊔ℕ k) b w p cb cw))
           (q-type k b cb) ∙
         (p-⨾ (b [ p ]) (w [ p ]) id (q b)
             (q-type k b cb ∙ [id] (b [ p ]) ⁻¹) ∙
           [id] (w [ p ]))

  -- The children's type at the section of a, and f's type there.
  children-section :
    {X : Ob} (m k : ℕ) (a : Tm X) (b : Tm (X ▸ a)) (x f : Tm X)
    → Code R k b → Code R (m ⊔ℕ k) (tree m k a b) → (tx : type-of x ＝ a)
    → type-of f ＝ pi k (m ⊔ℕ k) (b [ id ⨾ x ]) (tree m k a b [ p ])
    → type-of f
      ＝ children-type R products m k a b (tree m k a b) [ section R a x tx ]
  children-section m k a b x f cb cw tx tf =
    tf ∙
      (arrow-[] k (m ⊔ℕ k) b (tree m k a b [ p ]) (section R a x tx) cb
            (code-[] R (m ⊔ℕ k) (tree m k a b) p cw) ∙
          ap₂ (λ u v → pi k (m ⊔ℕ k) u (v [ p ]))
            (Environment.⨾-section R a x b tx)
            (p-section a (tree m k a b) x tx)) ⁻¹

  ----------------------------------------------------------------------
  -- The child f y

  child-value :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (a f : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Stable (meaning A) X env → Code R m (meaning A X env)
    → Stable (meaning B) (X ▸ meaning A X env) (ext (meaning A X env) env)
    → Code R k (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
    → Stable (meaning a) X env → type-of (meaning a X env) ＝ meaning A X env
    → Stable (meaning f) X env
    → let α = meaning A X env
          w = tree m k α (meaning B (X ▸ α) (ext α env))
          βa = meaning (Formers.instantiate B a) X env
      in meaning (Block.child m k A B a f) (X ▸ βa) (ext βa env)
         ＝ application k (m ⊔ℕ k) (βa [ p ]) (w [ p ] [ p ])
             (meaning f X env [ p ]) (q βa)
  child-value {n} m k A B a f X env sA cA sB cB sa ta sf =
    let α = meaning A X env
        T = Formers.tree m k A B
        βa = meaning (Formers.instantiate B a) X env
        env₁ = ext βa env
        sT = tree-stable m k A B X env sA cA sB cB
        eb₁ = weaken-at (Formers.instantiate B a) X βa env
                (instantiate-stable m B a X α env sB sa ta cA)
    in ap
           (λ b′ → application k (m ⊔ℕ k) b′
              (meaning
                (Binding.bound (Raw.binding C) (suc n) 1
                  (Formers.weaken (Formers.weaken T)))
                (X ▸ βa ▸ b′) (ext b′ env₁))
              (meaning (Formers.weaken f) (X ▸ βa) env₁) (q βa))
           eb₁ ∙
         ap₂ (λ u v → application k (m ⊔ℕ k) (βa [ p ]) u v (q βa))
           (bound-meaning 1 (Formers.weaken (Formers.weaken T))
               (X ▸ βa ▸ βa [ p ]) (ext (βa [ p ]) env₁) ∙
             (weaken-at (Formers.weaken T) (X ▸ βa) (βa [ p ]) env₁
                 (weaken-stable T X βa env sT) ∙
               (ap (λ s → s [ p ]) (weaken-at T X βa env sT) ∙
                 ap (λ s → s [ p ] [ p ]) (tree-value m k A B X env))))
           (weaken-at f X βa env sf)

  child-stable :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (a f : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Stable (meaning A) X env → Code R m (meaning A X env)
    → Stable (meaning B) (X ▸ meaning A X env) (ext (meaning A X env) env)
    → Code R k (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
    → Stable (meaning a) X env → type-of (meaning a X env) ＝ meaning A X env
    → Stable (meaning f) X env
    → let α = meaning A X env
          β = meaning B (X ▸ α) (ext α env)
      in type-of (meaning f X env)
         ＝ pi k (m ⊔ℕ k) (β [ id ⨾ meaning a X env ]) (tree m k α β [ p ])
         → let βa = meaning (Formers.instantiate B a) X env
           in Stable (meaning (Block.child m k A B a f)) (X ▸ βa)
                (ext βa env)
  child-stable m k A B a f X env sA cA sB cB sa ta sf tf =
    let α = meaning A X env
        β = meaning B (X ▸ α) (ext α env)
        w = tree m k α β
        T = Formers.tree m k A B
        βa = meaning (Formers.instantiate B a) X env
        env₁ = ext βa env
        cw = tree-type m k α β cA cB
        sT = tree-stable m k A B X env sA cA sB cB
        si = instantiate-stable m B a X α env sB sa ta cA
        eβa = instantiate-at m B a X α env sB sa ta cA
        cβa = transport (Code R k) (eβa ⁻¹)
                (instance-code m k α (meaning a X env) β ta cA cB)
        b₁ = meaning (Formers.weaken (Formers.instantiate B a)) (X ▸ βa) env₁
        eb₁ = weaken-at (Formers.instantiate B a) X βa env si
        ecod = λ (b′ : Tm (X ▸ βa)) →
                 weaken-at (Formers.weaken T) (X ▸ βa) b′ env₁
                     (weaken-stable T X βa env sT) ∙
                   (ap (λ s → s [ p ]) (weaken-at T X βa env sT) ∙
                     ap (λ s → s [ p ] [ p ]) (tree-value m k A B X env))
        tfa = tf ∙ ap (λ u → pi k (m ⊔ℕ k) u (w [ p ])) (eβa ⁻¹)
    in application-stable k (m ⊔ℕ k)
         (Formers.weaken (Formers.instantiate B a))
         (Formers.weaken (Formers.weaken T)) (Formers.weaken f)
         (Tree.hole fzero) (X ▸ βa) env₁
         (weaken-stable (Formers.instantiate B a) X βa env si)
         (transport (Code R k) (eb₁ ⁻¹) (code-[] R k βa p cβa))
         (weaken-stable (Formers.weaken T) (X ▸ βa) b₁ env₁
           (weaken-stable T X βa env sT))
         (transport (Code R (m ⊔ℕ k)) (ecod b₁ ⁻¹)
           (code-[] R (m ⊔ℕ k) (w [ p ]) p (code-[] R (m ⊔ℕ k) w p cw)))
         (weaken-stable f X βa env sf)
         (ap type-of (weaken-at f X βa env sf) ∙
           (type-of-[] (meaning f X env) p ∙
             (ap (λ s → s [ p ]) tfa ∙
               (arrow-[] k (m ⊔ℕ k) βa w p cβa cw ∙
                 (ap
                       (λ b′ → pi k (m ⊔ℕ k) b′
                          (meaning (Formers.weaken (Formers.weaken T))
                            (X ▸ βa ▸ b′) (ext b′ env₁)))
                       eb₁ ∙
                     ap (pi k (m ⊔ℕ k) (βa [ p ]))
                       (ecod (βa [ p ]))) ⁻¹))))
         (Environment.stable-lookup R fzero (X ▸ βa) env₁)
         (q-type k βa cβa ∙ eb₁ ⁻¹)

  ----------------------------------------------------------------------
  -- The motive and the recursive call at the child

  -- M at f y, read at the extension by B a.
  motive-at-child :
    {n : ℕ} (m k l : ℕ) (A : Raw.Expression C n)
    (B M : Raw.Expression C (suc n))
    (c : Raw.Expression C (suc (suc (suc n)))) (a f : Raw.Expression C n)
    (X : Ob) (env : Vec (Tm X) n) → Premises m k l A B M c X env
    → Stable (meaning a) X env → type-of (meaning a X env) ＝ meaning A X env
    → Stable (meaning f) X env
    → let α = meaning A X env
          β = meaning B (X ▸ α) (ext α env)
      in type-of (meaning f X env)
         ＝ pi k (m ⊔ℕ k) (β [ id ⨾ meaning a X env ]) (tree m k α β [ p ])
         → let α = meaning A X env
               β = meaning B (X ▸ α) (ext α env)
               w = tree m k α β
               N = meaning M (X ▸ w) (ext w env)
               F = children-type R products m k α β w
               H = hypotheses-type R products m k l α β w N
               G = tree-induction m k l α β N
                     (meaning c (X ▸ α ▸ F ▸ H) (ext H (ext F (ext α env))))
               βa = meaning (Formers.instantiate B a) X env
           in meaning
                (Formers.instantiate (Formers.weaken-past n 1 1 M)
                  (Block.child m k A B a f))
                (X ▸ βa) (ext βa env)
              ＝ N [ p ⨾ meaning (Block.child m k A B a f) (X ▸ βa)
                          (ext βa env) ]
  motive-at-child {n} m k l A B M c a f X env P sa ta sf tf =
    let α = meaning A X env
        β = meaning B (X ▸ α) (ext α env)
        w = tree m k α β
        N = meaning M (X ▸ w) (ext w env)
        F = children-type R products m k α β w
        H = hypotheses-type R products m k l α β w N
        c₀ = meaning c (X ▸ α ▸ F ▸ H) (ext H (ext F (ext α env)))
        G = tree-induction m k l α β N c₀
        a′ = meaning a X env
        f′ = meaning f X env
        βa = meaning (Formers.instantiate B a) X env
        env₁ = ext βa env
        sA = Generic.Premises.shape-stable P
        cA = Generic.Premises.shape-code P
        sB = Generic.Premises.position-stable P
        cB = Generic.Premises.position-code P
        sM = Generic.Premises.motive-stable P
        cM = Generic.Premises.motive-code P
        sc = Generic.Premises.method-stable P
        tc = Generic.Premises.method-typed P
        cw = tree-type m k α β cA cB
        eβa = instantiate-at m B a X α env sB sa ta cA
        cβa = transport (Code R k) (eβa ⁻¹) (instance-code m k α a′ β ta cA cB)
        tfa = tf ∙ ap (λ u → pi k (m ⊔ℕ k) u (w [ p ])) (eβa ⁻¹)
        ch = meaning (Block.child m k A B a f) (X ▸ βa) env₁
        sch = child-stable m k A B a f X env sA cA sB cB sa ta sf tf
        tch = ap type-of
                  (child-value m k A B a f X env sA cA sB cB sa ta sf) ∙
                child-type m k βa w f′ cβa cw tfa
    in instantiate-value (Formers.weaken-past n 1 1 M)
           (Block.child m k A B a f) (X ▸ βa) env₁ sch ∙
         (rename-value
             (Binding.lift (Raw.binding C) 1 (λ (y : Fin n) → 1 ↑ʳ y)) M
             (X ▸ βa) (ch ∷ env₁) ∙
           (ap (λ es → meaning M (X ▸ βa) (ch ∷ es))
               (tabulate-lookup (env [ p ]ᵉ)) ∙
             stable-extend (meaning M) (m ⊔ℕ k) X w env cw sM p ch tch))

  -- rec (f y), read at the extension by B a: the generic term at f y.
  recursion-value :
    {n : ℕ} (m k l : ℕ) (A : Raw.Expression C n)
    (B M : Raw.Expression C (suc n))
    (c : Raw.Expression C (suc (suc (suc n)))) (a f : Raw.Expression C n)
    (X : Ob) (env : Vec (Tm X) n) → Premises m k l A B M c X env
    → Stable (meaning a) X env → type-of (meaning a X env) ＝ meaning A X env
    → Stable (meaning f) X env
    → let α = meaning A X env
          β = meaning B (X ▸ α) (ext α env)
      in type-of (meaning f X env)
         ＝ pi k (m ⊔ℕ k) (β [ id ⨾ meaning a X env ]) (tree m k α β [ p ])
         → let α = meaning A X env
               β = meaning B (X ▸ α) (ext α env)
               w = tree m k α β
               N = meaning M (X ▸ w) (ext w env)
               F = children-type R products m k α β w
               H = hypotheses-type R products m k l α β w N
               G = tree-induction m k l α β N
                     (meaning c (X ▸ α ▸ F ▸ H) (ext H (ext F (ext α env))))
               βa = meaning (Formers.instantiate B a) X env
           in meaning (Formers.tree-induction m k l (Formers.weaken A)
             (Formers.weaken-past n 1 1 B) (Formers.weaken-past n 1 1 M)
             (Formers.weaken-past n 3 1 c) (Block.child m k A B a f))
                (X ▸ βa) (ext βa env)
              ＝ G [ p ⨾ meaning (Block.child m k A B a f) (X ▸ βa)
                          (ext βa env) ]
  recursion-value {n} m k l A B M c a f X env P sa ta sf tf =
    let α = meaning A X env
        β = meaning B (X ▸ α) (ext α env)
        w = tree m k α β
        N = meaning M (X ▸ w) (ext w env)
        F = children-type R products m k α β w
        H = hypotheses-type R products m k l α β w N
        c₀ = meaning c (X ▸ α ▸ F ▸ H) (ext H (ext F (ext α env)))
        G = tree-induction m k l α β N c₀
        a′ = meaning a X env
        f′ = meaning f X env
        βa = meaning (Formers.instantiate B a) X env
        env₁ = ext βa env
        sA = Generic.Premises.shape-stable P
        cA = Generic.Premises.shape-code P
        sB = Generic.Premises.position-stable P
        cB = Generic.Premises.position-code P
        sM = Generic.Premises.motive-stable P
        cM = Generic.Premises.motive-code P
        sc = Generic.Premises.method-stable P
        tc = Generic.Premises.method-typed P
        cw = tree-type m k α β cA cB
        eβa = instantiate-at m B a X α env sB sa ta cA
        cβa = transport (Code R k) (eβa ⁻¹) (instance-code m k α a′ β ta cA cB)
        tfa = tf ∙ ap (λ u → pi k (m ⊔ℕ k) u (w [ p ])) (eβa ⁻¹)
        ch = meaning (Block.child m k A B a f) (X ▸ βa) env₁
        sch = child-stable m k A B a f X env sA cA sB cB sa ta sf tf
        tch = ap type-of
                  (child-value m k A B a f X env sA cA sB cB sa ta sf) ∙
                child-type m k βa w f′ cβa cw tfa
    in weakened-induction-value m k l A B M c (Block.child m k A B a f)
           (X ▸ βa) (q βa) (env [ p ]ᵉ) ∙
         generic-stable m k l A B M c X env P p ch tch

  recursion-stable :
    {n : ℕ} (m k l : ℕ) (A : Raw.Expression C n)
    (B M : Raw.Expression C (suc n))
    (c : Raw.Expression C (suc (suc (suc n)))) (a f : Raw.Expression C n)
    (X : Ob) (env : Vec (Tm X) n) → Premises m k l A B M c X env
    → Stable (meaning a) X env → type-of (meaning a X env) ＝ meaning A X env
    → Stable (meaning f) X env
    → let α = meaning A X env
          β = meaning B (X ▸ α) (ext α env)
      in type-of (meaning f X env)
         ＝ pi k (m ⊔ℕ k) (β [ id ⨾ meaning a X env ]) (tree m k α β [ p ])
         → let βa = meaning (Formers.instantiate B a) X env
           in Stable (meaning (Formers.tree-induction m k l (Formers.weaken A)
             (Formers.weaken-past n 1 1 B) (Formers.weaken-past n 1 1 M)
             (Formers.weaken-past n 3 1 c) (Block.child m k A B a f)))
                (X ▸ βa) (ext βa env)
  recursion-stable {n} m k l A B M c a f X env P sa ta sf tf Y τ =
    let α = meaning A X env
        β = meaning B (X ▸ α) (ext α env)
        w = tree m k α β
        N = meaning M (X ▸ w) (ext w env)
        F = children-type R products m k α β w
        H = hypotheses-type R products m k l α β w N
        c₀ = meaning c (X ▸ α ▸ F ▸ H) (ext H (ext F (ext α env)))
        G = tree-induction m k l α β N c₀
        a′ = meaning a X env
        f′ = meaning f X env
        βa = meaning (Formers.instantiate B a) X env
        env₁ = ext βa env
        sA = Generic.Premises.shape-stable P
        cA = Generic.Premises.shape-code P
        sB = Generic.Premises.position-stable P
        cB = Generic.Premises.position-code P
        sM = Generic.Premises.motive-stable P
        cM = Generic.Premises.motive-code P
        sc = Generic.Premises.method-stable P
        tc = Generic.Premises.method-typed P
        cw = tree-type m k α β cA cB
        eβa = instantiate-at m B a X α env sB sa ta cA
        cβa = transport (Code R k) (eβa ⁻¹) (instance-code m k α a′ β ta cA cB)
        tfa = tf ∙ ap (λ u → pi k (m ⊔ℕ k) u (w [ p ])) (eβa ⁻¹)
        ch = meaning (Block.child m k A B a f) (X ▸ βa) env₁
        sch = child-stable m k A B a f X env sA cA sB cB sa ta sf tf
        tch = ap type-of
                  (child-value m k A B a f X env sA cA sB cB sa ta sf) ∙
                child-type m k βa w f′ cβa cw tfa
        u = meaning (Block.child m k A B a f) Y (env₁ [ τ ]ᵉ)
        tu = ap type-of (sch Y τ) ∙
               (type-of-[] ch τ ∙
                 (ap (λ s′ → s′ [ τ ]) tch ∙ [∘] w p τ ⁻¹))
    in weakened-induction-value m k l A B M c (Block.child m k A B a f) Y
           (q βa [ τ ]) (env [ p ]ᵉ [ τ ]ᵉ) ∙
         (ap
             (λ E →
                let α″ = meaning A Y E
                    β″ = meaning B (Y ▸ α″) (ext α″ E)
                    w″ = tree m k α″ β″
                    N″ = meaning M (Y ▸ w″) (ext w″ E)
                    F″ = children-type R products m k α″ β″ w″
                    H″ = hypotheses-type R products m k l α″ β″ w″ N″
                in tree-induction m k l α″ β″ N″
                     (meaning c (Y ▸ α″ ▸ F″ ▸ H″)
                       (ext H″ (ext F″ (ext α″ E))))
                     [ id ⨾ u ])
             (Environment.[]ᵉ-∘ R env p τ ⁻¹) ∙
           (generic-stable m k l A B M c X env P (p ∘ τ) u tu ∙
             (ap (λ v → G [ p ∘ τ ⨾ v ]) (sch Y τ) ∙
               (Environment.⨾-[] R (m ⊔ℕ k) w G p ch τ cw tch ⁻¹ ∙
                 ap (λ s′ → s′ [ τ ])
                   (recursion-value m k l A B M c a f X env P sa ta sf
                       tf ⁻¹)))))

  ----------------------------------------------------------------------
  -- The induction hypotheses

  hypotheses-value-at :
    {n : ℕ} (m k l : ℕ) (A : Raw.Expression C n)
    (B M : Raw.Expression C (suc n))
    (c : Raw.Expression C (suc (suc (suc n)))) (a f : Raw.Expression C n)
    (X : Ob) (env : Vec (Tm X) n) → Premises m k l A B M c X env
    → Stable (meaning a) X env → type-of (meaning a X env) ＝ meaning A X env
    → Stable (meaning f) X env
    → let α = meaning A X env
          β = meaning B (X ▸ α) (ext α env)
      in type-of (meaning f X env)
         ＝ pi k (m ⊔ℕ k) (β [ id ⨾ meaning a X env ]) (tree m k α β [ p ])
         → let α = meaning A X env
               β = meaning B (X ▸ α) (ext α env)
               w = tree m k α β
               N = meaning M (X ▸ w) (ext w env)
               F = children-type R products m k α β w
               H = hypotheses-type R products m k l α β w N
               G = tree-induction m k l α β N
                     (meaning c (X ▸ α ▸ F ▸ H) (ext H (ext F (ext α env))))
               a′ = meaning a X env
               f′ = meaning f X env
           in meaning (Block.hypotheses m k l A B M c a f) X env
              ＝ lambda k l (β [ id ⨾ a′ ])
                (N [ p ⨾ application k (m ⊔ℕ k) (β [ id ⨾ a′ ] [ p ])
                           (w [ p ] [ p ]) (f′ [ p ]) (q (β [ id ⨾ a′ ])) ])
                (G [ p ⨾ application k (m ⊔ℕ k) (β [ id ⨾ a′ ] [ p ])
                           (w [ p ] [ p ]) (f′ [ p ]) (q (β [ id ⨾ a′ ])) ])
  hypotheses-value-at {n} m k l A B M c a f X env P sa ta sf tf =
    let α = meaning A X env
        β = meaning B (X ▸ α) (ext α env)
        w = tree m k α β
        N = meaning M (X ▸ w) (ext w env)
        F = children-type R products m k α β w
        H = hypotheses-type R products m k l α β w N
        c₀ = meaning c (X ▸ α ▸ F ▸ H) (ext H (ext F (ext α env)))
        G = tree-induction m k l α β N c₀
        a′ = meaning a X env
        f′ = meaning f X env
        βa = meaning (Formers.instantiate B a) X env
        env₁ = ext βa env
        sA = Generic.Premises.shape-stable P
        cA = Generic.Premises.shape-code P
        sB = Generic.Premises.position-stable P
        cB = Generic.Premises.position-code P
        sM = Generic.Premises.motive-stable P
        cM = Generic.Premises.motive-code P
        sc = Generic.Premises.method-stable P
        tc = Generic.Premises.method-typed P
        cw = tree-type m k α β cA cB
        eβa = instantiate-at m B a X α env sB sa ta cA
        cβa = transport (Code R k) (eβa ⁻¹) (instance-code m k α a′ β ta cA cB)
        tfa = tf ∙ ap (λ u → pi k (m ⊔ℕ k) u (w [ p ])) (eβa ⁻¹)
        ch = meaning (Block.child m k A B a f) (X ▸ βa) env₁
        sch = child-stable m k A B a f X env sA cA sB cB sa ta sf tf
        tch = ap type-of
                  (child-value m k A B a f X env sA cA sB cB sa ta sf) ∙
                child-type m k βa w f′ cβa cw tfa
    in lambda-value k l (Formers.instantiate B a)
           (Formers.instantiate (Formers.weaken-past n 1 1 M)
             (Block.child m k A B a f))
           (Formers.tree-induction m k l (Formers.weaken A)
             (Formers.weaken-past n 1 1 B) (Formers.weaken-past n 1 1 M)
             (Formers.weaken-past n 3 1 c) (Block.child m k A B a f))
           X env ∙
         (ap₂ (lambda k l βa)
             (motive-at-child m k l A B M c a f X env P sa ta sf tf)
             (recursion-value m k l A B M c a f X env P sa ta sf tf) ∙
           (ap (λ v → lambda k l βa (N [ p ⨾ v ]) (G [ p ⨾ v ]))
               (child-value m k A B a f X env sA cA sB cB sa ta sf) ∙
             ap
               (λ b → lambda k l b
                  (N [ p ⨾ application k (m ⊔ℕ k) (b [ p ]) (w [ p ] [ p ])
                             (f′ [ p ]) (q b) ])
                  (G [ p ⨾ application k (m ⊔ℕ k) (b [ p ]) (w [ p ] [ p ])
                             (f′ [ p ]) (q b) ]))
               eβa))

  hypotheses-stable :
    {n : ℕ} (m k l : ℕ) (A : Raw.Expression C n)
    (B M : Raw.Expression C (suc n))
    (c : Raw.Expression C (suc (suc (suc n)))) (a f : Raw.Expression C n)
    (X : Ob) (env : Vec (Tm X) n) → Premises m k l A B M c X env
    → Stable (meaning a) X env → type-of (meaning a X env) ＝ meaning A X env
    → Stable (meaning f) X env
    → let α = meaning A X env
          β = meaning B (X ▸ α) (ext α env)
      in type-of (meaning f X env)
         ＝ pi k (m ⊔ℕ k) (β [ id ⨾ meaning a X env ]) (tree m k α β [ p ])
         → Stable (meaning (Block.hypotheses m k l A B M c a f)) X env
  hypotheses-stable {n} m k l A B M c a f X env P sa ta sf tf =
    let α = meaning A X env
        β = meaning B (X ▸ α) (ext α env)
        w = tree m k α β
        N = meaning M (X ▸ w) (ext w env)
        F = children-type R products m k α β w
        H = hypotheses-type R products m k l α β w N
        c₀ = meaning c (X ▸ α ▸ F ▸ H) (ext H (ext F (ext α env)))
        G = tree-induction m k l α β N c₀
        a′ = meaning a X env
        f′ = meaning f X env
        βa = meaning (Formers.instantiate B a) X env
        env₁ = ext βa env
        sA = Generic.Premises.shape-stable P
        cA = Generic.Premises.shape-code P
        sB = Generic.Premises.position-stable P
        cB = Generic.Premises.position-code P
        sM = Generic.Premises.motive-stable P
        cM = Generic.Premises.motive-code P
        sc = Generic.Premises.method-stable P
        tc = Generic.Premises.method-typed P
        cw = tree-type m k α β cA cB
        eβa = instantiate-at m B a X α env sB sa ta cA
        cβa = transport (Code R k) (eβa ⁻¹) (instance-code m k α a′ β ta cA cB)
        tfa = tf ∙ ap (λ u → pi k (m ⊔ℕ k) u (w [ p ])) (eβa ⁻¹)
        ch = meaning (Block.child m k A B a f) (X ▸ βa) env₁
        sch = child-stable m k A B a f X env sA cA sB cB sa ta sf tf
        tch = ap type-of
                  (child-value m k A B a f X env sA cA sB cB sa ta sf) ∙
                child-type m k βa w f′ cβa cw tfa
        si = instantiate-stable m B a X α env sB sa ta cA
        cwp = code-[] R (m ⊔ℕ k) w p cw
        em = motive-at-child m k l A B M c a f X env P sa ta sf tf
        sM₁ = rename-stable
                (Binding.lift (Raw.binding C) 1 (λ (y : Fin n) → 1 ↑ʳ y)) M
                (X ▸ βa ▸ w [ p ]) (ext (w [ p ]) env₁)
                (transport (Stable (meaning M) (X ▸ βa ▸ w [ p ]))
                  (ap (λ es → q (w [ p ]) ∷ es)
                    (tabulate-lookup (env [ p ]ᵉ [ p ]ᵉ) ⁻¹))
                  (stable-lift (meaning M) (m ⊔ℕ k) X w env cw sM p (w [ p ])
                    (env [ p ]ᵉ) (binder-type (m ⊔ℕ k) w p (w [ p ]) cwp refl)
                    refl))
    in lambda-stable k l (Formers.instantiate B a)
         (Formers.instantiate (Formers.weaken-past n 1 1 M)
           (Block.child m k A B a f))
         (Formers.tree-induction m k l (Formers.weaken A)
           (Formers.weaken-past n 1 1 B) (Formers.weaken-past n 1 1 M)
           (Formers.weaken-past n 3 1 c) (Block.child m k A B a f))
         X env si cβa
         (instantiate-stable (m ⊔ℕ k) (Formers.weaken-past n 1 1 M)
           (Block.child m k A B a f) (X ▸ βa) (w [ p ]) env₁ sM₁ sch tch cwp)
         (transport (Code R l) (em ⁻¹) (⨾-code l w N p ch tch cM))
         (recursion-stable m k l A B M c a f X env P sa ta sf tf)
         (ap type-of
             (recursion-value m k l A B M c a f X env P sa ta sf tf) ∙
           (⨾-type w N G p ch tch (generic-type m k l α β N c₀ cA cB cM tc) ∙
             em ⁻¹))

  -- The hypotheses' type: the model's, at the section of a and f.
  hypotheses-type-at :
    {n : ℕ} (m k l : ℕ) (A : Raw.Expression C n)
    (B M : Raw.Expression C (suc n))
    (c : Raw.Expression C (suc (suc (suc n)))) (a f : Raw.Expression C n)
    (X : Ob) (env : Vec (Tm X) n) → Premises m k l A B M c X env
    → Stable (meaning a) X env
    → (ta : type-of (meaning a X env) ＝ meaning A X env)
    → Stable (meaning f) X env
    → let α = meaning A X env
          β = meaning B (X ▸ α) (ext α env)
          w = tree m k α β
          N = meaning M (X ▸ w) (ext w env)
          F = children-type R products m k α β w
      in type-of (meaning f X env)
         ＝ pi k (m ⊔ℕ k) (β [ id ⨾ meaning a X env ]) (tree m k α β [ p ])
         → Stable
             (meaning
               (Formers.pi k l (Formers.weaken B)
                 (Formers.instantiate-past 3 M
                   (Formers.application k (m ⊔ℕ k)
                     (Formers.weaken (Formers.weaken B))
                     (Formers.weaken
                       (Formers.weaken
                         (Formers.weaken
                           (Formers.weaken (Formers.tree m k A B)))))
                     (Tree.hole (fsuc fzero)) (Tree.hole fzero)))))
             (X ▸ α ▸ F) (ext F (ext α env))
         → (ef : type-of (meaning f X env)
                 ＝ F [ section R α (meaning a X env) ta ])
         → let H = hypotheses-type R products m k l α β w N
           in type-of (meaning (Block.hypotheses m k l A B M c a f) X env)
              ＝ H [ extend F (section R α (meaning a X env) ta)
                      (meaning f X env) ef ]
  hypotheses-type-at m k l A B M c a f X env P sa ta sf tf sH ef =
    let α = meaning A X env
        β = meaning B (X ▸ α) (ext α env)
        w = tree m k α β
        N = meaning M (X ▸ w) (ext w env)
        F = children-type R products m k α β w
        H = hypotheses-type R products m k l α β w N
        c₀ = meaning c (X ▸ α ▸ F ▸ H) (ext H (ext F (ext α env)))
        G = tree-induction m k l α β N c₀
        a′ = meaning a X env
        f′ = meaning f X env
        βa = meaning (Formers.instantiate B a) X env
        env₁ = ext βa env
        sA = Generic.Premises.shape-stable P
        cA = Generic.Premises.shape-code P
        sB = Generic.Premises.position-stable P
        cB = Generic.Premises.position-code P
        sM = Generic.Premises.motive-stable P
        cM = Generic.Premises.motive-code P
        sc = Generic.Premises.method-stable P
        tc = Generic.Premises.method-typed P
        cw = tree-type m k α β cA cB
        eβa = instantiate-at m B a X α env sB sa ta cA
        cβa = transport (Code R k) (eβa ⁻¹) (instance-code m k α a′ β ta cA cB)
        tfa = tf ∙ ap (λ u → pi k (m ⊔ℕ k) u (w [ p ])) (eβa ⁻¹)
        ch = meaning (Block.child m k A B a f) (X ▸ βa) env₁
        sch = child-stable m k A B a f X env sA cA sB cB sa ta sf tf
        tch = ap type-of
                  (child-value m k A B a f X env sA cA sB cB sa ta sf) ∙
                child-type m k βa w f′ cβa cw tfa
        b₀ = β [ id ⨾ a′ ]
        cb₀ = instance-code m k α a′ β ta cA cB
        chd = application k (m ⊔ℕ k) (b₀ [ p ]) (w [ p ] [ p ]) (f′ [ p ])
                (q b₀)
        tchd = child-type m k b₀ w f′ cb₀ cw tf
        cF = pi-type k (m ⊔ℕ k) β (w [ p ] [ p ]) cB
               (code-[] R (m ⊔ℕ k) (w [ p ]) p (code-[] R (m ⊔ℕ k) w p cw))
        cH = hypotheses-code m k l α β w N cB cw cM
        ρ₂ = extend F (section R α a′ ta) f′ ef
        h′ = meaning (Block.hypotheses m k l A B M c a f) X env
        ew = tree-value m k A B X env
        ebv = instantiate-value B a X env sa ⁻¹ ∙ eβa
    in ap type-of
           (hypotheses-value-at m k l A B M c a f X env P sa ta sf tf) ∙
         (lambda-type k l b₀ (N [ p ⨾ chd ]) (G [ p ⨾ chd ]) cb₀
             (⨾-code l w N p chd tchd cM)
             (⨾-type w N G p chd tchd
               (generic-type m k l α β N c₀ cA cB cM tc)) ∙
           (ap (λ s′ → s′ [ ρ₂ ])
                 (hypotheses-model m k l A B M X env sA cA sB cB sM ⁻¹) ∙
               (sH X ρ₂ ⁻¹ ∙
                 (ap (meaning (Formers.pi k l (Formers.weaken B)
                       (Formers.instantiate-past 3 M
                         (Formers.application k (m ⊔ℕ k)
                           (Formers.weaken (Formers.weaken B))
                           (Formers.weaken
                             (Formers.weaken
                               (Formers.weaken
                                 (Formers.weaken (Formers.tree m k A B)))))
                           (Tree.hole (fsuc fzero))
                           (Tree.hole fzero))))
                       X)
                     (ext-section₂ m (k ⊔ℕ (m ⊔ℕ k)) α F env a′ f′ ta cA ef
                       cF) ∙
                   (hypotheses-value m k l A B M X f′ a′ env
                       (Environment.stable-section R m (meaning B) α a′ env
                         ta cA sB)
                       (transport (Code R k) (ebv ⁻¹) cb₀)
                       (tree-stable m k A B X env sA cA sB cB)
                       (transport (Code R (m ⊔ℕ k)) (ew ⁻¹) cw)
                       (tf ∙
                         ap₂ (λ u v → pi k (m ⊔ℕ k) u (v [ p ])) ebv
                             ew ⁻¹) ∙
                     (ap₂
                         (λ u v → pi k l u
                            (meaning M (X ▸ u)
                              (application k (m ⊔ℕ k) (u [ p ]) (v [ p ] [ p ])
                                 (f′ [ p ]) (q u)
                               ∷ env [ p ]ᵉ)))
                         ebv ew ∙
                       ap (pi k l b₀)
                         (stable-extend (meaning M) (m ⊔ℕ k) X w env cw sM p
                           chd tchd)))))) ⁻¹)

  ----------------------------------------------------------------------
  -- Induction at sup a f

  computation-value :
    {n : ℕ} (m k l : ℕ) (A : Raw.Expression C n)
    (B M : Raw.Expression C (suc n))
    (c : Raw.Expression C (suc (suc (suc n)))) (a f : Raw.Expression C n)
    (X : Ob) (env : Vec (Tm X) n) → Premises m k l A B M c X env
    → Stable (meaning a) X env
    → (ta : type-of (meaning a X env) ＝ meaning A X env)
    → Stable (meaning f) X env
    → let α = meaning A X env
          β = meaning B (X ▸ α) (ext α env)
          w = tree m k α β
          N = meaning M (X ▸ w) (ext w env)
          F = children-type R products m k α β w
      in type-of (meaning f X env)
         ＝ pi k (m ⊔ℕ k) (β [ id ⨾ meaning a X env ]) (tree m k α β [ p ])
         → Stable
             (meaning
               (Formers.pi k l (Formers.weaken B)
                 (Formers.instantiate-past 3 M
                   (Formers.application k (m ⊔ℕ k)
                     (Formers.weaken (Formers.weaken B))
                     (Formers.weaken
                       (Formers.weaken
                         (Formers.weaken
                           (Formers.weaken (Formers.tree m k A B)))))
                     (Tree.hole (fsuc fzero)) (Tree.hole fzero)))))
             (X ▸ α ▸ F) (ext F (ext α env))
         → (ef : type-of (meaning f X env)
                 ＝ F [ section R α (meaning a X env) ta ])
         → meaning
             (Formers.tree-induction m k l A B M c
               (Formers.supremum m k A B a f))
             X env
           ＝ meaning
               (Formers.instantiate₃ c a f
                 (Block.hypotheses m k l A B M c a f))
               X env
  computation-value m k l A B M c a f X env P sa ta sf tf sH ef =
    let α = meaning A X env
        β = meaning B (X ▸ α) (ext α env)
        w = tree m k α β
        N = meaning M (X ▸ w) (ext w env)
        F = children-type R products m k α β w
        H = hypotheses-type R products m k l α β w N
        c₀ = meaning c (X ▸ α ▸ F ▸ H) (ext H (ext F (ext α env)))
        G = tree-induction m k l α β N c₀
        a′ = meaning a X env
        f′ = meaning f X env
        βa = meaning (Formers.instantiate B a) X env
        env₁ = ext βa env
        sA = Generic.Premises.shape-stable P
        cA = Generic.Premises.shape-code P
        sB = Generic.Premises.position-stable P
        cB = Generic.Premises.position-code P
        sM = Generic.Premises.motive-stable P
        cM = Generic.Premises.motive-code P
        sc = Generic.Premises.method-stable P
        tc = Generic.Premises.method-typed P
        cw = tree-type m k α β cA cB
        eβa = instantiate-at m B a X α env sB sa ta cA
        cβa = transport (Code R k) (eβa ⁻¹) (instance-code m k α a′ β ta cA cB)
        tfa = tf ∙ ap (λ u → pi k (m ⊔ℕ k) u (w [ p ])) (eβa ⁻¹)
        ch = meaning (Block.child m k A B a f) (X ▸ βa) env₁
        sch = child-stable m k A B a f X env sA cA sB cB sa ta sf tf
        tch = ap type-of
                  (child-value m k A B a f X env sA cA sB cB sa ta sf) ∙
                child-type m k βa w f′ cβa cw tfa
        b₀ = β [ id ⨾ a′ ]
        cb₀ = instance-code m k α a′ β ta cA cB
        chd = application k (m ⊔ℕ k) (b₀ [ p ]) (w [ p ] [ p ]) (f′ [ p ])
                (q b₀)
        tchd = child-type m k b₀ w f′ cb₀ cw tf
        cF = pi-type k (m ⊔ℕ k) β (w [ p ] [ p ]) cB
               (code-[] R (m ⊔ℕ k) (w [ p ]) p (code-[] R (m ⊔ℕ k) w p cw))
        cH = hypotheses-code m k l α β w N cB cw cM
        ρ₂ = extend F (section R α a′ ta) f′ ef
        h′ = meaning (Block.hypotheses m k l A B M c a f) X env
        eh = hypotheses-type-at m k l A B M c a f X env P sa ta sf tf sH ef
        eext₃ = Environment.ext-extend R (k ⊔ℕ l) H (ext F (ext α env)) ρ₂ h′
                    eh cH ∙
                  ap (λ es → h′ ∷ es)
                    (ext-section₂ m (k ⊔ℕ (m ⊔ℕ k)) α F env a′ f′ ta cA ef cF)
    in induction-value m k l A B M c (Formers.supremum m k A B a f) X env ∙
         (ap (λ s′ → G [ id ⨾ s′ ]) (supremum-value m k A B a f X env) ∙
           (generic-supremum m k l α β N c₀ a′ f′ cA cB cM tc ta tf ef ∙
             (ap (λ h → c₀ [ ρ₂ ⨾ h ])
                 (hypotheses-value-at m k l A B M c a f X env P sa ta sf
                     tf ⁻¹) ∙
               ([⨾] H c₀ ρ₂ h′ eh ∙
                 (sc X (extend H ρ₂ h′ eh) ⁻¹ ∙
                   (ap (meaning c X) eext₃ ∙
                     instantiate₃-value c a f
                         (Block.hypotheses m k l A B M c a f) X env sa sf
                         (hypotheses-stable m k l A B M c a f X env P sa ta sf
                           tf) ⁻¹))))))

  -- The method's instance at a, f and the hypotheses is stable.
  instance₃-stable :
    {n : ℕ} (m k l : ℕ) (A : Raw.Expression C n)
    (B M : Raw.Expression C (suc n))
    (c : Raw.Expression C (suc (suc (suc n)))) (a f : Raw.Expression C n)
    (X : Ob) (env : Vec (Tm X) n) → Premises m k l A B M c X env
    → Stable (meaning a) X env
    → (ta : type-of (meaning a X env) ＝ meaning A X env)
    → Stable (meaning f) X env
    → let α = meaning A X env
          β = meaning B (X ▸ α) (ext α env)
          w = tree m k α β
          N = meaning M (X ▸ w) (ext w env)
          F = children-type R products m k α β w
      in type-of (meaning f X env)
         ＝ pi k (m ⊔ℕ k) (β [ id ⨾ meaning a X env ]) (tree m k α β [ p ])
         → Stable
             (meaning
               (Formers.pi k l (Formers.weaken B)
                 (Formers.instantiate-past 3 M
                   (Formers.application k (m ⊔ℕ k)
                     (Formers.weaken (Formers.weaken B))
                     (Formers.weaken
                       (Formers.weaken
                         (Formers.weaken
                           (Formers.weaken (Formers.tree m k A B)))))
                     (Tree.hole (fsuc fzero)) (Tree.hole fzero)))))
             (X ▸ α ▸ F) (ext F (ext α env))
         → (ef : type-of (meaning f X env)
                 ＝ F [ section R α (meaning a X env) ta ])
         → Stable
             (meaning
               (Formers.instantiate₃ c a f
                 (Block.hypotheses m k l A B M c a f)))
             X env
  instance₃-stable {n} m k l A B M c a f X env P sa ta sf tf sH ef =
    let α = meaning A X env
        β = meaning B (X ▸ α) (ext α env)
        w = tree m k α β
        N = meaning M (X ▸ w) (ext w env)
        F = children-type R products m k α β w
        H = hypotheses-type R products m k l α β w N
        c₀ = meaning c (X ▸ α ▸ F ▸ H) (ext H (ext F (ext α env)))
        G = tree-induction m k l α β N c₀
        a′ = meaning a X env
        f′ = meaning f X env
        βa = meaning (Formers.instantiate B a) X env
        env₁ = ext βa env
        sA = Generic.Premises.shape-stable P
        cA = Generic.Premises.shape-code P
        sB = Generic.Premises.position-stable P
        cB = Generic.Premises.position-code P
        sM = Generic.Premises.motive-stable P
        cM = Generic.Premises.motive-code P
        sc = Generic.Premises.method-stable P
        tc = Generic.Premises.method-typed P
        cw = tree-type m k α β cA cB
        eβa = instantiate-at m B a X α env sB sa ta cA
        cβa = transport (Code R k) (eβa ⁻¹) (instance-code m k α a′ β ta cA cB)
        tfa = tf ∙ ap (λ u → pi k (m ⊔ℕ k) u (w [ p ])) (eβa ⁻¹)
        ch = meaning (Block.child m k A B a f) (X ▸ βa) env₁
        sch = child-stable m k A B a f X env sA cA sB cB sa ta sf tf
        tch = ap type-of
                  (child-value m k A B a f X env sA cA sB cB sa ta sf) ∙
                child-type m k βa w f′ cβa cw tfa
        b₀ = β [ id ⨾ a′ ]
        cb₀ = instance-code m k α a′ β ta cA cB
        chd = application k (m ⊔ℕ k) (b₀ [ p ]) (w [ p ] [ p ]) (f′ [ p ])
                (q b₀)
        tchd = child-type m k b₀ w f′ cb₀ cw tf
        cF = pi-type k (m ⊔ℕ k) β (w [ p ] [ p ]) cB
               (code-[] R (m ⊔ℕ k) (w [ p ]) p (code-[] R (m ⊔ℕ k) w p cw))
        cH = hypotheses-code m k l α β w N cB cw cM
        ρ₂ = extend F (section R α a′ ta) f′ ef
        h′ = meaning (Block.hypotheses m k l A B M c a f) X env
        eh = hypotheses-type-at m k l A B M c a f X env P sa ta sf tf sH ef
        eext₃ = Environment.ext-extend R (k ⊔ℕ l) H (ext F (ext α env)) ρ₂ h′
                    eh cH ∙
                  ap (λ es → h′ ∷ es)
                    (ext-section₂ m (k ⊔ℕ (m ⊔ℕ k)) α F env a′ f′ ta cA ef cF)
        hy = Block.hypotheses m k l A B M c a f
        σ₁ = Formers.extended (λ (i : Fin n) → Tree.hole i) a
        σ₂ = Formers.extended σ₁ f
    in substitute-stable (Formers.extended σ₂ hy) c X env
         (extended-stable σ₂ hy X env
           (extended-stable σ₁ f X env
             (extended-stable (λ (i : Fin n) → Tree.hole i) a X env
               (λ i → Environment.stable-lookup R i X env) sa)
             sf)
           (hypotheses-stable m k l A B M c a f X env P sa ta sf tf))
         (transport (Stable (meaning c) X)
           (ap (λ es → h′ ∷ f′ ∷ a′ ∷ es) (tabulate-lookup env ⁻¹))
           (transport (Stable (meaning c) X) eext₃
             (Environment.stable-[] R (meaning c) (X ▸ α ▸ F ▸ H)
               (ext H (ext F (ext α env))) sc (extend H ρ₂ h′ eh))))

