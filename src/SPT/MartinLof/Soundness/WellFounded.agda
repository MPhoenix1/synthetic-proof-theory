{-# OPTIONS --safe --without-K --no-projection-like #-}

module SPT.MartinLof.Soundness.WellFounded where

-- Soundness of the rules of W-types (`sound`), from WellFounded/: W A B
-- and sup are typed by their typing laws (Trees), induction through the
-- premises of the model's induction (Induction: `premises`,
-- `induction-typed`), and induction at sup a f computes to the method's
-- instance at the induction hypotheses (Computation). In the congruences
-- the primed side is typed at its own data and retyped along the equal
-- values: the children's type of sup (`children-equal`), and for
-- induction the premises carried to the equal data (Induction's
-- `premises-equal`) and the generic term moved along the equal values of
-- its data (`induction-equal`, from `induction-moved`). A type weakened
-- past a variable is a type (`weakened-type`). The premises at the method
-- context are read at the model's method context written out
-- (`extended-stable`, `extended-typed`, `extended-equal`).

open import SPT.Base hiding (Lift; _∘_; id; lift; lower; zero)
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Tree as Tree
import SPT.MartinLof.Formers as Formers
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Judgment using (Context; _▸[_]_; Judgment)
import SPT.MartinLof.Rules.WellFounded as Block
open import SPT.MartinLof.Model.Empty using (Empty)
open import SPT.MartinLof.Model.Identity using (Identity)
open import SPT.MartinLof.Model.Lift using (Lift)
open import SPT.MartinLof.Model.Natural using (Natural)
open import SPT.MartinLof.Model.Subuniverse using
  (Operations; Subuniverse)
open import SPT.MartinLof.Model.Pi using (Pi)
open import SPT.MartinLof.Model.Russell using
  (Russell; Code; code-[]; closed-code)
open import SPT.MartinLof.Model.Sigma using (Sigma)
open import SPT.MartinLof.Model.Sum using (Sum)
open import SPT.MartinLof.Model.Unit using (Unit)
open import SPT.MartinLof.Model.WellFounded using
  (WellFounded; children-type; hypotheses-type)
import SPT.MartinLof.Soundness.Environment as Environment
import SPT.MartinLof.Soundness.Instances as Instances
import SPT.MartinLof.Soundness.Interpretation as Interpretation
import SPT.MartinLof.Soundness.Pi as Products
import SPT.MartinLof.Soundness.Typing as Typing
import SPT.MartinLof.Soundness.WellFounded.Computation as Computation
import SPT.MartinLof.Soundness.WellFounded.Induction as Induction
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
  (let weaken-at = Instances.weaken-at R lifting products pairs paths trees
                     nothing one sums numbers operations subuniverses constant)
  (let weaken-stable = Instances.weaken-stable R lifting products pairs paths
                         trees nothing one sums numbers operations subuniverses
                           constant)
  (let closed-stable = Typing.closed-stable R lifting products pairs paths
                         trees nothing one sums numbers operations subuniverses
                           constant)
  (let retype = Typing.retype R lifting products pairs paths trees nothing
                  one sums numbers operations subuniverses constant)
  (let typed-along = Typing.typed-along R lifting products pairs paths trees
                       nothing one sums numbers operations subuniverses
                         constant)
  (let as-type = Typing.as-type R lifting products pairs paths trees nothing
                   one sums numbers operations subuniverses constant)
  (let instance-as-type = Typing.instance-as-type R lifting products pairs
                            paths trees nothing one sums numbers
                            operations subuniverses constant)
  (let instantiate-equal = Typing.instantiate-equal R lifting products pairs
                             paths trees nothing one sums numbers
                             operations subuniverses constant)
  (let pi-typed = Products.pi-typed R lifting products pairs paths trees
                    nothing one sums numbers operations subuniverses constant)
  (let tree-value = Trees.tree-value R lifting products pairs paths trees
                      nothing one sums numbers operations subuniverses constant)
  (let supremum-value = Trees.supremum-value R lifting products pairs paths
                          trees nothing one sums numbers operations
                            subuniverses constant)
  (let induction-value = Trees.induction-value R lifting products pairs
                           paths trees nothing one sums numbers
                           operations subuniverses constant)
  (let tree-typed = Trees.tree-typed R lifting products pairs paths trees
                      nothing one sums numbers operations subuniverses constant)
  (let supremum-typed = Trees.supremum-typed R lifting products pairs paths
                          trees nothing one sums numbers operations
                            subuniverses constant)
  (let children-at = Trees.children-at R lifting products pairs paths trees
                       nothing one sums numbers operations subuniverses
                         constant)
  (let children-model = Induction.children-model R lifting products pairs
                          paths trees nothing one sums numbers
                          operations subuniverses constant)
  (let hypotheses-model = Induction.hypotheses-model R lifting products pairs
                            paths trees nothing one sums numbers
                            operations subuniverses constant)
  (let premises = Induction.premises R lifting products pairs paths trees
                    nothing one sums numbers operations subuniverses constant)
  (let premises-equal = Induction.premises-equal R lifting products pairs
                          paths trees nothing one sums numbers
                          operations subuniverses constant)
  (let induction-typed = Induction.induction-typed R lifting products pairs
                           paths trees nothing one sums numbers
                           operations subuniverses constant)
  (let children-section = Computation.children-section R lifting products
                            pairs paths trees nothing one sums numbers
                            operations subuniverses constant)
  (let computation-value = Computation.computation-value R lifting products
                             pairs paths trees nothing one sums numbers
                             operations subuniverses constant)
  (let instance₃-stable = Computation.instance₃-stable R lifting products
                            pairs paths trees nothing one sums numbers
                            operations subuniverses constant)
  (let type-stable = Interpretation.Typed.type-stable)
  (let type-code = Interpretation.Typed.type-code)
  (let term-stable = Interpretation.Typed.term-stable)
  (let term-type = Interpretation.Typed.term-type)
  where

  ----------------------------------------------------------------------
  -- Equal data

  -- A type weakened past a variable of type b is a type.
  weakened-type :
    {n : ℕ} (l : ℕ) (T : Raw.Expression C n) (X : Ob) (env : Vec (Tm X) n)
    (b : Tm X)
    → Typed X env (suc l) T (Formers.universe l)
    → Typed (X ▸ b) (ext b env) (suc l) (Formers.weaken T)
        (Formers.universe l)
  weakened-type l T X env b TT = record
    { type-stable = closed-stable (universe l) (X ▸ b) (ext b env)
    ; type-code =
        closed-code R (suc l) (universe l) (ε (X ▸ b)) (universe-type l)
    ; term-stable = weaken-stable T X b env (term-stable TT)
    ; term-type =
        ap type-of (weaken-at T X b env (term-stable TT)) ∙
          (type-of-[] (meaning T X env) p ∙
            (ap (λ s → s [ p ]) (term-type TT) ∙
              closed-stable (universe l) X env (X ▸ b) p ⁻¹))
    }

  tree-equal :
    {n : ℕ} (m k : ℕ) (A A′ : Raw.Expression C n)
    (B B′ : Raw.Expression C (suc n)) (X : Ob) (env : Vec (Tm X) n)
    → meaning A X env ＝ meaning A′ X env
    → meaning B (X ▸ meaning A X env) (ext (meaning A X env) env)
      ＝ meaning B′ (X ▸ meaning A X env) (ext (meaning A X env) env)
    → meaning (Formers.tree m k A B) X env
      ＝ meaning (Formers.tree m k A′ B′) X env
  tree-equal m k A A′ B B′ X env eA eB =
    tree-value m k A B X env ∙
      (ap (tree m k (meaning A X env)) eB ∙
        (ap (λ x → tree m k x (meaning B′ (X ▸ x) (ext x env))) eA ∙
          tree-value m k A′ B′ X env ⁻¹))

  -- The children's types B a → W A B at equal data.
  children-equal :
    {n : ℕ} (m k : ℕ) (A A′ : Raw.Expression C n)
    (B B′ : Raw.Expression C (suc n)) (a a′ : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Typed X env (suc m) A (Formers.universe m)
    → Typed (X ▸ meaning A X env) (ext (meaning A X env) env) (suc k) B
        (Formers.universe k)
    → Typed X env m a A
    → Typed X env (suc m) A′ (Formers.universe m)
    → Typed (X ▸ meaning A′ X env) (ext (meaning A′ X env) env) (suc k) B′
        (Formers.universe k)
    → Typed X env m a′ A′
    → meaning A X env ＝ meaning A′ X env
    → meaning B (X ▸ meaning A X env) (ext (meaning A X env) env)
      ＝ meaning B′ (X ▸ meaning A X env) (ext (meaning A X env) env)
    → meaning a X env ＝ meaning a′ X env
    → meaning
        (Formers.pi k (m ⊔ℕ k) (Formers.instantiate B a)
          (Formers.weaken (Formers.tree m k A B)))
        X env
      ＝ meaning
          (Formers.pi k (m ⊔ℕ k) (Formers.instantiate B′ a′)
            (Formers.weaken (Formers.tree m k A′ B′)))
          X env
  children-equal m k A A′ B B′ a a′ X env TA TB Ta TA′ TB′ Ta′ eA eB ea =
    let α = meaning A X env
    in children-at m k A B a X env (term-stable TA) (term-type TA)
           (term-stable TB) (term-type TB) (term-stable Ta) (term-type Ta) ∙
         (ap (λ b → pi k (m ⊔ℕ k) (b [ id ⨾ meaning a X env ])
                          (tree m k α b [ p ]))
             eB ∙
           (ap₂
               (λ x y → pi k (m ⊔ℕ k)
                  (meaning B′ (X ▸ x) (ext x env) [ id ⨾ y ])
                  (tree m k x (meaning B′ (X ▸ x) (ext x env)) [ p ]))
               eA ea ∙
             children-at m k A′ B′ a′ X env (term-stable TA′)
                 (term-type TA′) (term-stable TB′) (term-type TB′)
                 (term-stable Ta′) (term-type Ta′) ⁻¹))

  -- Induction at equal shape, position and motive types, at a fixed method
  -- and argument; at variables, by the equation's refl.
  induction-moved :
    {n : ℕ} (m k l : ℕ) (c : Raw.Expression C (suc (suc (suc n)))) (X : Ob)
    (env : Vec (Tm X) n) (u : Tm X) (α : Tm X) (β : Tm (X ▸ α))
    (N : Tm (X ▸ tree m k α β)) (α′ : Tm X) (β′ : Tm (X ▸ α′))
    (N′ : Tm (X ▸ tree m k α′ β′))
    → _＝_ {A = Σ (Tm X) (λ x → Σ (Tm (X ▸ x)) (λ b → Tm (X ▸ tree m k x b)))}
        (α , β , N) (α′ , β′ , N′)
    → let F = children-type R products m k α β (tree m k α β)
          H = hypotheses-type R products m k l α β (tree m k α β) N
          F′ = children-type R products m k α′ β′ (tree m k α′ β′)
          H′ = hypotheses-type R products m k l α′ β′ (tree m k α′ β′) N′
      in tree-induction m k l α β N
           (meaning c (X ▸ α ▸ F ▸ H) (ext H (ext F (ext α env))))
           [ id ⨾ u ]
         ＝ tree-induction m k l α′ β′ N′
             (meaning c (X ▸ α′ ▸ F′ ▸ H′) (ext H′ (ext F′ (ext α′ env))))
             [ id ⨾ u ]
  induction-moved m k l c X env u α β N .α .β .N refl = refl

  -- The values of induction at equal data, the methods equal at the
  -- model's method context.
  induction-equal :
    {n : ℕ} (m k l : ℕ) (A A′ : Raw.Expression C n)
    (B B′ M M′ : Raw.Expression C (suc n))
    (c c′ : Raw.Expression C (suc (suc (suc n))))
    (t t′ : Raw.Expression C n) (X : Ob) (env : Vec (Tm X) n)
    → let α = meaning A X env
          β = meaning B (X ▸ α) (ext α env)
          w = tree m k α β
          N = meaning M (X ▸ w) (ext w env)
          F = children-type R products m k α β w
          H = hypotheses-type R products m k l α β w N
      in meaning A X env ＝ meaning A′ X env
         → β ＝ meaning B′ (X ▸ α) (ext α env)
         → N ＝ meaning M′ (X ▸ w) (ext w env)
         → meaning c (X ▸ α ▸ F ▸ H) (ext H (ext F (ext α env)))
           ＝ meaning c′ (X ▸ α ▸ F ▸ H) (ext H (ext F (ext α env)))
         → meaning t X env ＝ meaning t′ X env
         → meaning (Formers.tree-induction m k l A B M c t) X env
           ＝ meaning (Formers.tree-induction m k l A′ B′ M′ c′ t′) X env
  induction-equal m k l A A′ B B′ M M′ c c′ t t′ X env eA eB eM ec et =
    let α = meaning A X env
        β = meaning B (X ▸ α) (ext α env)
        w = tree m k α β
        N = meaning M (X ▸ w) (ext w env)
        F = children-type R products m k α β w
        H = hypotheses-type R products m k l α β w N
        α′ = meaning A′ X env
        β′ = meaning B′ (X ▸ α′) (ext α′ env)
        w′ = tree m k α′ β′
        u′ = meaning t′ X env
        eq : _＝_
               {A = Σ (Tm X)
                      (λ x → Σ (Tm (X ▸ x)) (λ b → Tm (X ▸ tree m k x b)))}
               (α , β , N) (α′ , β′ , meaning M′ (X ▸ w′) (ext w′ env))
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
    in induction-value m k l A B M c t X env ∙
         (ap₂ (λ d u → tree-induction m k l α β N d [ id ⨾ u ]) ec et ∙
           (induction-moved m k l c′ X env u′ α β N α′ β′
               (meaning M′ (X ▸ w′) (ext w′ env)) eq ∙
             induction-value m k l A′ B′ M′ c′ t′ X env ⁻¹))

  ----------------------------------------------------------------------
  -- The method context

  -- The model context and the values of Γ extended by A, F and H are the
  -- model's extensions by their values. The premises at the method
  -- context carry it folded, and the lemmas of WellFounded/ carry it
  -- written out. Stated at variable types F and H, the two spellings meet
  -- where the values of F and H are stuck, and the instances at the
  -- method context agree literally.
  extended-stable :
    {n : ℕ} (Γ : Context C n) (a b : ℕ) (A : Raw.Expression C n)
    (F : Raw.Expression C (suc n)) (H : Raw.Expression C (suc (suc n)))
    → let X = object Γ
          env = values Γ
          α = meaning A X env
          Fs = meaning F (X ▸ α) (ext α env)
      in Stable (meaning H) (object (Γ ▸[ a ] A ▸[ b ] F))
           (values (Γ ▸[ a ] A ▸[ b ] F))
         → Stable (meaning H) (X ▸ α ▸ Fs) (ext Fs (ext α env))
  extended-stable Γ a b A F H sH = sH

  extended-typed :
    {n : ℕ} (Γ : Context C n) (a b d l : ℕ) (A : Raw.Expression C n)
    (F : Raw.Expression C (suc n)) (H : Raw.Expression C (suc (suc n)))
    (c T : Raw.Expression C (suc (suc (suc n))))
    → let X = object Γ
          env = values Γ
          α = meaning A X env
          Fs = meaning F (X ▸ α) (ext α env)
          Hs = meaning H (X ▸ α ▸ Fs) (ext Fs (ext α env))
      in Typed (object (Γ ▸[ a ] A ▸[ b ] F ▸[ d ] H))
           (values (Γ ▸[ a ] A ▸[ b ] F ▸[ d ] H)) l c T
         → Typed (X ▸ α ▸ Fs ▸ Hs) (ext Hs (ext Fs (ext α env))) l c T
  extended-typed Γ a b d l A F H c T Tc = Tc

  extended-equal :
    {n : ℕ} (Γ : Context C n) (a b d : ℕ) (A : Raw.Expression C n)
    (F : Raw.Expression C (suc n)) (H : Raw.Expression C (suc (suc n)))
    (c c′ : Raw.Expression C (suc (suc (suc n))))
    → let X = object Γ
          env = values Γ
          α = meaning A X env
          Fs = meaning F (X ▸ α) (ext α env)
          Hs = meaning H (X ▸ α ▸ Fs) (ext Fs (ext α env))
          Δ = Γ ▸[ a ] A ▸[ b ] F ▸[ d ] H
      in meaning c (object Δ) (values Δ) ＝ meaning c′ (object Δ) (values Δ)
         → meaning c (X ▸ α ▸ Fs ▸ Hs) (ext Hs (ext Fs (ext α env)))
           ＝ meaning c′ (X ▸ α ▸ Fs ▸ Hs) (ext Hs (ext Fs (ext α env)))
  extended-equal Γ a b d A F H c c′ ec = ec

  ----------------------------------------------------------------------
  -- The rules of W-types

  sound :
    {j : Judgment C} (r : Block.Rule C j)
    → ((i : Fin (length (Block.premises r)))
       → Valid (list-lookup (Block.premises r) i))
    → Valid j
  sound (Block.formation Γ m k A B) h =
    let (vΓ , TA) = h fzero
        (_ , TB) = h (fsuc fzero)
    in vΓ , tree-typed m k A B (object Γ) (values Γ) TA TB
  sound (Block.introduction Γ m k A B a f) h =
    let (vΓ , TA) = h fzero
        (_ , TB) = h (fsuc fzero)
        (_ , Ta) = h (fsuc (fsuc fzero))
        (_ , Tf) = h (fsuc (fsuc (fsuc fzero)))
    in vΓ , supremum-typed m k A B a f (object Γ) (values Γ) TA TB Ta Tf
  sound (Block.elimination Γ m k l A B M c t) h =
    let (vΓ , TA) = h fzero
        (_ , TB) = h (fsuc fzero)
        (_ , TM) = h (fsuc (fsuc fzero))
        (_ , Tc) = h (fsuc (fsuc (fsuc fzero)))
        (_ , Tt) = h (fsuc (fsuc (fsuc (fsuc fzero))))
        X = object Γ
        env = values Γ
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
        P = premises m k l A B M c X env TA TB TM
              (extended-typed Γ m (k ⊔ℕ (m ⊔ℕ k)) (k ⊔ℕ l) l A F′ H′ c
                (Block.method-type m k A B M) Tc)
    in vΓ , induction-typed m k l A B M c t X env P TM Tt
  sound (Block.computation Γ m k l A B M c a f) h =
    let (vΓ , TA) = h fzero
        (_ , TB) = h (fsuc fzero)
        (_ , TM) = h (fsuc (fsuc fzero))
        (((_ , sF , cF) , sH , cH) , Tc) =
          h (fsuc (fsuc (fsuc fzero)))
        (_ , Ta) = h (fsuc (fsuc (fsuc (fsuc fzero))))
        (_ , Tf) =
          h (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))
        X = object Γ
        env = values Γ
        α = meaning A X env
        β = meaning B (X ▸ α) (ext α env)
        sA = term-stable TA
        cA = term-type TA
        sB = term-stable TB
        cB = term-type TB
        sa = term-stable Ta
        ta = term-type Ta
        sf = term-stable Tf
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
        P = premises m k l A B M c X env TA TB TM
              (extended-typed Γ m (k ⊔ℕ (m ⊔ℕ k)) (k ⊔ℕ l) l A F′ H′ c
                (Block.method-type m k A B M) Tc)
        sH′ = transport
                (λ G → Stable (meaning H′) (X ▸ α ▸ G) (ext G (ext α env)))
                (children-model m k A B X env sA cA sB cB)
                (extended-stable Γ m (k ⊔ℕ (m ⊔ℕ k)) A F′ H′ sH)
        tf = term-type Tf ∙
               children-at m k A B a X env sA cA sB cB sa ta
        ef = children-section m k α β (meaning a X env) (meaning f X env) cB
               (tree-type m k α β cA cB) ta tf
        TL = induction-typed m k l A B M c (Formers.supremum m k A B a f) X
               env P TM (supremum-typed m k A B a f X env TA TB Ta Tf)
        ev = computation-value m k l A B M c a f X env P sa ta sf tf sH′ ef
        sL = type-stable TL
        cL = type-code TL
        tL = term-type TL
        sI = instance₃-stable m k l A B M c a f X env P sa ta sf tf sH′ ef
        eI = ap type-of (ev ⁻¹) ∙ tL
    in vΓ
       , TL
       , record
           { type-stable = sL
           ; type-code = cL
           ; term-stable = sI
           ; term-type = eI
           }
       , ev
  sound (Block.formation-equal Γ m k A A′ B B′) h =
    let (vΓ , TA , TA′ , eA) = h fzero
        (_ , TB , TB′ , eB) = h (fsuc fzero)
        X = object Γ
        env = values Γ
    in vΓ
       , tree-typed m k A B X env TA TB
       , tree-typed m k A′ B′ X env TA′
           (typed-along X env (suc k) B′ (Formers.universe k) eA TB′)
       , tree-equal m k A A′ B B′ X env eA eB
  sound (Block.introduction-equal Γ m k A A′ B B′ a a′ f f′) h =
    let (vΓ , TA , TA′ , eA) = h fzero
        (_ , TB , TB′ , eB) = h (fsuc fzero)
        (_ , Ta , Ta′ , ea) = h (fsuc (fsuc fzero))
        (_ , Tf , Tf′ , ef) = h (fsuc (fsuc (fsuc fzero)))
        X = object Γ
        env = values Γ
        TB″ = typed-along X env (suc k) B′ (Formers.universe k) eA TB′
        sA′ = term-stable TA′
        cA′ = term-type TA′
        Ta″ = retype X env m a′ A′ A Ta′ sA′ cA′ eA
        TI′ = instance-as-type m k A′ B′ a′ X env TB″ Ta″
        TP′ = pi-typed k (m ⊔ℕ k) (Formers.instantiate B′ a′)
                (Formers.weaken (Formers.tree m k A′ B′)) X env TI′
                (weakened-type (m ⊔ℕ k) (Formers.tree m k A′ B′) X env
                  (meaning (Formers.instantiate B′ a′) X env)
                  (tree-typed m k A′ B′ X env TA′ TB″))
        sP′ = term-stable TP′
        cP′ = term-type TP′
        Tf″ = retype X env (k ⊔ℕ (m ⊔ℕ k)) f′
                (Formers.pi k (m ⊔ℕ k) (Formers.instantiate B′ a′)
                  (Formers.weaken (Formers.tree m k A′ B′)))
                (Formers.pi k (m ⊔ℕ k) (Formers.instantiate B a)
                  (Formers.weaken (Formers.tree m k A B)))
                Tf′ sP′ cP′
                (children-equal m k A A′ B B′ a a′ X env TA TB Ta TA′ TB″ Ta″
                  eA eB ea)
        TW = tree-typed m k A B X env TA TB
        sW = term-stable TW
        cW = term-type TW
        α = meaning A X env
    in vΓ
       , supremum-typed m k A B a f X env TA TB Ta Tf
       , retype X env (m ⊔ℕ k) (Formers.supremum m k A′ B′ a′ f′)
           (Formers.tree m k A B) (Formers.tree m k A′ B′)
           (supremum-typed m k A′ B′ a′ f′ X env TA′ TB″ Ta″ Tf″) sW cW
           (tree-equal m k A A′ B B′ X env eA eB ⁻¹)
       , supremum-value m k A B a f X env ∙
           (ap₂
               (λ b u → supremum m k α b u (meaning f X env)) eB ea ∙
             (ap (supremum m k α (meaning B′ (X ▸ α) (ext α env))
                        (meaning a′ X env))
                 ef ∙
               (ap
                   (λ x → supremum m k x (meaning B′ (X ▸ x) (ext x env))
                            (meaning a′ X env) (meaning f′ X env))
                   eA ∙
                 supremum-value m k A′ B′ a′ f′ X env ⁻¹)))
  sound (Block.elimination-equal Γ m k l A A′ B B′ M M′ c c′ t t′) h =
    let (vΓ , TA , TA′ , eA) = h fzero
        (_ , TB , TB′ , eB) = h (fsuc fzero)
        (_ , TM , TM′ , eM) = h (fsuc (fsuc fzero))
        (_ , Tc , Tc′ , ec) = h (fsuc (fsuc (fsuc fzero)))
        (_ , Tt , Tt′ , et) =
          h (fsuc (fsuc (fsuc (fsuc fzero))))
        X = object Γ
        env = values Γ
        α = meaning A X env
        β = meaning B (X ▸ α) (ext α env)
        w = tree m k α β
        T = Formers.tree m k A B
        T′ = Formers.tree m k A′ B′
        sA = term-stable TA
        cA = term-type TA
        sB = term-stable TB
        cB = term-type TB
        sA′ = term-stable TA′
        cA′ = term-type TA′
        ew = tree-value m k A B X env
        eT = tree-equal m k A A′ B B′ X env eA eB
        TB″ = typed-along X env (suc k) B′ (Formers.universe k) eA TB′
        sB″ = term-stable TB″
        cB″ = term-type TB″
        TW′ = tree-typed m k A′ B′ X env TA′ TB″
        sW′ = term-stable TW′
        cW′ = term-type TW′
        TM″ = typed-along X env (suc l) M′ (Formers.universe l) eT TM′
        sMT = term-stable TM
        sM″ = term-stable TM″
        cM″ = term-type TM″
        ew′ = tree-value m k A′ B′ X env
        sM′ = transport (λ v → Stable (meaning M′) (X ▸ v) (ext v env)) ew′ sM″
        cM′ = transport (λ v → Code R l (meaning M′ (X ▸ v) (ext v env))) ew′
                cM″
        eMw = transport
                (λ v → meaning M (X ▸ v) (ext v env)
                       ＝ meaning M′ (X ▸ v) (ext v env))
                ew eM
        sM = transport (λ v → Stable (meaning M) (X ▸ v) (ext v env)) ew sMT
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
        ec₁ = transport
                (λ G → meaning c
                         (X ▸ α ▸ G
                            ▸ meaning H′ (X ▸ α ▸ G) (ext G (ext α env)))
                         (ext (meaning H′ (X ▸ α ▸ G) (ext G (ext α env)))
                           (ext G (ext α env)))
                       ＝ meaning c′
                           (X ▸ α ▸ G
                              ▸ meaning H′ (X ▸ α ▸ G) (ext G (ext α env)))
                           (ext (meaning H′ (X ▸ α ▸ G) (ext G (ext α env)))
                             (ext G (ext α env))))
                (children-model m k A B X env sA cA sB cB)
                (extended-equal Γ m (k ⊔ℕ (m ⊔ℕ k)) (k ⊔ℕ l) A F′ H′ c c′ ec)
        ec₂ = transport
                (λ K → meaning c (X ▸ α ▸ F ▸ K) (ext K (ext F (ext α env)))
                       ＝ meaning c′ (X ▸ α ▸ F ▸ K)
                           (ext K (ext F (ext α env))))
                (hypotheses-model m k l A B M X env sA cA sB cB sM) ec₁
        P = premises m k l A B M c X env TA TB TM
              (extended-typed Γ m (k ⊔ℕ (m ⊔ℕ k)) (k ⊔ℕ l) l A F′ H′ c
                (Block.method-type m k A B M) Tc)
        P′ = premises-equal m k l A A′ B B′ M M′ c′ X env
               (premises m k l A B M c′ X env TA TB TM
                 (extended-typed Γ m (k ⊔ℕ (m ⊔ℕ k)) (k ⊔ℕ l) l A F′ H′ c′
                   (Block.method-type m k A B M) Tc′))
               sA′ cA′ sB″ cB″ sM′ cM′ eA eB eMw
        Tt″ = retype X env (m ⊔ℕ k) t′ T′ T Tt′ sW′ cW′ eT
        TL = induction-typed m k l A B M c t X env P TM Tt
        sL = type-stable TL
        cL = type-code TL
    in vΓ
       , TL
       , retype X env l (Formers.tree-induction m k l A′ B′ M′ c′ t′)
           (Formers.instantiate M t) (Formers.instantiate M′ t′)
           (induction-typed m k l A′ B′ M′ c′ t′ X env P′ TM″ Tt″) sL cL
           (instantiate-equal (m ⊔ℕ k) T T′ M M′ t t′ X env sMT sM″ Tt Tt″
               eT eM et ⁻¹)
       , induction-equal m k l A A′ B B′ M M′ c c′ t t′ X env eA eB eMw ec₂
           et
