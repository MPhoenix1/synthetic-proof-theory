{-# OPTIONS --safe --without-K --no-projection-like #-}

module SPT.MartinLof.Soundness.Identity where

-- Soundness of the rules of identity types (`sound`). Id and refl are the
-- model's operations at the values of their children; J's value reads
-- the motive at the extension by A and by the paths from the base point
-- (`J-value`). The paths from x, a type over the extension by A
-- (`paths-code`), are taken under a binder and at a section as the
-- model's laws ask (`paths-under`, `paths-at`); the syntactic paths of
-- the motive's context have their value (`paths-value`). Each former is
-- stable by its stability law (`identity-stable`, `reflexivity-stable`,
-- `J-stable`: the motive taken along the substitution under both
-- binders) and has its type by its typing law (`identity-typed`,
-- `reflexivity-typed`, `J-typed`). J at refl computes by the model's β.
-- In the congruence of J, motives equal at the extension are equal at its
-- instances (`equal₂-at`).

open import SPT.Base hiding (Lift; _∘_; id; lift; lower; zero)
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Tree as Tree
import SPT.MartinLof.Formers as Formers
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Judgment using (Judgment)
import SPT.MartinLof.Rules.Identity as Block
open import SPT.MartinLof.Model.Empty using (Empty)
open import SPT.MartinLof.Model.Identity using (Identity)
open import SPT.MartinLof.Model.Lift using (Lift)
open import SPT.MartinLof.Model.Natural using (Natural)
open import SPT.MartinLof.Model.Subuniverse using
  (Operations; Subuniverse)
open import SPT.MartinLof.Model.Pi using (Pi)
open import SPT.MartinLof.Model.Russell using
  (Russell; Code; code-[]; section; under)
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
  (let weaken-at = Instances.weaken-at R lifting products pairs paths trees
                     nothing one sums numbers operations subuniverses constant)
  (let instantiate₂-value = Instances.instantiate₂-value R lifting products
                              pairs paths trees nothing one sums numbers
                              operations subuniverses constant)
  (let as-type = Typing.as-type R lifting products pairs paths trees nothing
                   one sums numbers operations subuniverses constant)
  (let retype = Typing.retype R lifting products pairs paths trees nothing
                  one sums numbers operations subuniverses constant)
  (let typed-along = Typing.typed-along R lifting products pairs paths trees
                       nothing one sums numbers operations subuniverses
                         constant)
  (let p-under = Typing.p-under R lifting products pairs paths trees nothing
                   one sums numbers operations subuniverses constant)
  (let q-under = Typing.q-under R lifting products pairs paths trees nothing
                   one sums numbers operations subuniverses constant)
  (let p-section = Typing.p-section R lifting products pairs paths trees
                     nothing one sums numbers operations subuniverses constant)
  (let q-section = Typing.q-section R lifting products pairs paths trees
                     nothing one sums numbers operations subuniverses constant)
  (let ⨾-code = Typing.⨾-code R lifting products pairs paths trees nothing
                  one sums numbers operations subuniverses constant)
  (let lift-stable = Typing.lift-stable R lifting products pairs paths trees
                       nothing one sums numbers operations subuniverses
                         constant)
  (let equal-[] = Typing.equal-[] R lifting products pairs paths trees
                    nothing one sums numbers operations subuniverses constant)
  (let ext-section₂ = Typing.ext-section₂ R lifting products pairs paths
                        trees nothing one sums numbers operations subuniverses
                          constant)
  (let instantiate₂-at = Typing.instantiate₂-at R lifting products pairs
                           paths trees nothing one sums numbers
                           operations subuniverses constant)
  (let instantiate₂-stable = Typing.instantiate₂-stable R lifting products
                               pairs paths trees nothing one sums numbers
                               operations subuniverses constant)
  (let type-stable = Interpretation.Typed.type-stable)
  (let type-code = Interpretation.Typed.type-code)
  (let term-stable = Interpretation.Typed.term-stable)
  (let term-type = Interpretation.Typed.term-type)
  where

  ----------------------------------------------------------------------
  -- The paths from a point

  paths-code :
    {X : Ob} (m : ℕ) (a x : Tm X) → Code R m a → type-of x ＝ a
    → Code R m (identity m (a [ p ]) (x [ p ]) (q a))
  paths-code m a x ta tx =
    identity-type m (a [ p ]) (x [ p ]) (q a) (code-[] R m a p ta)
      (type-of-[] x p ∙ ap (λ s → s [ p ]) tx) (q-type m a ta)

  paths-under :
    {X Y : Ob} (m : ℕ) (a x : Tm X) (τ : Hom Y X) (ta : Code R m a)
    → type-of x ＝ a
    → identity m (a [ p ]) (x [ p ]) (q a) [ under R m a τ ta ]
      ＝ identity m (a [ τ ] [ p ]) (x [ τ ] [ p ]) (q (a [ τ ]))
  paths-under m a x τ ta tx =
    identity-[] m (a [ p ]) (x [ p ]) (q a) (under R m a τ ta)
        (code-[] R m a p ta) (type-of-[] x p ∙ ap (λ s → s [ p ]) tx)
        (q-type m a ta) ∙
      ap₃ (identity m) (p-under m a a τ ta) (p-under m a x τ ta)
        (q-under m a τ ta)

  paths-at :
    {X : Ob} (m : ℕ) (a x y : Tm X) → Code R m a → type-of x ＝ a
    → (ty : type-of y ＝ a)
    → identity m (a [ p ]) (x [ p ]) (q a) [ section R a y ty ]
      ＝ identity m a x y
  paths-at m a x y ta tx ty =
    identity-[] m (a [ p ]) (x [ p ]) (q a) (section R a y ty)
        (code-[] R m a p ta) (type-of-[] x p ∙ ap (λ s → s [ p ]) tx)
        (q-type m a ta) ∙
      ap₃ (identity m) (p-section a a y ty) (p-section a x y ty)
        (q-section m a y ty ta)

  -- The paths of the motive's context, from the base point a.
  paths-value :
    {n : ℕ} (m : ℕ) (A a : Raw.Expression C n) (X : Ob) (env : Vec (Tm X) n)
    → Stable (meaning A) X env → Stable (meaning a) X env
    → meaning
        (Formers.identity m (Formers.weaken A) (Formers.weaken a)
          (Tree.hole fzero))
        (X ▸ meaning A X env) (ext (meaning A X env) env)
      ＝ identity m (meaning A X env [ p ]) (meaning a X env [ p ])
          (q (meaning A X env))
  paths-value m A a X env sA sa =
    ap₂ (λ u v → identity m u v (q (meaning A X env)))
      (weaken-at A X (meaning A X env) env sA)
      (weaken-at a X (meaning A X env) env sa)

  ----------------------------------------------------------------------
  -- Values and stability

  J-value :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (M : Raw.Expression C (suc (suc n))) (a d b w : Raw.Expression C n)
    (X : Ob) (env : Vec (Tm X) n)
    → meaning (Formers.path-induction m k A M a d b w) X env
      ＝ path-induction m k (meaning A X env) (meaning a X env)
          (meaning M
            (X ▸ meaning A X env
               ▸ identity m (meaning A X env [ p ]) (meaning a X env [ p ])
                   (q (meaning A X env)))
            (ext
              (identity m (meaning A X env [ p ]) (meaning a X env [ p ])
                (q (meaning A X env)))
              (ext (meaning A X env) env)))
          (meaning d X env) (meaning b X env) (meaning w X env)
  J-value m k A M a d b w X env =
    let α = meaning A X env
        I = identity m (α [ p ]) (meaning a X env [ p ]) (q α)
    in ap
         (λ c → path-induction m k α (meaning a X env) c (meaning d X env)
                  (meaning b X env) (meaning w X env))
         (bound-meaning 2 M (X ▸ α ▸ I) (ext I (ext α env)))

  identity-stable :
    {n : ℕ} (m : ℕ) (A a b : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Stable (meaning A) X env → Code R m (meaning A X env)
    → Stable (meaning a) X env → type-of (meaning a X env) ＝ meaning A X env
    → Stable (meaning b) X env → type-of (meaning b X env) ＝ meaning A X env
    → Stable (meaning (Formers.identity m A a b)) X env
  identity-stable m A a b X env sA cA sa ta sb tb Y τ =
    ap₃ (identity m) (sA Y τ) (sa Y τ) (sb Y τ) ∙
      identity-[] m (meaning A X env) (meaning a X env) (meaning b X env)
          τ cA ta tb ⁻¹

  reflexivity-stable :
    {n : ℕ} (m : ℕ) (A a : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Stable (meaning A) X env → Code R m (meaning A X env)
    → Stable (meaning a) X env → type-of (meaning a X env) ＝ meaning A X env
    → Stable (meaning (Formers.reflexivity m A a)) X env
  reflexivity-stable m A a X env sA cA sa ta Y τ =
    ap₂ (reflexivity m) (sA Y τ) (sa Y τ) ∙
      reflexivity-[] m (meaning A X env) (meaning a X env) τ cA ta ⁻¹

  J-stable :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (M : Raw.Expression C (suc (suc n))) (a d b w : Raw.Expression C n)
    (X : Ob) (env : Vec (Tm X) n)
    → Stable (meaning A) X env → (cA : Code R m (meaning A X env))
    → Stable (meaning a) X env
    → (ta : type-of (meaning a X env) ＝ meaning A X env)
    → Stable (meaning M)
        (X ▸ meaning A X env
           ▸ identity m (meaning A X env [ p ]) (meaning a X env [ p ])
               (q (meaning A X env)))
        (ext
          (identity m (meaning A X env [ p ]) (meaning a X env [ p ])
            (q (meaning A X env)))
          (ext (meaning A X env) env))
    → Code R k
        (meaning M
          (X ▸ meaning A X env
             ▸ identity m (meaning A X env [ p ]) (meaning a X env [ p ])
                 (q (meaning A X env)))
          (ext
            (identity m (meaning A X env [ p ]) (meaning a X env [ p ])
              (q (meaning A X env)))
            (ext (meaning A X env) env)))
    → Stable (meaning d) X env
    → type-of (meaning d X env)
      ＝ meaning M
          (X ▸ meaning A X env
             ▸ identity m (meaning A X env [ p ]) (meaning a X env [ p ])
                 (q (meaning A X env)))
          (ext
            (identity m (meaning A X env [ p ]) (meaning a X env [ p ])
              (q (meaning A X env)))
            (ext (meaning A X env) env))
          [ section R (meaning A X env) (meaning a X env) ta
          ⨾ reflexivity m (meaning A X env) (meaning a X env) ]
    → Stable (meaning b) X env → type-of (meaning b X env) ＝ meaning A X env
    → Stable (meaning w) X env
    → type-of (meaning w X env)
      ＝ identity m (meaning A X env) (meaning a X env) (meaning b X env)
    → Stable (meaning (Formers.path-induction m k A M a d b w)) X env
  J-stable m k A M a d b w X env sA cA sa ta sM cM sd td sb tb sw tw Y τ =
    let α = meaning A X env
        x = meaning a X env
        I = identity m (α [ p ]) (x [ p ]) (q α)
        M₀ = meaning M (X ▸ α ▸ I) (ext I (ext α env))
        envτ = env [ τ ]ᵉ
        Iτ = identity m (α [ τ ] [ p ]) (x [ τ ] [ p ]) (q (α [ τ ]))
        eI = q-type m Iτ
                 (paths-code m (α [ τ ]) (x [ τ ]) (code-[] R m α τ cA)
                   (type-of-[] x τ ∙ ap (λ s → s [ τ ]) ta)) ∙
               (ap (λ s → s [ p ]) (paths-under m α x τ cA ta ⁻¹) ∙
                 [∘] I (under R m α τ cA) p ⁻¹)
    in J-value m k A M a d b w Y envτ ∙
         (ap₂
             (λ u v → path-induction m k u v
                (meaning M (Y ▸ u ▸ identity m (u [ p ]) (v [ p ]) (q u))
                  (ext (identity m (u [ p ]) (v [ p ]) (q u)) (ext u envτ)))
                (meaning d Y envτ) (meaning b Y envτ) (meaning w Y envτ))
             (sA Y τ) (sa Y τ) ∙
           (ap
               (λ c → path-induction m k (α [ τ ]) (x [ τ ]) c
                        (meaning d Y envτ) (meaning b Y envτ)
                        (meaning w Y envτ))
               (lift-stable (meaning M) m (X ▸ α) I (ext α env)
                 (paths-code m α x cA ta) sM (under R m α τ cA) Iτ
                 (ext (α [ τ ]) envτ) eI
                 (Environment.ext-under R m α env τ cA)) ∙
             (ap₃
                 (path-induction m k (α [ τ ]) (x [ τ ])
                   (M₀ [ under R m α τ cA ∘ p ⨾ q Iτ ]))
                 (sd Y τ) (sb Y τ) (sw Y τ) ∙
               (path-induction-[] m k α x M₀ (meaning d X env)
                     (meaning b X env) (meaning w X env) τ cA ta cM td tb tw ⁻¹
                       ∙
                 ap (λ s → s [ τ ])
                   (J-value m k A M a d b w X env ⁻¹)))))

  ----------------------------------------------------------------------
  -- Typing

  identity-typed :
    {n : ℕ} (m : ℕ) (A a b : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Typed X env (suc m) A (Formers.universe m) → Typed X env m a A
    → Typed X env m b A
    → Typed X env (suc m) (Formers.identity m A a b) (Formers.universe m)
  identity-typed m A a b X env TA Ta Tb =
    as-type X env m (Formers.identity m A a b)
      (identity-stable m A a b X env (term-stable TA) (term-type TA)
        (term-stable Ta) (term-type Ta) (term-stable Tb) (term-type Tb))
      (identity-type m (meaning A X env) (meaning a X env) (meaning b X env)
        (term-type TA) (term-type Ta) (term-type Tb))

  reflexivity-typed :
    {n : ℕ} (m : ℕ) (A a : Raw.Expression C n) (X : Ob) (env : Vec (Tm X) n)
    → Typed X env (suc m) A (Formers.universe m) → Typed X env m a A
    → Typed X env m (Formers.reflexivity m A a) (Formers.identity m A a a)
  reflexivity-typed m A a X env TA Ta =
    let T = identity-typed m A a a X env TA Ta Ta
    in record
      { type-stable = term-stable T
      ; type-code = term-type T
      ; term-stable =
          reflexivity-stable m A a X env (term-stable TA) (term-type TA)
            (term-stable Ta) (term-type Ta)
      ; term-type =
          reflexivity-type m (meaning A X env) (meaning a X env)
            (term-type TA) (term-type Ta)
      }

  -- J, with the method's type read at reflexivity and the base point.
  J-typed :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (M : Raw.Expression C (suc (suc n))) (a d b w : Raw.Expression C n)
    (X : Ob) (env : Vec (Tm X) n)
    → Typed X env (suc m) A (Formers.universe m) → Typed X env m a A
    → Typed
        (X ▸ meaning A X env
           ▸ identity m (meaning A X env [ p ]) (meaning a X env [ p ])
               (q (meaning A X env)))
        (ext
          (identity m (meaning A X env [ p ]) (meaning a X env [ p ])
            (q (meaning A X env)))
          (ext (meaning A X env) env))
        (suc k) M (Formers.universe k)
    → Stable (meaning d) X env
    → type-of (meaning d X env)
      ＝ meaning M X
          (reflexivity m (meaning A X env) (meaning a X env)
           ∷ meaning a X env ∷ env)
    → Typed X env m b A → Typed X env m w (Formers.identity m A a b)
    → Typed X env k (Formers.path-induction m k A M a d b w)
        (Formers.instantiate₂ M b w)
  J-typed m k A M a d b w X env TA Ta TM sd tdv Tb Tw =
    let α = meaning A X env
        x = meaning a X env
        y = meaning b X env
        I = identity m (α [ p ]) (x [ p ]) (q α)
        M₀ = meaning M (X ▸ α ▸ I) (ext I (ext α env))
        cA = term-type TA
        ta = term-type Ta
        tb = term-type Tb
        cI = paths-code m α x cA ta
        sr = reflexivity-stable m A a X env (term-stable TA) cA
               (term-stable Ta) ta
        tr = reflexivity-type m α x cA ta ∙
               paths-at m α x x cA ta ta ⁻¹
        td = tdv ∙
               (instantiate₂-value M a (Formers.reflexivity m A a) X env
                     (term-stable Ta) sr ⁻¹ ∙
                 instantiate₂-at m m M a (Formers.reflexivity m A a) X α I
                   env (term-stable TM) (term-stable Ta) sr ta cA tr cI)
        tw = term-type Tw ∙ paths-at m α x y cA ta tb ⁻¹
        e = instantiate₂-at m m M b w X α I env (term-stable TM)
              (term-stable Tb) (term-stable Tw) tb cA tw cI
    in record
      { type-stable =
          instantiate₂-stable m m M b w X α I env (term-stable TM)
            (term-stable Tb) (term-stable Tw) tb cA tw cI
      ; type-code =
          transport (Code R k) (e ⁻¹)
            (⨾-code k I M₀ (section R α y tb) (meaning w X env) tw
              (term-type TM))
      ; term-stable =
          J-stable m k A M a d b w X env (term-stable TA) cA (term-stable Ta)
            ta (term-stable TM) (term-type TM) sd td (term-stable Tb) tb
            (term-stable Tw) (term-type Tw)
      ; term-type =
          ap type-of (J-value m k A M a d b w X env) ∙
            (path-induction-type m k α x M₀ (meaning d X env) y
                (meaning w X env) cA ta (term-type TM) td tb (term-type Tw) ∙
              e ⁻¹)
      }

  -- Motives equal at the extension by a and b, at its instances.
  equal₂-at :
    {n : ℕ} (l m : ℕ) (M M′ : Raw.Expression C (suc (suc n))) (X : Ob)
    (a : Tm X) (b : Tm (X ▸ a)) (env : Vec (Tm X) n)
    → Stable (meaning M) (X ▸ a ▸ b) (ext b (ext a env))
    → Stable (meaning M′) (X ▸ a ▸ b) (ext b (ext a env))
    → meaning M (X ▸ a ▸ b) (ext b (ext a env))
      ＝ meaning M′ (X ▸ a ▸ b) (ext b (ext a env))
    → (x y : Tm X) (tx : type-of x ＝ a) → Code R l a
    → (ty : type-of y ＝ b [ section R a x tx ]) → Code R m b
    → meaning M X (y ∷ x ∷ env) ＝ meaning M′ X (y ∷ x ∷ env)
  equal₂-at l m M M′ X a b env sM sM′ eM x y tx ta ty tb =
    transport (λ es → meaning M X es ＝ meaning M′ X es)
      (ext-section₂ l m a b env x y tx ta ty tb)
      (equal-[] (meaning M) (meaning M′) (X ▸ a ▸ b) (ext b (ext a env)) sM
        sM′ eM (extend b (section R a x tx) y ty))

  ----------------------------------------------------------------------
  -- The rules of identity types

  sound :
    {j : Judgment C} (r : Block.Rule C j)
    → ((i : Fin (length (Block.premises r)))
       → Valid (list-lookup (Block.premises r) i))
    → Valid j
  sound (Block.formation Γ m A a b) h =
    let (vΓ , TA) = h fzero
        (_ , Ta) = h (fsuc fzero)
        (_ , Tb) = h (fsuc (fsuc fzero))
    in vΓ , identity-typed m A a b (object Γ) (values Γ) TA Ta Tb
  sound (Block.introduction Γ m A a) h =
    let (vΓ , TA) = h fzero
        (_ , Ta) = h (fsuc fzero)
    in vΓ , reflexivity-typed m A a (object Γ) (values Γ) TA Ta
  sound (Block.elimination Γ m k A M a d b w) h =
    let (vΓ , TA) = h fzero
        (_ , Ta) = h (fsuc fzero)
        (_ , TM) = h (fsuc (fsuc fzero))
        (_ , Td) = h (fsuc (fsuc (fsuc fzero)))
        (_ , Tb) = h (fsuc (fsuc (fsuc (fsuc fzero))))
        (_ , Tw) =
          h (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))
        X = object Γ
        env = values Γ
        α = meaning A X env
    in vΓ
       , J-typed m k A M a d b w X env TA Ta
           (typed-along (X ▸ α) (ext α env) (suc k) M (Formers.universe k)
             (paths-value m A a X env (term-stable TA) (term-stable Ta)) TM)
           (term-stable Td)
           (term-type Td ∙
             instantiate₂-value M a (Formers.reflexivity m A a) X env
               (term-stable Ta)
               (reflexivity-stable m A a X env (term-stable TA) (term-type TA)
                 (term-stable Ta) (term-type Ta)))
           Tb Tw
  sound (Block.computation Γ m k A M a d) h =
    let (vΓ , TA) = h fzero
        (_ , Ta) = h (fsuc fzero)
        (_ , TM) = h (fsuc (fsuc fzero))
        (_ , Td) = h (fsuc (fsuc (fsuc fzero)))
        X = object Γ
        env = values Γ
        α = meaning A X env
        x = meaning a X env
        I = identity m (α [ p ]) (x [ p ]) (q α)
        cA = term-type TA
        ta = term-type Ta
        TM₀ = typed-along (X ▸ α) (ext α env) (suc k) M (Formers.universe k)
                (paths-value m A a X env (term-stable TA) (term-stable Ta)) TM
        sr = reflexivity-stable m A a X env (term-stable TA) cA
               (term-stable Ta) ta
        tr = reflexivity-type m α x cA ta ∙
               paths-at m α x x cA ta ta ⁻¹
        td = term-type Td ∙
               instantiate₂-at m m M a (Formers.reflexivity m A a) X α I env
                 (term-stable TM₀) (term-stable Ta) sr ta cA tr
                 (paths-code m α x cA ta)
    in vΓ
       , J-typed m k A M a d a (Formers.reflexivity m A a) X env TA Ta TM₀
           (term-stable Td)
           (term-type Td ∙
             instantiate₂-value M a (Formers.reflexivity m A a) X env
               (term-stable Ta) sr)
           Ta (reflexivity-typed m A a X env TA Ta)
       , Td
       , J-value m k A M a d a (Formers.reflexivity m A a) X env ∙
           path-induction-reflexivity m k α x
             (meaning M (X ▸ α ▸ I) (ext I (ext α env))) (meaning d X env) cA
             ta (term-type TM₀) td
  sound (Block.formation-equal Γ m A A′ a a′ b b′) h =
    let (vΓ , TA , TA′ , eA) = h fzero
        (_ , Ta , Ta′ , ea) = h (fsuc fzero)
        (_ , Tb , Tb′ , eb) = h (fsuc (fsuc fzero))
        X = object Γ
        env = values Γ
    in vΓ
       , identity-typed m A a b X env TA Ta Tb
       , identity-typed m A′ a′ b′ X env TA′
           (retype X env m a′ A′ A Ta′ (term-stable TA′) (term-type TA′) eA)
           (retype X env m b′ A′ A Tb′ (term-stable TA′) (term-type TA′) eA)
       , ap₃ (identity m) eA ea eb
  sound (Block.introduction-equal Γ m A A′ a a′) h =
    let (vΓ , TA , TA′ , eA) = h fzero
        (_ , Ta , Ta′ , ea) = h (fsuc fzero)
        X = object Γ
        env = values Γ
        TR = reflexivity-typed m A a X env TA Ta
    in vΓ
       , TR
       , retype X env m (Formers.reflexivity m A′ a′)
           (Formers.identity m A a a) (Formers.identity m A′ a′ a′)
           (reflexivity-typed m A′ a′ X env TA′
             (retype X env m a′ A′ A Ta′ (term-stable TA′) (term-type TA′)
               eA))
           (type-stable TR) (type-code TR)
           (ap₃ (identity m) eA ea ea ⁻¹)
       , ap₂ (reflexivity m) eA ea
  sound (Block.elimination-equal Γ m k A A′ M M′ a a′ d d′ b b′ w w′) h =
    let (vΓ , TA , TA′ , eA) = h fzero
        (_ , Ta , Ta′ , ea) = h (fsuc fzero)
        (_ , TM , TM′ , eM) = h (fsuc (fsuc fzero))
        (_ , Td , Td′ , ed) = h (fsuc (fsuc (fsuc fzero)))
        (_ , Tb , Tb′ , eb) =
          h (fsuc (fsuc (fsuc (fsuc fzero))))
        (_ , Tw , Tw′ , ew) =
          h (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))
        X = object Γ
        env = values Γ
        α = meaning A X env
        x = meaning a X env
        y = meaning b X env
        I = identity m (α [ p ]) (x [ p ]) (q α)
        cA = term-type TA
        ta = term-type Ta
        tb = term-type Tb
        eI = paths-value m A a X env (term-stable TA) (term-stable Ta)
        TM₀ = typed-along (X ▸ α) (ext α env) (suc k) M (Formers.universe k)
                eI TM
        TM₀′ = typed-along (X ▸ α) (ext α env) (suc k) M′
                 (Formers.universe k) eI TM′
        eM₀ = transport
                (λ c → meaning M (X ▸ α ▸ c) (ext c (ext α env))
                       ＝ meaning M′ (X ▸ α ▸ c) (ext c (ext α env)))
                eI eM
        cI = paths-code m α x cA ta
        sr = reflexivity-stable m A a X env (term-stable TA) cA
               (term-stable Ta) ta
        tr = reflexivity-type m α x cA ta ∙
               paths-at m α x x cA ta ta ⁻¹
        tw = term-type Tw ∙ paths-at m α x y cA ta tb ⁻¹
        Ta″ = retype X env m a′ A′ A Ta′ (term-stable TA′) (term-type TA′) eA
        Tb″ = retype X env m b′ A′ A Tb′ (term-stable TA′) (term-type TA′) eA
        TI′ = identity-typed m A′ a′ b′ X env TA′ Ta″ Tb″
        Tw″ = retype X env m w′ (Formers.identity m A′ a′ b′)
                (Formers.identity m A a b) Tw′ (term-stable TI′)
                (term-type TI′) (ap₃ (identity m) eA ea eb)
        TM″ = transport₂
                (λ u v → Typed
                   (X ▸ u ▸ identity m (u [ p ]) (v [ p ]) (q u))
                   (ext (identity m (u [ p ]) (v [ p ]) (q u)) (ext u env))
                   (suc k) M′ (Formers.universe k))
                eA ea TM₀′
        tdv = term-type Td ∙
                instantiate₂-value M a (Formers.reflexivity m A a) X env
                  (term-stable Ta) sr
        tdv′ = term-type Td′ ∙
                 (instantiate₂-value M a (Formers.reflexivity m A a) X env
                     (term-stable Ta) sr ∙
                   (equal₂-at m m M M′ X α I env (term-stable TM₀)
                       (term-stable TM₀′) eM₀ x (reflexivity m α x) ta cA tr
                       cI ∙
                     ap₂ (λ u v → meaning M′ X (reflexivity m u v ∷ v ∷ env))
                       eA ea))
        TL = J-typed m k A M a d b w X env TA Ta TM₀ (term-stable Td) tdv Tb Tw
    in vΓ
       , TL
       , retype X env k (Formers.path-induction m k A′ M′ a′ d′ b′ w′)
           (Formers.instantiate₂ M b w) (Formers.instantiate₂ M′ b′ w′)
           (J-typed m k A′ M′ a′ d′ b′ w′ X env TA′ Ta″ TM″ (term-stable Td′)
             tdv′ Tb″ Tw″)
           (type-stable TL) (type-code TL)
           (instantiate₂-value M′ b′ w′ X env (term-stable Tb′)
               (term-stable Tw′) ∙
             (ap₂ (λ u v → meaning M′ X (u ∷ v ∷ env)) (ew ⁻¹) (eb ⁻¹) ∙
               (equal₂-at m m M M′ X α I env (term-stable TM₀)
                     (term-stable TM₀′) eM₀ y (meaning w X env) tb cA tw cI ⁻¹ ∙
                 instantiate₂-value M b w X env (term-stable Tb)
                     (term-stable Tw) ⁻¹)))
       , J-value m k A M a d b w X env ∙
           (ap
               (λ c → path-induction m k α x c (meaning d X env) y
                        (meaning w X env))
               eM₀ ∙
             (ap₃
                 (path-induction m k α x
                   (meaning M′ (X ▸ α ▸ I) (ext I (ext α env))))
                 ed eb ew ∙
               (ap₂
                   (λ u v → path-induction m k u v
                      (meaning M′
                        (X ▸ u ▸ identity m (u [ p ]) (v [ p ]) (q u))
                        (ext (identity m (u [ p ]) (v [ p ]) (q u))
                          (ext u env)))
                      (meaning d′ X env) (meaning b′ X env)
                      (meaning w′ X env))
                   eA ea ∙
                 J-value m k A′ M′ a′ d′ b′ w′ X env ⁻¹)))
