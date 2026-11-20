{-# OPTIONS --safe --without-K --no-projection-like #-}

module SPT.MartinLof.Soundness.Typing where

-- Small facts the soundness of every rule block uses. A closed term read
-- along ε is stable (`closed-stable`), so the value of a closed former
-- is. A stable term of a universe is a type there (`as-type`). A
-- premise binding a variable of a type a, stable at the extension, is
-- carried by a substitution τ to the premise at the extension by a [ τ ]
-- with its last variable replaced (`under-stable`); an instance of it at a
-- term x of type a is a type when it is (`instance-code`), and the
-- instance of a term of it has the instance type (`instance-type`). A
-- term typed by B is typed by any A with B's value (`retype`). Typed data
-- survive substitution (`typed-[]`), also under a binder (`typed-under`),
-- and follow an equation of the bound type (`typed-along`).
--
-- Substitutions under binders: a weakened term after a substitution with
-- a last variable (`p-⨾`), under a binder (`p-under`, `q-under`) and at a
-- section (`p-section`, `q-section`); replacing the last variable keeps
-- types and codes (`⨾-type`, `⨾-code`). A meaning stable at an
-- extension by s takes, at a substitution ρ with a term of type s [ ρ ]
-- for the variable, the value it has there with the variable replaced
-- (`stable-extend`), also at a binder of a new type b′ (`lift-stable`); a
-- substitution lifts to binders whose types it relates (`binder-type`,
-- `ext-lift`), carrying stability and typed data (`stable-lift`,
-- `typed-lift`); meanings equal and
-- stable at an environment are equal at its instances (`equal-[]`).
--
-- Instances: a weakened expression skips the first entry of an environment
-- (`weaken-cons`, `weaken-cons-stable`); a renamed one reads the
-- environment through the renaming (`rename-stable`); the instance of a
-- type over A at a term of A is a type (`instance-as-type`), the instance
-- of a term of it has the instance type (`instance-typed`), and instances
-- of equal families at equal terms are equal (`instantiate-equal`). Over
-- two variables, the values, stability and typing of instances at two terms
-- (`ext-section₂`, `instantiate₂-at`, `instantiate₂-stable`,
-- `instance₂-typed`).

open import SPT.Base hiding (Lift; _∘_; id; lift; lower; zero)
open import SPT.Foundation.Vectors.Tabulation using
  (tabulate; tabulate-cong; tabulate-lookup; tabulate-∘)
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Tree as Tree
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
  (Russell; Code; code-[]; closed-code; section; under; under-type)
open import SPT.MartinLof.Model.Sigma using (Sigma)
open import SPT.MartinLof.Model.Sum using (Sum)
open import SPT.MartinLof.Model.Unit using (Unit)
open import SPT.MartinLof.Model.WellFounded using (WellFounded)
import SPT.MartinLof.Soundness.Environment as Environment
import SPT.MartinLof.Soundness.Instances as Instances
import SPT.MartinLof.Soundness.Interpretation as Interpretation

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
  (let extended-stable = Instances.extended-stable R lifting products pairs
                           paths trees nothing one sums numbers
                           operations subuniverses constant)
  (let substitute-stable = Instances.substitute-stable R lifting products
                             pairs paths trees nothing one sums numbers
                             operations subuniverses constant)
  (let instantiate-at = Instances.instantiate-at R lifting products pairs
                          paths trees nothing one sums numbers
                          operations subuniverses constant)
  (let instantiate-stable = Instances.instantiate-stable R lifting products
                              pairs paths trees nothing one sums numbers
                              operations subuniverses constant)
  (let instantiate₂-value = Instances.instantiate₂-value R lifting products
                              pairs paths trees nothing one sums numbers
                              operations subuniverses constant)
  (let weaken-value = Instances.weaken-value R lifting products pairs paths
                        trees nothing one sums numbers operations subuniverses
                          constant)
  (let rename-value = Instances.rename-value R lifting products pairs paths
                        trees nothing one sums numbers operations subuniverses
                          constant)
  (let type-stable = Interpretation.Typed.type-stable)
  (let type-code = Interpretation.Typed.type-code)
  (let term-stable = Interpretation.Typed.term-stable)
  (let term-type = Interpretation.Typed.term-type)
  where

  -- A closed term, read along ε, is stable.
  closed-stable :
    (t : Tm ◇) (X : Ob) {k : ℕ} (env : Vec (Tm X) k)
    → Stable (λ Y env′ → t [ ε Y ]) X env
  closed-stable t X env Y τ =
    ap (λ σ → t [ σ ]) (ε-unique (ε X ∘ τ) ⁻¹) ∙ [∘] t (ε X) τ

  -- A stable term of the universe at l is a type at l.
  as-type :
    {n : ℕ} (X : Ob) (env : Vec (Tm X) n) (l : ℕ) (A : Raw.Expression C n)
    → Stable (meaning A) X env → Code R l (meaning A X env)
    → Typed X env (suc l) A (Formers.universe l)
  as-type X env l A sA cA = record
    { type-stable = closed-stable (universe l) X env
    ; type-code = closed-code R (suc l) (universe l) (ε X) (universe-type l)
    ; term-stable = sA
    ; term-type = cA
    }

  -- A premise binding a variable of type a, along a substitution τ.
  under-stable :
    {n : ℕ} (l : ℕ) (B : Raw.Expression C (suc n)) (X : Ob) (a : Tm X)
    (env : Vec (Tm X) n) (ta : Code R l a)
    → Stable (meaning B) (X ▸ a) (ext a env) → {Y : Ob} (τ : Hom Y X)
    → meaning B (Y ▸ a [ τ ]) (ext (a [ τ ]) (env [ τ ]ᵉ))
      ＝ meaning B (X ▸ a) (ext a env) [ τ ∘ p ⨾ q (a [ τ ]) ]
  under-stable l B X a env ta sB {Y} τ =
    ap (meaning B (Y ▸ a [ τ ]))
        (Environment.ext-under R l a env τ ta ⁻¹) ∙
      (sB (Y ▸ a [ τ ]) (under R l a τ ta) ∙
        Environment.⨾-under R l a (meaning B (X ▸ a) (ext a env)) τ ta)

  -- A type over a, replaced at a term of type a, is a type.
  instance-code :
    {X : Ob} (l k : ℕ) (a x : Tm X) (b : Tm (X ▸ a))
    → type-of x ＝ a → Code R l a → Code R k b → Code R k (b [ id ⨾ x ])
  instance-code l k a x b tx ta tb =
    transport (Code R k) (Environment.⨾-section R a x b tx)
      (code-[] R k b (section R a x tx) tb)

  -- A term of type B has every type A with B's value.
  retype :
    {n : ℕ} (X : Ob) (env : Vec (Tm X) n) (l : ℕ) (t A B : Raw.Expression C n)
    → Typed X env l t B → Stable (meaning A) X env
    → Code R l (meaning A X env) → meaning B X env ＝ meaning A X env
    → Typed X env l t A
  retype X env l t A B T sA cA e = record
    { type-stable = sA
    ; type-code = cA
    ; term-stable = Interpretation.Typed.term-stable T
    ; term-type = Interpretation.Typed.term-type T ∙ e
    }

  -- The instance of a term of b at x has the instance of b.
  instance-type :
    {X : Ob} (a x : Tm X) (b t : Tm (X ▸ a)) → type-of x ＝ a
    → type-of t ＝ b → type-of (t [ id ⨾ x ]) ＝ b [ id ⨾ x ]
  instance-type a x b t tx tt =
    ap type-of (Environment.⨾-section R a x t tx ⁻¹) ∙
      (type-of-[] t (section R a x tx) ∙
        (ap (λ s → s [ section R a x tx ]) tt ∙
          Environment.⨾-section R a x b tx))

  -- Typed data survive substitution.
  typed-[] :
    {n : ℕ} (X : Ob) (env : Vec (Tm X) n) (l : ℕ) (t A : Raw.Expression C n)
    → Typed X env l t A → {Y : Ob} (τ : Hom Y X)
    → Typed Y (env [ τ ]ᵉ) l t A
  typed-[] X env l t A T {Y} τ = record
    { type-stable =
        Environment.stable-[] R (meaning A) X env
          (Interpretation.Typed.type-stable T) τ
    ; type-code =
        transport (Code R l) (Interpretation.Typed.type-stable T Y τ ⁻¹)
          (code-[] R l (meaning A X env) τ (Interpretation.Typed.type-code T))
    ; term-stable =
        Environment.stable-[] R (meaning t) X env
          (Interpretation.Typed.term-stable T) τ
    ; term-type =
        ap type-of (Interpretation.Typed.term-stable T Y τ) ∙
          (type-of-[] (meaning t X env) τ ∙
            (ap (λ s → s [ τ ]) (Interpretation.Typed.term-type T) ∙
              Interpretation.Typed.type-stable T Y τ ⁻¹))
    }

  -- Typed data at an extension follow an equation of the bound type.
  typed-along :
    {n : ℕ} (X : Ob) (env : Vec (Tm X) n) (l : ℕ)
    (t B : Raw.Expression C (suc n)) {a a′ : Tm X} → a ＝ a′
    → Typed (X ▸ a) (ext a env) l t B → Typed (X ▸ a′) (ext a′ env) l t B
  typed-along X env l t B e T =
    transport (λ x → Typed (X ▸ x) (ext x env) l t B) e T

  -- Typed data at the extension by A's value, carried along τ.
  typed-under :
    {n : ℕ} (X : Ob) (env : Vec (Tm X) n) (m l : ℕ) (A : Raw.Expression C n)
    (t B : Raw.Expression C (suc n))
    → Stable (meaning A) X env → Code R m (meaning A X env)
    → Typed (X ▸ meaning A X env) (ext (meaning A X env) env) l t B
    → {Y : Ob} (τ : Hom Y X)
    → Typed (Y ▸ meaning A Y (env [ τ ]ᵉ))
        (ext (meaning A Y (env [ τ ]ᵉ)) (env [ τ ]ᵉ)) l t B
  typed-under X env m l A t B sA cA T {Y} τ =
    typed-along Y (env [ τ ]ᵉ) l t B (sA Y τ ⁻¹)
      (transport (λ e → Typed (Y ▸ meaning A X env [ τ ]) e l t B)
        (Environment.ext-under R m (meaning A X env) env τ cA)
        (typed-[] (X ▸ meaning A X env) (ext (meaning A X env) env) l t B T
          (under R m (meaning A X env) τ cA)))

  ----------------------------------------------------------------------
  -- Substitutions under binders

  -- A weakened term, after a substitution with a last variable.
  p-⨾ :
    {X Y : Ob} (a t : Tm X) (σ : Hom Y X) (x : Tm Y) → type-of x ＝ a [ σ ]
    → t [ p ] [ σ ⨾ x ] ＝ t [ σ ]
  p-⨾ a t σ x e =
    [⨾] a (t [ p ]) σ x e ∙
      ([∘] t p (extend a σ x e) ⁻¹ ∙
        ap (λ ν → t [ ν ]) (p-extend a σ x e))

  -- A weakened term, taken under a binder.
  p-under :
    {X Y : Ob} (l : ℕ) (a t : Tm X) (τ : Hom Y X) (ta : Code R l a)
    → t [ p ] [ under R l a τ ta ] ＝ t [ τ ] [ p ]
  p-under l a t τ ta =
    [∘] t p (under R l a τ ta) ⁻¹ ∙
      (ap (λ ν → t [ ν ])
          (p-extend a (τ ∘ p) (q (a [ τ ])) (under-type R l a τ ta)) ∙
        [∘] t τ p)

  q-under :
    {X Y : Ob} (l : ℕ) (a : Tm X) (τ : Hom Y X) (ta : Code R l a)
    → q a [ under R l a τ ta ] ＝ q (a [ τ ])
  q-under l a τ ta =
    q-extend l a (τ ∘ p) (q (a [ τ ])) (under-type R l a τ ta) ta

  -- A weakened term, and the variable, at a section.
  p-section :
    {X : Ob} (a t x : Tm X) (tx : type-of x ＝ a)
    → t [ p ] [ section R a x tx ] ＝ t
  p-section a t x tx =
    [∘] t p (section R a x tx) ⁻¹ ∙
      (ap (λ ν → t [ ν ])
          (p-extend a id x (tx ∙ [id] a ⁻¹)) ∙
        [id] t)

  q-section :
    {X : Ob} (l : ℕ) (a x : Tm X) (tx : type-of x ＝ a) → Code R l a
    → q a [ section R a x tx ] ＝ x
  q-section l a x tx ta = q-extend l a id x (tx ∙ [id] a ⁻¹) ta

  -- Replacing the last variable keeps types and codes.
  ⨾-type :
    {X Y : Ob} (a : Tm X) (b t : Tm (X ▸ a)) (σ : Hom Y X) (x : Tm Y)
    → type-of x ＝ a [ σ ] → type-of t ＝ b
    → type-of (t [ σ ⨾ x ]) ＝ b [ σ ⨾ x ]
  ⨾-type a b t σ x e tt =
    ap type-of ([⨾] a t σ x e) ∙
      (type-of-[] t (extend a σ x e) ∙
        (ap (λ s → s [ extend a σ x e ]) tt ∙
          [⨾] a b σ x e ⁻¹))

  ⨾-code :
    {X Y : Ob} (l : ℕ) (a : Tm X) (b : Tm (X ▸ a)) (σ : Hom Y X) (x : Tm Y)
    → type-of x ＝ a [ σ ] → Code R l b → Code R l (b [ σ ⨾ x ])
  ⨾-code l a b σ x e tb =
    transport (Code R l) ([⨾] a b σ x e ⁻¹) (code-[] R l b (extend a σ x e) tb)

  ----------------------------------------------------------------------
  -- Stability under binders

  -- Stable at an extension by s: at a substitution ρ with a term t of type
  -- s [ ρ ] for the variable, the value with the variable replaced.
  stable-extend :
    {k : ℕ} (μ : (Y : Ob) → Vec (Tm Y) (suc k) → Tm Y) (l : ℕ) (X : Ob)
    (s : Tm X) (env : Vec (Tm X) k) → Code R l s
    → Stable μ (X ▸ s) (ext s env)
    → {Y : Ob} (ρ : Hom Y X) (t : Tm Y) (e : type-of t ＝ s [ ρ ])
    → μ Y (t ∷ env [ ρ ]ᵉ) ＝ μ (X ▸ s) (ext s env) [ ρ ⨾ t ]
  stable-extend μ l X s env cs sμ {Y} ρ t e =
    ap (μ Y) (Environment.ext-extend R l s env ρ t e cs ⁻¹) ∙
      (sμ Y (extend s ρ t e) ∙
        [⨾] s (μ (X ▸ s) (ext s env)) ρ t e ⁻¹)

  -- The same along a binder of a new type b′, with the environment env′.
  lift-stable :
    {k : ℕ} (μ : (Y : Ob) → Vec (Tm Y) (suc k) → Tm Y) (l : ℕ) (X : Ob)
    (b : Tm X) (env : Vec (Tm X) k) → Code R l b
    → Stable μ (X ▸ b) (ext b env)
    → {Y : Ob} (ρ : Hom Y X) (b′ : Tm Y) (env′ : Vec (Tm Y) k)
    → (e : type-of (q b′) ＝ b [ ρ ∘ p ]) → env [ ρ ]ᵉ ＝ env′
    → μ (Y ▸ b′) (ext b′ env′) ＝ μ (X ▸ b) (ext b env) [ ρ ∘ p ⨾ q b′ ]
  lift-stable μ l X b env cb sμ {Y} ρ b′ env′ e eenv =
    ap (λ es → μ (Y ▸ b′) (q b′ ∷ es))
        ((Environment.[]ᵉ-∘ R env ρ p ∙
            ap (λ es → es [ p ]ᵉ) eenv) ⁻¹) ∙
      stable-extend μ l X b env cb sμ (ρ ∘ p) (q b′) e

  -- A substitution lifted to binders of types b over X and b′ over Y,
  -- where b [ ρ ] is b′: the typing proof, the environment, and typed
  -- data carried along it.
  binder-type :
    {X Y : Ob} (l : ℕ) (b : Tm X) (ρ : Hom Y X) (b′ : Tm Y) → Code R l b′
    → b [ ρ ] ＝ b′ → type-of (q b′) ＝ b [ ρ ∘ p ]
  binder-type l b ρ b′ cb′ e =
    q-type l b′ cb′ ∙
      (ap (λ t → t [ p ]) (e ⁻¹) ∙ [∘] b ρ p ⁻¹)

  ext-lift :
    {X Y : Ob} {k : ℕ} (l : ℕ) (b : Tm X) (env : Vec (Tm X) k) (ρ : Hom Y X)
    (b′ : Tm Y) (env′ : Vec (Tm Y) k) (e : type-of (q b′) ＝ b [ ρ ∘ p ])
    → Code R l b → env [ ρ ]ᵉ ＝ env′
    → ext b env [ extend b (ρ ∘ p) (q b′) e ]ᵉ ＝ ext b′ env′
  ext-lift l b env ρ b′ env′ e cb eenv =
    Environment.ext-extend R l b env (ρ ∘ p) (q b′) e cb ∙
      ap (λ es → q b′ ∷ es)
        (Environment.[]ᵉ-∘ R env ρ p ∙ ap (λ es → es [ p ]ᵉ) eenv)

  -- Stability along a lifted substitution, at the new binder: the typing
  -- proof of the lift stays inside, so the result does not mention it.
  stable-lift :
    {k : ℕ} (μ : (Y : Ob) → Vec (Tm Y) (suc k) → Tm Y) (l : ℕ) (X : Ob)
    (b : Tm X) (env : Vec (Tm X) k) → Code R l b
    → Stable μ (X ▸ b) (ext b env)
    → {Y : Ob} (ρ : Hom Y X) (b′ : Tm Y) (env′ : Vec (Tm Y) k)
    → (e : type-of (q b′) ＝ b [ ρ ∘ p ]) → env [ ρ ]ᵉ ＝ env′
    → Stable μ (Y ▸ b′) (ext b′ env′)
  stable-lift μ l X b env cb s {Y} ρ b′ env′ e eenv =
    transport (Stable μ (Y ▸ b′)) (ext-lift l b env ρ b′ env′ e cb eenv)
      (Environment.stable-[] R μ (X ▸ b) (ext b env) s
        (extend b (ρ ∘ p) (q b′) e))

  typed-lift :
    {n : ℕ} (X : Ob) (b : Tm X) (env : Vec (Tm X) n) (l l′ : ℕ)
    (t T : Raw.Expression C (suc n))
    → Typed (X ▸ b) (ext b env) l t T → Code R l′ b
    → {Y : Ob} (ρ : Hom Y X) (b′ : Tm Y) (env′ : Vec (Tm Y) n)
    → (e : type-of (q b′) ＝ b [ ρ ∘ p ]) → env [ ρ ]ᵉ ＝ env′
    → Typed (Y ▸ b′) (ext b′ env′) l t T
  typed-lift X b env l l′ t T TT cb {Y} ρ b′ env′ e eenv =
    transport (λ es → Typed (Y ▸ b′) es l t T)
      (ext-lift l′ b env ρ b′ env′ e cb eenv)
      (typed-[] (X ▸ b) (ext b env) l t T TT (extend b (ρ ∘ p) (q b′) e))

  -- Meanings equal and stable at env are equal at its instances.
  equal-[] :
    {k : ℕ} (μ μ′ : (Y : Ob) → Vec (Tm Y) k → Tm Y) (X : Ob)
    (env : Vec (Tm X) k) → Stable μ X env → Stable μ′ X env
    → μ X env ＝ μ′ X env → {Y : Ob} (τ : Hom Y X)
    → μ Y (env [ τ ]ᵉ) ＝ μ′ Y (env [ τ ]ᵉ)
  equal-[] μ μ′ X env s s′ e {Y} τ =
    s Y τ ∙ (ap (λ t → t [ τ ]) e ∙ s′ Y τ ⁻¹)

  ----------------------------------------------------------------------
  -- Instances

  -- A weakened expression, read in an environment with a first entry.
  weaken-cons :
    {n : ℕ} (e : Raw.Expression C n) (X : Ob) (v : Tm X) (env : Vec (Tm X) n)
    → meaning (Formers.weaken e) X (v ∷ env) ＝ meaning e X env
  weaken-cons e X v env =
    weaken-value e X (v ∷ env) ∙
      ap (meaning e X) (tabulate-lookup env)

  -- A weakened expression is stable where the expression is.
  weaken-cons-stable :
    {n : ℕ} (e : Raw.Expression C n) (X : Ob) (v : Tm X) (env : Vec (Tm X) n)
    → Stable (meaning e) X env
    → Stable (meaning (Formers.weaken e)) X (v ∷ env)
  weaken-cons-stable e X v env s Y τ =
    weaken-cons e Y (v [ τ ]) (env [ τ ]ᵉ) ∙
      (s Y τ ∙ ap (λ t → t [ τ ]) (weaken-cons e X v env ⁻¹))

  -- A renamed expression is stable where the expression is stable at the
  -- environment read through the renaming.
  rename-stable :
    {n k : ℕ} (ρ : Fin n → Fin k) (e : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) k)
    → Stable (meaning e) X (tabulate (λ i → vector-lookup env (ρ i)))
    → Stable (meaning (Binding.rename (Raw.binding C) ρ e)) X env
  rename-stable ρ e X env s Y τ =
    rename-value ρ e Y (env [ τ ]ᵉ) ∙
      (ap (meaning e Y)
          (tabulate-cong (λ i → Environment.lookup-[]ᵉ R env τ (ρ i)) ∙
            tabulate-∘ (λ t → t [ τ ]) (λ i → vector-lookup env (ρ i))) ∙
        (s Y τ ∙
          ap (λ t → t [ τ ]) (rename-value ρ e X env ⁻¹)))

  -- The instance of a type over A at a term of A is a type.
  instance-as-type :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (x : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Typed (X ▸ meaning A X env) (ext (meaning A X env) env) (suc k) B
        (Formers.universe k)
    → Typed X env m x A
    → Typed X env (suc k) (Formers.instantiate B x) (Formers.universe k)
  instance-as-type m k A B x X env TB Tx =
    let a = meaning A X env
        sB = term-stable TB
        sx = term-stable Tx
        tx = term-type Tx
        cA = type-code Tx
    in as-type X env k (Formers.instantiate B x)
         (instantiate-stable m B x X a env sB sx tx cA)
         (transport (Code R k) (instantiate-at m B x X a env sB sx tx cA ⁻¹)
           (instance-code m k a (meaning x X env)
             (meaning B (X ▸ a) (ext a env)) tx cA (term-type TB)))

  -- The instance of a term of B at a term of A has the instance of B.
  instance-typed :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B t : Raw.Expression C (suc n)) (x : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Typed (X ▸ meaning A X env) (ext (meaning A X env) env) (suc k) B
        (Formers.universe k)
    → Typed (X ▸ meaning A X env) (ext (meaning A X env) env) k t B
    → Typed X env m x A
    → Typed X env k (Formers.instantiate t x) (Formers.instantiate B x)
  instance-typed m k A B t x X env TB Tt Tx =
    let a = meaning A X env
        sx = term-stable Tx
        tx = term-type Tx
        cA = type-code Tx
        st = term-stable Tt
        T = instance-as-type m k A B x X env TB Tx
    in record
      { type-stable = term-stable T
      ; type-code = term-type T
      ; term-stable = instantiate-stable m t x X a env st sx tx cA
      ; term-type =
          ap type-of (instantiate-at m t x X a env st sx tx cA) ∙
            (instance-type a (meaning x X env)
                (meaning B (X ▸ a) (ext a env))
                (meaning t (X ▸ a) (ext a env)) tx (term-type Tt) ∙
              instantiate-at m B x X a env (term-stable TB) sx tx cA ⁻¹)
      }

  -- Instances of equal families over equal types at equal terms.
  instantiate-equal :
    {n : ℕ} (m : ℕ) (A A′ : Raw.Expression C n)
    (B B′ : Raw.Expression C (suc n)) (x x′ : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Stable (meaning B) (X ▸ meaning A X env) (ext (meaning A X env) env)
    → Stable (meaning B′) (X ▸ meaning A′ X env)
        (ext (meaning A′ X env) env)
    → Typed X env m x A → Typed X env m x′ A′
    → meaning A X env ＝ meaning A′ X env
    → meaning B (X ▸ meaning A X env) (ext (meaning A X env) env)
      ＝ meaning B′ (X ▸ meaning A X env) (ext (meaning A X env) env)
    → meaning x X env ＝ meaning x′ X env
    → meaning (Formers.instantiate B x) X env
      ＝ meaning (Formers.instantiate B′ x′) X env
  instantiate-equal m A A′ B B′ x x′ X env sB sB′ Tx Tx′ eA eB ex =
    instantiate-at m B x X (meaning A X env) env sB (term-stable Tx)
        (term-type Tx) (type-code Tx) ∙
      (ap (λ c → c [ id ⨾ meaning x X env ]) eB ∙
        (ap₂ (λ y z → meaning B′ (X ▸ y) (ext y env) [ id ⨾ z ]) eA ex ∙
          instantiate-at m B′ x′ X (meaning A′ X env) env sB′
              (term-stable Tx′) (term-type Tx′) (type-code Tx′) ⁻¹))

  ----------------------------------------------------------------------
  -- Instances over two variables

  -- An extension by a and b, along the section at x and y.
  ext-section₂ :
    {X : Ob} {k : ℕ} (l m : ℕ) (a : Tm X) (b : Tm (X ▸ a))
    (env : Vec (Tm X) k) (x y : Tm X) (tx : type-of x ＝ a) → Code R l a
    → (ty : type-of y ＝ b [ section R a x tx ]) → Code R m b
    → ext b (ext a env) [ extend b (section R a x tx) y ty ]ᵉ ＝ y ∷ x ∷ env
  ext-section₂ l m a b env x y tx ta ty tb =
    Environment.ext-extend R m b (ext a env) (section R a x tx) y ty tb ∙
      ap (λ es → y ∷ es) (Environment.ext-section R l a x env tx ta)

  -- The instance at x and y: the value at the extension with both
  -- variables replaced.
  instantiate₂-at :
    {n : ℕ} (l m : ℕ) (M : Raw.Expression C (suc (suc n)))
    (x y : Raw.Expression C n) (X : Ob) (a : Tm X) (b : Tm (X ▸ a))
    (env : Vec (Tm X) n)
    → Stable (meaning M) (X ▸ a ▸ b) (ext b (ext a env))
    → Stable (meaning x) X env → Stable (meaning y) X env
    → (tx : type-of (meaning x X env) ＝ a) → Code R l a
    → (ty : type-of (meaning y X env)
            ＝ b [ section R a (meaning x X env) tx ])
    → Code R m b
    → meaning (Formers.instantiate₂ M x y) X env
      ＝ meaning M (X ▸ a ▸ b) (ext b (ext a env))
          [ section R a (meaning x X env) tx ⨾ meaning y X env ]
  instantiate₂-at l m M x y X a b env sM sx sy tx ta ty tb =
    let x′ = meaning x X env
        y′ = meaning y X env
    in instantiate₂-value M x y X env sx sy ∙
         (ap (meaning M X)
             (ext-section₂ l m a b env x′ y′ tx ta ty tb ⁻¹) ∙
           (sM X (extend b (section R a x′ tx) y′ ty) ∙
             [⨾] b (meaning M (X ▸ a ▸ b) (ext b (ext a env)))
                 (section R a x′ tx) y′ ty ⁻¹))

  instantiate₂-stable :
    {n : ℕ} (l m : ℕ) (M : Raw.Expression C (suc (suc n)))
    (x y : Raw.Expression C n) (X : Ob) (a : Tm X) (b : Tm (X ▸ a))
    (env : Vec (Tm X) n)
    → Stable (meaning M) (X ▸ a ▸ b) (ext b (ext a env))
    → Stable (meaning x) X env → Stable (meaning y) X env
    → (tx : type-of (meaning x X env) ＝ a) → Code R l a
    → type-of (meaning y X env) ＝ b [ section R a (meaning x X env) tx ]
    → Code R m b
    → Stable (meaning (Formers.instantiate₂ M x y)) X env
  instantiate₂-stable {n} l m M x y X a b env sM sx sy tx ta ty tb =
    let x′ = meaning x X env
        y′ = meaning y X env
    in substitute-stable
         (Formers.extended
           (Formers.extended (λ (i : Fin n) → Tree.hole i) x) y)
         M X env
         (extended-stable
           (Formers.extended (λ (i : Fin n) → Tree.hole i) x) y X env
           (extended-stable (λ (i : Fin n) → Tree.hole i) x X env
             (λ i → Environment.stable-lookup R i X env) sx)
           sy)
         (transport (Stable (meaning M) X)
           (ap (λ es → y′ ∷ x′ ∷ es) (tabulate-lookup env ⁻¹))
           (transport (Stable (meaning M) X)
             (ext-section₂ l m a b env x′ y′ tx ta ty tb)
             (Environment.stable-[] R (meaning M) (X ▸ a ▸ b)
               (ext b (ext a env)) sM (extend b (section R a x′ tx) y′ ty))))

  -- The instance at x and y of a term of S has the instance of S.
  instance₂-typed :
    {n : ℕ} (l l₁ l₂ : ℕ) (s S : Raw.Expression C (suc (suc n)))
    (x y : Raw.Expression C n) (X : Ob) (a : Tm X) (b : Tm (X ▸ a))
    (env : Vec (Tm X) n)
    → Typed (X ▸ a ▸ b) (ext b (ext a env)) l s S
    → Stable (meaning x) X env → (tx : type-of (meaning x X env) ＝ a)
    → Code R l₁ a → Stable (meaning y) X env
    → type-of (meaning y X env) ＝ b [ section R a (meaning x X env) tx ]
    → Code R l₂ b
    → Typed X env l (Formers.instantiate₂ s x y) (Formers.instantiate₂ S x y)
  instance₂-typed l l₁ l₂ s S x y X a b env T sx tx ta sy ty tb =
    let x′ = meaning x X env
        y′ = meaning y X env
        σ = section R a x′ tx
        S′ = meaning S (X ▸ a ▸ b) (ext b (ext a env))
        eS = instantiate₂-at l₁ l₂ S x y X a b env (type-stable T) sx sy tx
               ta ty tb
    in record
      { type-stable =
          instantiate₂-stable l₁ l₂ S x y X a b env (type-stable T) sx sy tx
            ta ty tb
      ; type-code =
          transport (Code R l) (eS ⁻¹) (⨾-code l b S′ σ y′ ty (type-code T))
      ; term-stable =
          instantiate₂-stable l₁ l₂ s x y X a b env (term-stable T) sx sy tx
            ta ty tb
      ; term-type =
          ap type-of
              (instantiate₂-at l₁ l₂ s x y X a b env (term-stable T) sx sy tx
                ta ty tb) ∙
            (⨾-type b S′ (meaning s (X ▸ a ▸ b) (ext b (ext a env))) σ y′
                ty (term-type T) ∙
              eS ⁻¹)
      }
