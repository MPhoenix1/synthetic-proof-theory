{-# OPTIONS --safe --without-K --no-projection-like #-}

module SPT.MartinLof.Soundness.Natural where

-- Soundness of the rules of ℕ (`sound`). ℕ and zero are closed terms read
-- along ε; the successor and induction are the model's operations at the
-- values of their children, the motive read at the extension by ℕ and the
-- step at the further extension by the motive (`induction-value`). They
-- are stable (`successor-stable`, `induction-stable`: the motive is taken
-- along the extension of a substitution by ℕ over the new context, the
-- step along that extension and the motive's) and have their types by the
-- typing laws (`successor-typed`, `induction-typed`). The step's type, M
-- at the successor, has the value the model's laws ask for
-- (`next-value`). At zero and at a successor, induction computes by the
-- model's β; the step's instance has the motive's type at the successor
-- (`next-instance-value`).

open import SPT.Base hiding (Lift; _∘_; id; lift; lower; zero)
open import SPT.Foundation.Vectors.Tabulation using (tabulate-lookup)
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Tree as Tree
import SPT.Foundation.Tree.Binding as Binding
import SPT.MartinLof.Formers as Formers
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Judgment using (Judgment)
import SPT.MartinLof.Rules.Natural as Block
open import SPT.MartinLof.Model.Empty using (Empty)
open import SPT.MartinLof.Model.Identity using (Identity)
open import SPT.MartinLof.Model.Lift using (Lift)
open import SPT.MartinLof.Model.Natural using (Natural)
open import SPT.MartinLof.Model.Subuniverse using
  (Operations; Subuniverse)
open import SPT.MartinLof.Model.Pi using (Pi)
open import SPT.MartinLof.Model.Russell using
  (Russell; Code; closed-code; section)
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
  (let instantiate-value = Instances.instantiate-value R lifting products
                             pairs paths trees nothing one sums numbers
                             operations subuniverses constant)
  (let instantiate₂-value = Instances.instantiate₂-value R lifting products
                              pairs paths trees nothing one sums numbers
                              operations subuniverses constant)
  (let instantiate-past-value = Instances.instantiate-past-value R lifting
                                  products pairs paths trees nothing one sums
                                  numbers operations subuniverses constant)
  (let instantiate-at = Instances.instantiate-at R lifting products pairs
                          paths trees nothing one sums numbers
                          operations subuniverses constant)
  (let closed-stable = Typing.closed-stable R lifting products pairs paths
                         trees nothing one sums numbers operations subuniverses
                           constant)
  (let as-type = Typing.as-type R lifting products pairs paths trees nothing
                   one sums numbers operations subuniverses constant)
  (let retype = Typing.retype R lifting products pairs paths trees nothing
                  one sums numbers operations subuniverses constant)
  (let ⨾-code = Typing.⨾-code R lifting products pairs paths trees nothing
                  one sums numbers operations subuniverses constant)
  (let stable-extend = Typing.stable-extend R lifting products pairs paths
                         trees nothing one sums numbers operations subuniverses
                           constant)
  (let lift-stable = Typing.lift-stable R lifting products pairs paths trees
                       nothing one sums numbers operations subuniverses
                         constant)
  (let instance-as-type = Typing.instance-as-type R lifting products pairs
                            paths trees nothing one sums numbers
                            operations subuniverses constant)
  (let instantiate-equal = Typing.instantiate-equal R lifting products pairs
                             paths trees nothing one sums numbers
                             operations subuniverses constant)
  (let instantiate₂-at = Typing.instantiate₂-at R lifting products pairs
                           paths trees nothing one sums numbers
                           operations subuniverses constant)
  (let instance₂-typed = Typing.instance₂-typed R lifting products pairs
                           paths trees nothing one sums numbers
                           operations subuniverses constant)
  (let type-stable = Interpretation.Typed.type-stable)
  (let type-code = Interpretation.Typed.type-code)
  (let term-stable = Interpretation.Typed.term-stable)
  (let term-type = Interpretation.Typed.term-type)
  where

  ----------------------------------------------------------------------
  -- ℕ, zero and the successor

  natural-code : (X : Ob) → Code R 0 (natural [ ε X ])
  natural-code X = closed-code R 0 natural (ε X) natural-type

  zero-type-at : (X : Ob) → type-of (zero [ ε X ]) ＝ natural [ ε X ]
  zero-type-at X =
    type-of-[] zero (ε X) ∙ ap (λ s → s [ ε X ]) zero-type

  natural-typed :
    {n : ℕ} (X : Ob) (env : Vec (Tm X) n)
    → Typed X env (suc 0) Formers.natural (Formers.universe 0)
  natural-typed X env =
    as-type X env 0 Formers.natural (closed-stable natural X env)
      (natural-code X)

  zero-typed :
    {n : ℕ} (X : Ob) (env : Vec (Tm X) n)
    → Typed X env 0 Formers.zero Formers.natural
  zero-typed X env = record
    { type-stable = closed-stable natural X env
    ; type-code = natural-code X
    ; term-stable = closed-stable zero X env
    ; term-type = zero-type-at X
    }

  successor-stable :
    {n : ℕ} (t : Raw.Expression C n) (X : Ob) (env : Vec (Tm X) n)
    → Stable (meaning t) X env → type-of (meaning t X env) ＝ natural [ ε X ]
    → Stable (meaning (Formers.successor t)) X env
  successor-stable t X env st tt Y τ =
    ap successor (st Y τ) ∙
      successor-[] (meaning t X env) τ tt ⁻¹

  successor-typed :
    {n : ℕ} (t : Raw.Expression C n) (X : Ob) (env : Vec (Tm X) n)
    → Typed X env 0 t Formers.natural
    → Typed X env 0 (Formers.successor t) Formers.natural
  successor-typed t X env Tt = record
    { type-stable = closed-stable natural X env
    ; type-code = natural-code X
    ; term-stable = successor-stable t X env (term-stable Tt) (term-type Tt)
    ; term-type = successor-type (meaning t X env) (term-type Tt)
    }

  ----------------------------------------------------------------------
  -- Induction

  induction-value :
    {n : ℕ} (l : ℕ) (M : Raw.Expression C (suc n)) (z : Raw.Expression C n)
    (s : Raw.Expression C (suc (suc n))) (t : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → meaning (Formers.natural-induction l M z s t) X env
      ＝ natural-induction l
          (meaning M (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env))
          (meaning z X env)
          (meaning s
            (X ▸ natural [ ε X ]
               ▸ meaning M (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env))
            (ext (meaning M (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env))
              (ext (natural [ ε X ]) env)))
          (meaning t X env)
  induction-value {n} l M z s t X env =
    let N = natural [ ε X ]
        M₀ = meaning M (X ▸ N) (ext N env)
    in ap
           (λ M′ → natural-induction l M′ (meaning z X env)
                     (meaning (Binding.bound (Raw.binding C) n 2 s)
                       (X ▸ N ▸ M′) (ext M′ (ext N env)))
                     (meaning t X env))
           (bound-meaning 1 M (X ▸ N) (ext N env)) ∙
         ap
           (λ s′ → natural-induction l M₀ (meaning z X env) s′
                     (meaning t X env))
           (bound-meaning 2 s (X ▸ N ▸ M₀) (ext M₀ (ext N env)))

  -- The variable of the extension by ℕ, weakened past the motive's.
  previous-type :
    (X : Ob) (M₀ : Tm (X ▸ natural [ ε X ]))
    → type-of (q (natural [ ε X ]) [ p ])
      ＝ natural [ ε (X ▸ natural [ ε X ] ▸ M₀) ]
  previous-type X M₀ =
    let N = natural [ ε X ]
    in type-of-[] (q N) p ∙
         (ap (λ u → u [ p ]) (q-type 0 N (natural-code X)) ∙
           ([∘] N p p ⁻¹ ∙
             closed-stable natural X [] (X ▸ N ▸ M₀) (p ∘ p) ⁻¹))

  -- The step's type, M at the successor of the number.
  next-value :
    {n : ℕ} (M : Raw.Expression C (suc n)) (X : Ob) (env : Vec (Tm X) n)
    → Stable (meaning M) (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env)
    → meaning (Block.next M)
        (X ▸ natural [ ε X ]
           ▸ meaning M (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env))
        (ext (meaning M (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env))
          (ext (natural [ ε X ]) env))
      ＝ meaning M (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env)
          [ p ∘ p ⨾ successor (q (natural [ ε X ]) [ p ]) ]
  next-value M X env sM =
    let N = natural [ ε X ]
        M₀ = meaning M (X ▸ N) (ext N env)
        Z = X ▸ N ▸ M₀
        env₂ = ext M₀ (ext N env)
        e = successor-type (q N [ p ]) (previous-type X M₀) ∙
              closed-stable natural X env Z (p ∘ p)
    in instantiate-past-value 2 M
           (Formers.successor (Tree.hole (fsuc fzero))) Z env₂
           (successor-stable (Tree.hole (fsuc fzero)) Z env₂
             (Environment.stable-lookup R (fsuc fzero) Z env₂)
             (previous-type X M₀)) ∙
         (ap (λ es → meaning M Z (successor (q N [ p ]) ∷ es))
             (tabulate-lookup (env [ p ]ᵉ [ p ]ᵉ) ∙
               Environment.[]ᵉ-∘ R env p p ⁻¹) ∙
           stable-extend (meaning M) 0 X N env (natural-code X) sM (p ∘ p)
             (successor (q N [ p ])) e)

  induction-stable :
    {n : ℕ} (l : ℕ) (M : Raw.Expression C (suc n)) (z : Raw.Expression C n)
    (s : Raw.Expression C (suc (suc n))) (t : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Stable (meaning M) (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env)
    → Code R l (meaning M (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env))
    → Stable (meaning z) X env
    → type-of (meaning z X env)
      ＝ meaning M (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env)
          [ id ⨾ zero [ ε X ] ]
    → Stable (meaning s)
        (X ▸ natural [ ε X ]
           ▸ meaning M (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env))
        (ext (meaning M (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env))
          (ext (natural [ ε X ]) env))
    → type-of
        (meaning s
          (X ▸ natural [ ε X ]
             ▸ meaning M (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env))
          (ext (meaning M (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env))
            (ext (natural [ ε X ]) env)))
      ＝ meaning M (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env)
          [ p ∘ p ⨾ successor (q (natural [ ε X ]) [ p ]) ]
    → Stable (meaning t) X env → type-of (meaning t X env) ＝ natural [ ε X ]
    → Stable (meaning (Formers.natural-induction l M z s t)) X env
  induction-stable l M z s t X env sM cM sz tz ss ts st tt Y τ =
    let N = natural [ ε X ]
        N′ = natural [ ε Y ]
        M₀ = meaning M (X ▸ N) (ext N env)
        s₀ = meaning s (X ▸ N ▸ M₀) (ext M₀ (ext N env))
        envτ = env [ τ ]ᵉ
        e = q-type 0 N′ (natural-code Y) ∙
              (ap (λ u → u [ p ]) (closed-stable natural X env Y τ) ∙
                [∘] N τ p ⁻¹)
        ρ = extend N (τ ∘ p) (q N′) e
        Mτ = M₀ [ τ ∘ p ⨾ q N′ ]
        e₂ = q-type l Mτ (⨾-code l N M₀ (τ ∘ p) (q N′) e cM) ∙
               (ap (λ u → u [ p ]) ([⨾] N M₀ (τ ∘ p) (q N′) e) ∙
                 [∘] M₀ ρ p ⁻¹)
        eenv = Environment.ext-extend R 0 N env (τ ∘ p) (q N′) e
                   (natural-code X) ∙
                 ap (λ es → q N′ ∷ es) (Environment.[]ᵉ-∘ R env τ p)
    in induction-value l M z s t Y envτ ∙
         (ap
             (λ M′ → natural-induction l M′ (meaning z Y envτ)
                       (meaning s (Y ▸ N′ ▸ M′) (ext M′ (ext N′ envτ)))
                       (meaning t Y envτ))
             (lift-stable (meaning M) 0 X N env (natural-code X) sM τ N′ envτ e
               refl) ∙
           (ap₃ (natural-induction l Mτ) (sz Y τ)
               (lift-stable (meaning s) l (X ▸ N) M₀ (ext N env) cM ss ρ Mτ
                 (ext N′ envτ) e₂ eenv)
               (st Y τ) ∙
             (natural-induction-[] l M₀ (meaning z X env) s₀
                   (meaning t X env) τ cM tz ts tt e ⁻¹ ∙
               ap (λ u → u [ τ ])
                 (induction-value l M z s t X env ⁻¹))))

  induction-typed :
    {n : ℕ} (l : ℕ) (M : Raw.Expression C (suc n)) (z : Raw.Expression C n)
    (s : Raw.Expression C (suc (suc n))) (t : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Typed (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env) (suc l) M
        (Formers.universe l)
    → Stable (meaning z) X env
    → type-of (meaning z X env)
      ＝ meaning M (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env)
          [ id ⨾ zero [ ε X ] ]
    → Stable (meaning s)
        (X ▸ natural [ ε X ]
           ▸ meaning M (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env))
        (ext (meaning M (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env))
          (ext (natural [ ε X ]) env))
    → type-of
        (meaning s
          (X ▸ natural [ ε X ]
             ▸ meaning M (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env))
          (ext (meaning M (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env))
            (ext (natural [ ε X ]) env)))
      ＝ meaning M (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env)
          [ p ∘ p ⨾ successor (q (natural [ ε X ]) [ p ]) ]
    → Typed X env 0 t Formers.natural
    → Typed X env l (Formers.natural-induction l M z s t)
        (Formers.instantiate M t)
  induction-typed l M z s t X env TM sz tz ss ts Tt =
    let N = natural [ ε X ]
        M₀ = meaning M (X ▸ N) (ext N env)
        T = instance-as-type 0 l Formers.natural M t X env TM Tt
    in record
      { type-stable = term-stable T
      ; type-code = term-type T
      ; term-stable =
          induction-stable l M z s t X env (term-stable TM) (term-type TM) sz
            tz ss ts (term-stable Tt) (term-type Tt)
      ; term-type =
          ap type-of (induction-value l M z s t X env) ∙
            (natural-induction-type l M₀ (meaning z X env)
                (meaning s (X ▸ N ▸ M₀) (ext M₀ (ext N env)))
                (meaning t X env) (term-type TM) tz ts (term-type Tt) ∙
              instantiate-at 0 M t X N env (term-stable TM)
                  (term-stable Tt) (term-type Tt) (natural-code X) ⁻¹)
      }

  -- The types of the base and of the step, from the premises.
  base-type :
    {n : ℕ} (l : ℕ) (M : Raw.Expression C (suc n)) (z : Raw.Expression C n)
    (X : Ob) (env : Vec (Tm X) n)
    → Typed (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env) (suc l) M
        (Formers.universe l)
    → Typed X env l z (Formers.instantiate M Formers.zero)
    → type-of (meaning z X env)
      ＝ meaning M (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env)
          [ id ⨾ zero [ ε X ] ]
  base-type l M z X env TM Tz =
    term-type Tz ∙
      instantiate-at 0 M Formers.zero X (natural [ ε X ]) env
        (term-stable TM) (closed-stable zero X env) (zero-type-at X)
        (natural-code X)

  step-type :
    {n : ℕ} (l : ℕ) (M : Raw.Expression C (suc n))
    (s : Raw.Expression C (suc (suc n))) (X : Ob) (env : Vec (Tm X) n)
    → Typed (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env) (suc l) M
        (Formers.universe l)
    → Typed
        (X ▸ natural [ ε X ]
           ▸ meaning M (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env))
        (ext (meaning M (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env))
          (ext (natural [ ε X ]) env))
        l s (Block.next M)
    → type-of
        (meaning s
          (X ▸ natural [ ε X ]
             ▸ meaning M (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env))
          (ext (meaning M (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env))
            (ext (natural [ ε X ]) env)))
      ＝ meaning M (X ▸ natural [ ε X ]) (ext (natural [ ε X ]) env)
          [ p ∘ p ⨾ successor (q (natural [ ε X ]) [ p ]) ]
  step-type l M s X env TM Ts =
    term-type Ts ∙ next-value M X env (term-stable TM)

  -- The step's instance at t and r has the motive's type at the successor.
  next-instance-value :
    {n : ℕ} (M : Raw.Expression C (suc n)) (t r : Raw.Expression C n)
    (X : Ob) (env : Vec (Tm X) n)
    → Stable (meaning t) X env → type-of (meaning t X env) ＝ natural [ ε X ]
    → Stable (meaning r) X env
    → meaning (Formers.instantiate₂ (Block.next M) t r) X env
      ＝ meaning (Formers.instantiate M (Formers.successor t)) X env
  next-instance-value M t r X env st tt sr =
    let t′ = meaning t X env
        r′ = meaning r X env
    in instantiate₂-value (Block.next M) t r X env st sr ∙
         (instantiate-past-value 2 M
             (Formers.successor (Tree.hole (fsuc fzero))) X
             (r′ ∷ t′ ∷ env)
             (successor-stable (Tree.hole (fsuc fzero)) X (r′ ∷ t′ ∷ env)
               (Environment.stable-lookup R (fsuc fzero) X
                 (r′ ∷ t′ ∷ env))
               tt) ∙
           (ap (λ es → meaning M X (successor t′ ∷ es))
               (tabulate-lookup env) ∙
             instantiate-value M (Formers.successor t) X env
                 (successor-stable t X env st tt) ⁻¹))

  ----------------------------------------------------------------------
  -- The rules of ℕ

  sound :
    {j : Judgment C} (r : Block.Rule C j)
    → ((i : Fin (length (Block.premises r)))
       → Valid (list-lookup (Block.premises r) i))
    → Valid j
  sound (Block.formation Γ) h =
    h fzero , natural-typed (object Γ) (values Γ)
  sound (Block.zero-introduction Γ) h =
    h fzero , zero-typed (object Γ) (values Γ)
  sound (Block.successor-introduction Γ t) h =
    let (vΓ , Tt) = h fzero
    in vΓ , successor-typed t (object Γ) (values Γ) Tt
  sound (Block.elimination Γ l M z s t) h =
    let (_ , TM) = h fzero
        (vΓ , Tz) = h (fsuc fzero)
        (_ , Ts) = h (fsuc (fsuc fzero))
        (_ , Tt) = h (fsuc (fsuc (fsuc fzero)))
        X = object Γ
        env = values Γ
    in vΓ
       , induction-typed l M z s t X env TM (term-stable Tz)
           (base-type l M z X env TM Tz) (term-stable Ts)
           (step-type l M s X env TM Ts) Tt
  sound (Block.zero-computation Γ l M z s) h =
    let (_ , TM) = h fzero
        (vΓ , Tz) = h (fsuc fzero)
        (_ , Ts) = h (fsuc (fsuc fzero))
        X = object Γ
        env = values Γ
        N = natural [ ε X ]
        M₀ = meaning M (X ▸ N) (ext N env)
        tz = base-type l M z X env TM Tz
        ts = step-type l M s X env TM Ts
    in vΓ
       , induction-typed l M z s Formers.zero X env TM (term-stable Tz) tz
           (term-stable Ts) ts (zero-typed X env)
       , Tz
       , induction-value l M z s Formers.zero X env ∙
           natural-induction-zero l M₀ (meaning z X env)
             (meaning s (X ▸ N ▸ M₀) (ext M₀ (ext N env))) (term-type TM) tz
             ts
  sound (Block.successor-computation Γ l M z s t) h =
    let (_ , TM) = h fzero
        (vΓ , Tz) = h (fsuc fzero)
        (_ , Ts) = h (fsuc (fsuc fzero))
        (_ , Tt) = h (fsuc (fsuc (fsuc fzero)))
        X = object Γ
        env = values Γ
        N = natural [ ε X ]
        M₀ = meaning M (X ▸ N) (ext N env)
        s₀ = meaning s (X ▸ N ▸ M₀) (ext M₀ (ext N env))
        t′ = meaning t X env
        tz = base-type l M z X env TM Tz
        ts = step-type l M s X env TM Ts
        Rt = Formers.natural-induction l M z s t
        TR = induction-typed l M z s t X env TM (term-stable Tz) tz
               (term-stable Ts) ts Tt
        T = induction-typed l M z s (Formers.successor t) X env TM
              (term-stable Tz) tz (term-stable Ts) ts
              (successor-typed t X env Tt)
        tR = term-type TR ∙
               (instantiate-at 0 M t X N env (term-stable TM)
                   (term-stable Tt) (term-type Tt) (natural-code X) ∙
                 Environment.⨾-section R N t′ M₀ (term-type Tt) ⁻¹)
    in vΓ
       , T
       , retype X env l (Formers.instantiate₂ s t Rt)
           (Formers.instantiate M (Formers.successor t))
           (Formers.instantiate₂ (Block.next M) t Rt)
           (instance₂-typed l 0 l s (Block.next M) t Rt X N M₀ env Ts
             (term-stable Tt) (term-type Tt) (natural-code X) (term-stable TR)
             tR (term-type TM))
           (type-stable T) (type-code T)
           (next-instance-value M t Rt X env (term-stable Tt) (term-type Tt)
             (term-stable TR))
       , induction-value l M z s (Formers.successor t) X env ∙
           (natural-induction-successor l M₀ (meaning z X env) s₀ t′
               (term-type TM) tz ts (term-type Tt) ∙
             (ap (λ r → s₀ [ section R N t′ (term-type Tt) ⨾ r ])
                 (induction-value l M z s t X env ⁻¹) ∙
               instantiate₂-at 0 l s t Rt X N M₀ env (term-stable Ts)
                   (term-stable Tt) (term-stable TR) (term-type Tt)
                   (natural-code X) tR (term-type TM) ⁻¹))
  sound (Block.successor-introduction-equal Γ t t′) h =
    let (vΓ , Tt , Tt′ , et) = h fzero
        X = object Γ
        env = values Γ
    in vΓ
       , successor-typed t X env Tt
       , successor-typed t′ X env Tt′
       , ap successor et
  sound (Block.elimination-equal Γ l M M′ z z′ s s′ t t′) h =
    let (_ , TM , TM′ , eM) = h fzero
        (vΓ , Tz , Tz′ , ez) = h (fsuc fzero)
        (_ , Ts , Ts′ , es) = h (fsuc (fsuc fzero))
        (_ , Tt , Tt′ , et) = h (fsuc (fsuc (fsuc fzero)))
        X = object Γ
        env = values Γ
        N = natural [ ε X ]
        M₀ = meaning M (X ▸ N) (ext N env)
        TL = induction-typed l M z s t X env TM (term-stable Tz)
               (base-type l M z X env TM Tz) (term-stable Ts)
               (step-type l M s X env TM Ts) Tt
        tz′ = base-type l M z′ X env TM Tz′ ∙
                ap (λ u → u [ id ⨾ zero [ ε X ] ]) eM
        ss′ =
          transport (λ u → Stable (meaning s′) (X ▸ N ▸ u) (ext u (ext N env)))
                eM (term-stable Ts′)
        ts′ = transport
                (λ u → type-of (meaning s′ (X ▸ N ▸ u) (ext u (ext N env)))
                       ＝ u [ p ∘ p ⨾ successor (q N [ p ]) ])
                eM (step-type l M s′ X env TM Ts′)
    in vΓ
       , TL
       , retype X env l (Formers.natural-induction l M′ z′ s′ t′)
           (Formers.instantiate M t) (Formers.instantiate M′ t′)
           (induction-typed l M′ z′ s′ t′ X env TM′ (term-stable Tz′) tz′ ss′
             ts′ Tt′)
           (type-stable TL) (type-code TL)
           (instantiate-equal 0 Formers.natural Formers.natural M M′ t t′ X
               env (term-stable TM) (term-stable TM′) Tt Tt′ refl eM et ⁻¹)
       , induction-value l M z s t X env ∙
           (ap
               (λ u → natural-induction l M₀ (meaning z X env) u
                        (meaning t X env))
               es ∙
             (ap₂
                 (λ u v → natural-induction l M₀ u
                            (meaning s′ (X ▸ N ▸ M₀) (ext M₀ (ext N env))) v)
                 ez et ∙
               (ap
                   (λ u → natural-induction l u (meaning z′ X env)
                            (meaning s′ (X ▸ N ▸ u) (ext u (ext N env)))
                            (meaning t′ X env))
                   eM ∙
                 induction-value l M′ z′ s′ t′ X env ⁻¹)))
