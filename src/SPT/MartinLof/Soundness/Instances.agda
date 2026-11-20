{-# OPTIONS --safe --without-K --no-projection-like #-}

module SPT.MartinLof.Soundness.Instances where

-- The values of the syntactic operations the rules of the core theory
-- use, and their stability.
--
-- A substitution instance is stable when what is substituted is stable
-- and the expression is stable at their values (`substitute-stable`;
-- `extended-stable`). A renaming reads the environment through it
-- (`rename-value`); weakening reads it past its newest entry
-- (`weaken-value`, `weaken-ext`, `weaken-stable`, `weaken-at`). A closed
-- expression is read in the empty environment (`closed-value`).
-- Replacing the last one, two or three variables adds their values to
-- the environment (`instantiate-value`, `instantiate₂-value`,
-- `instantiate₃-value`), also under further variables
-- (`instantiate-past-value`). At an extension by a type a, the instance
-- at a term of type a is the value at the extension with its last
-- variable replaced (`instantiate-at`), and it is stable
-- (`instantiate-stable`). A variable of a valid context has the type its
-- entry gives it (`variable-typed`).

open import SPT.Base hiding (Lift; _∘_; id; lift; lower; zero)
open import SPT.Foundation.Vectors.Tabulation using
  (tabulate; tabulate-cong; tabulate-lookup; tabulate-∘)
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Tree as Tree
import SPT.Foundation.Tree.Binding as Binding
import SPT.Foundation.Tree.Binding.Laws as Laws
import SPT.MartinLof.Formers as Formers
import SPT.MartinLof.Judgment as Judgment
open import SPT.MartinLof.Judgment using (Context; ∅; _▸[_]_; level)
import SPT.MartinLof.Raw as Raw
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
open import SPT.MartinLof.Model.WellFounded using (WellFounded)
import SPT.MartinLof.Soundness.Environment as Environment
import SPT.MartinLof.Soundness.Interpretation as Interpretation
import SPT.MartinLof.Soundness.Transport as Transport

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
  (let valid-context = Interpretation.valid-context R lifting products pairs
                         paths trees nothing one sums numbers
                         operations subuniverses constant)
  (let Typed = Interpretation.Typed R lifting products pairs paths trees
                 nothing one sums numbers operations subuniverses constant)
  (let meaning-rel = Transport.meaning-rel R lifting products pairs paths
                       trees nothing one sums numbers operations subuniverses
                         constant)
  (let substitute-meaning = Transport.substitute-meaning R lifting products
                              pairs paths trees nothing one sums numbers
                              operations subuniverses constant)
  where

  ----------------------------------------------------------------------
  -- Substitution instances

  -- Variables, and a substitution extended by a stable term, are stable.
  extended-stable :
    {k m : ℕ} (σ : Fin k → Raw.Expression C m) (e : Raw.Expression C m)
    (X : Ob) (env : Vec (Tm X) m)
    → ((i : Fin k) → Stable (meaning (σ i)) X env)
    → Stable (meaning e) X env
    → (i : Fin (suc k)) → Stable (meaning (Formers.extended σ e i)) X env
  extended-stable σ e X env sσ se fzero = se
  extended-stable σ e X env sσ se (fsuc i) = sσ i

  substitute-stable :
    {k m : ℕ} (σ : Fin k → Raw.Expression C m) (M : Raw.Expression C k)
    (X : Ob) (env : Vec (Tm X) m)
    → ((i : Fin k) → Stable (meaning (σ i)) X env)
    → Stable (meaning M) X (tabulate (λ i → meaning (σ i) X env))
    → Stable (meaning (Binding.substitute (Raw.binding C) m σ M)) X env
  substitute-stable σ M X env sσ sM Y τ =
    substitute-meaning σ M Y (env [ τ ]ᵉ)
        (λ i → Environment.stable-[] R (meaning (σ i)) X env (sσ i) τ) ∙
      (ap (meaning M Y)
          (tabulate-cong (λ i → sσ i Y τ) ∙
            tabulate-∘ (λ t → t [ τ ]) (λ i → meaning (σ i) X env)) ∙
        (sM Y τ ∙
          ap (λ t → t [ τ ]) (substitute-meaning σ M X env sσ ⁻¹)))

  ----------------------------------------------------------------------
  -- Renaming, weakening and closed expressions

  -- A renaming reads the environment through it.
  rename-value :
    {n m : ℕ} (ρ : Fin n → Fin m) (e : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) m)
    → meaning (Binding.rename (Raw.binding C) ρ e) X env
      ＝ meaning e X (tabulate (λ i → vector-lookup env (ρ i)))
  rename-value ρ e X env =
    meaning-rel (Laws.rename-substitute-rel (Raw.binding C) ρ e) X env ∙
      substitute-meaning (λ i → Tree.hole (ρ i)) e X env
        (λ i → Environment.stable-lookup R (ρ i) X env)

  weaken-value :
    {n : ℕ} (e : Raw.Expression C n) (X : Ob) (env : Vec (Tm X) (suc n))
    → meaning (Formers.weaken e) X env
      ＝ meaning e X (tabulate (λ i → vector-lookup env (fsuc i)))
  weaken-value e X env =
    meaning-rel (Laws.rename-substitute-rel (Raw.binding C) fsuc e)
             X env ∙
      substitute-meaning (λ i → Tree.hole (fsuc i)) e X env
        (λ i → Environment.stable-lookup R (fsuc i) X env)

  weaken-ext :
    {n : ℕ} (e : Raw.Expression C n) (X : Ob) (a : Tm X)
    (env : Vec (Tm X) n)
    → meaning (Formers.weaken e) (X ▸ a) (ext a env)
      ＝ meaning e (X ▸ a) (env [ p ]ᵉ)
  weaken-ext e X a env =
    weaken-value e (X ▸ a) (ext a env) ∙
      ap (meaning e (X ▸ a)) (tabulate-lookup (env [ p ]ᵉ))

  weaken-stable :
    {n : ℕ} (e : Raw.Expression C n) (X : Ob) (a : Tm X)
    (env : Vec (Tm X) n)
    → Stable (meaning e) X env
    → Stable (meaning (Formers.weaken e)) (X ▸ a) (ext a env)
  weaken-stable e X a env s Y τ =
    weaken-value e Y (ext a env [ τ ]ᵉ) ∙
      (ap (meaning e Y) (tabulate-lookup (env [ p ]ᵉ [ τ ]ᵉ)) ∙
        (Environment.stable-[] R (meaning e) X env s p Y τ ∙
          ap (λ t → t [ τ ]) (weaken-ext e X a env ⁻¹)))

  -- The value of weakening at an extension, for a stable expression.
  weaken-at :
    {n : ℕ} (e : Raw.Expression C n) (X : Ob) (a : Tm X)
    (env : Vec (Tm X) n)
    → Stable (meaning e) X env
    → meaning (Formers.weaken e) (X ▸ a) (ext a env) ＝ meaning e X env [ p ]
  weaken-at e X a env s = weaken-ext e X a env ∙ s (X ▸ a) p

  closed-value :
    {n : ℕ} (T : Raw.Expression C 0) (X : Ob) (env : Vec (Tm X) n)
    → meaning (Formers.closed n T) X env ＝ meaning T X []
  closed-value {n} T X env =
    meaning-rel
        (Laws.rename-substitute-rel (Raw.binding C) (λ (i : Fin 0) → i ↑ˡ n) T)
        X env ∙
      substitute-meaning (λ i → Tree.hole (i ↑ˡ n)) T X env (λ ())

  ----------------------------------------------------------------------
  -- Replacing the last variables

  instantiate-value :
    {n : ℕ} (M : Raw.Expression C (suc n)) (e : Raw.Expression C n)
    (X : Ob) (env : Vec (Tm X) n)
    → Stable (meaning e) X env
    → meaning (Formers.instantiate M e) X env
      ＝ meaning M X (meaning e X env ∷ env)
  instantiate-value {n} M e X env se =
    substitute-meaning (Formers.extended (λ (i : Fin n) → Tree.hole i) e)
        M X env
        (extended-stable (λ (i : Fin n) → Tree.hole i) e X env
          (λ i → Environment.stable-lookup R i X env) se) ∙
      ap (λ es → meaning M X (meaning e X env ∷ es)) (tabulate-lookup env)

  instantiate₂-value :
    {n : ℕ} (M : Raw.Expression C (suc (suc n))) (a b : Raw.Expression C n)
    (X : Ob) (env : Vec (Tm X) n)
    → Stable (meaning a) X env → Stable (meaning b) X env
    → meaning (Formers.instantiate₂ M a b) X env
      ＝ meaning M X (meaning b X env ∷ meaning a X env ∷ env)
  instantiate₂-value {n} M a b X env sa sb =
    substitute-meaning
        (Formers.extended
          (Formers.extended (λ (i : Fin n) → Tree.hole i) a) b)
        M X env
        (extended-stable
          (Formers.extended (λ (i : Fin n) → Tree.hole i) a) b X env
          (extended-stable (λ (i : Fin n) → Tree.hole i) a X env
            (λ i → Environment.stable-lookup R i X env) sa)
          sb) ∙
      ap (λ es → meaning M X (meaning b X env ∷ meaning a X env ∷ es))
        (tabulate-lookup env)

  instantiate₃-value :
    {n : ℕ} (M : Raw.Expression C (suc (suc (suc n))))
    (a b c : Raw.Expression C n) (X : Ob) (env : Vec (Tm X) n)
    → Stable (meaning a) X env → Stable (meaning b) X env
    → Stable (meaning c) X env
    → meaning (Formers.instantiate₃ M a b c) X env
      ＝ meaning M X
          (meaning c X env ∷ meaning b X env ∷ meaning a X env ∷ env)
  instantiate₃-value {n} M a b c X env sa sb sc =
    substitute-meaning
        (Formers.extended
          (Formers.extended
            (Formers.extended (λ (i : Fin n) → Tree.hole i) a) b) c)
        M X env
        (extended-stable
          (Formers.extended
            (Formers.extended (λ (i : Fin n) → Tree.hole i) a) b) c X env
          (extended-stable
            (Formers.extended (λ (i : Fin n) → Tree.hole i) a) b X env
            (extended-stable (λ (i : Fin n) → Tree.hole i) a X env
              (λ i → Environment.stable-lookup R i X env) sa)
            sb)
          sc) ∙
      ap
        (λ es → meaning M X
          (meaning c X env ∷ meaning b X env ∷ meaning a X env ∷ es))
        (tabulate-lookup env)

  instantiate-past-value :
    {n : ℕ} (d : ℕ) (M : Raw.Expression C (suc n))
    (e : Raw.Expression C (d + n)) (X : Ob) (env : Vec (Tm X) (d + n))
    → Stable (meaning e) X env
    → meaning (Formers.instantiate-past d M e) X env
      ＝ meaning M X (meaning e X env ∷ Environment.outer R d n env)
  instantiate-past-value {n} d M e X env se =
    substitute-meaning (Formers.extended (Formers.shifted n d) e) M X env
      (extended-stable (Formers.shifted n d) e X env
        (λ i → Environment.stable-lookup R (d ↑ʳ i) X env) se)

  ----------------------------------------------------------------------
  -- Instances at an extension

  instantiate-at :
    {n : ℕ} (l : ℕ) (M : Raw.Expression C (suc n)) (e : Raw.Expression C n)
    (X : Ob) (a : Tm X) (env : Vec (Tm X) n)
    → Stable (meaning M) (X ▸ a) (ext a env) → Stable (meaning e) X env
    → (tx : type-of (meaning e X env) ＝ a) → Code R l a
    → meaning (Formers.instantiate M e) X env
      ＝ meaning M (X ▸ a) (ext a env) [ id ⨾ meaning e X env ]
  instantiate-at l M e X a env sM se tx ta =
    instantiate-value M e X env se ∙
      (ap (meaning M X)
          (Environment.ext-section R l a (meaning e X env) env tx ta ⁻¹) ∙
        (sM X (section R a (meaning e X env) tx) ∙
          Environment.⨾-section R a (meaning e X env)
            (meaning M (X ▸ a) (ext a env)) tx))

  instantiate-stable :
    {n : ℕ} (l : ℕ) (M : Raw.Expression C (suc n)) (e : Raw.Expression C n)
    (X : Ob) (a : Tm X) (env : Vec (Tm X) n)
    → Stable (meaning M) (X ▸ a) (ext a env) → Stable (meaning e) X env
    → type-of (meaning e X env) ＝ a → Code R l a
    → Stable (meaning (Formers.instantiate M e)) X env
  instantiate-stable {n} l M e X a env sM se tx ta =
    substitute-stable (Formers.extended (λ (i : Fin n) → Tree.hole i) e) M X env
      (extended-stable (λ (i : Fin n) → Tree.hole i) e X env
        (λ i → Environment.stable-lookup R i X env) se)
      (transport (Stable (meaning M) X)
        (ap (λ es → meaning e X env ∷ es) (tabulate-lookup env ⁻¹))
        (Environment.stable-section R l (meaning M) a (meaning e X env) env
          tx ta sM))

  ----------------------------------------------------------------------
  -- Variables

  variable-typed :
    {n : ℕ} (Γ : Context C n) → valid-context Γ → (i : Fin n)
    → Typed (object Γ) (values Γ) (level Γ i) (Tree.hole i)
        (Judgment.lookup Γ i)
  variable-typed (Γ ▸[ l ] A) (vΓ , sA , cA) fzero =
    let a = meaning A (object Γ) (values Γ)
        e = weaken-at A (object Γ) a (values Γ) sA
    in record
      { type-stable = weaken-stable A (object Γ) a (values Γ) sA
      ; type-code = transport (Code R l) (e ⁻¹) (code-[] R l a p cA)
      ; term-stable =
          Environment.stable-lookup R fzero (object Γ ▸ a) (ext a (values Γ))
      ; term-type = q-type l a cA ∙ e ⁻¹
      }
  variable-typed (Γ ▸[ l ] A) (vΓ , sA , cA) (fsuc i) =
    let a = meaning A (object Γ) (values Γ)
        t = variable-typed Γ vΓ i
        B = Judgment.lookup Γ i
        sB = Interpretation.Typed.type-stable t
        e = weaken-at B (object Γ) a (values Γ) sB
    in record
      { type-stable = weaken-stable B (object Γ) a (values Γ) sB
      ; type-code =
          transport (Code R (level Γ i)) (e ⁻¹)
            (code-[] R (level Γ i) (meaning B (object Γ) (values Γ)) p
              (Interpretation.Typed.type-code t))
      ; term-stable =
          Environment.stable-lookup R (fsuc i) (object Γ ▸ a)
            (ext a (values Γ))
      ; term-type =
          ap type-of (Environment.lookup-[]ᵉ R (values Γ) p i) ∙
            (type-of-[] (vector-lookup (values Γ) i) p ∙
              (ap (λ x → x [ p ]) (Interpretation.Typed.term-type t) ∙
                e ⁻¹))
      }
