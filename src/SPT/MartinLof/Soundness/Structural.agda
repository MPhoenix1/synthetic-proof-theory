{-# OPTIONS --safe --without-K --no-projection-like #-}

module SPT.MartinLof.Soundness.Structural where

-- Soundness of the structural rules (`sound`): the empty and extended
-- contexts, variables (Instances' `variable-typed`), conversion of terms
-- and of equal terms, and reflexivity, symmetry and transitivity of
-- equal terms. For the extensional rule: meanings equal at every point
-- carry stability (`stable-pointwise`, `typed-pointwise`); related
-- contexts have equal interpretations (`context-meaning-rel`) and
-- validity (`valid-context-rel`); so related judgments are valid together
-- (`valid-rel`).

open import SPT.Base hiding (Lift; _∘_; id; lift; lower; zero)
import SPT.MartinLof.Formers as Formers
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Judgment using
  (Context; Judgment; Context-Rel; Judgment-Rel; empty-rel; extend-rel
  ; context-rel; term-rel; term-equal-rel)
import SPT.MartinLof.Structural as Block
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
open import SPT.MartinLof.Model.WellFounded using (WellFounded)
import SPT.MartinLof.Soundness.Environment as Environment
import SPT.MartinLof.Soundness.Instances as Instances
import SPT.MartinLof.Soundness.Interpretation as Interpretation
import SPT.MartinLof.Soundness.Transport as Transport
import SPT.Base.Universes as Universes

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
  (let Valid = Interpretation.Valid R lifting products pairs paths trees
                 nothing one sums numbers operations subuniverses constant)
  (let meaning-rel = Transport.meaning-rel R lifting products pairs paths
                       trees nothing one sums numbers operations subuniverses
                         constant)
  (let variable-typed = Instances.variable-typed R lifting products pairs
                          paths trees nothing one sums numbers
                          operations subuniverses constant)
  where

  ----------------------------------------------------------------------
  -- The extensional rule

  stable-pointwise :
    {k : ℕ} (μ μ′ : (Y : Ob) → Vec (Tm Y) k → Tm Y)
    → ((Y : Ob) (env′ : Vec (Tm Y) k) → μ Y env′ ＝ μ′ Y env′)
    → (X : Ob) (env : Vec (Tm X) k) → Stable μ X env → Stable μ′ X env
  stable-pointwise μ μ′ e X env s Y τ =
    e Y (env [ τ ]ᵉ) ⁻¹ ∙
      (s Y τ ∙ ap (λ t → t [ τ ]) (e X env))

  typed-pointwise :
    {n : ℕ} {t t′ A A′ : Raw.Expression C n} (X : Ob) (env : Vec (Tm X) n)
    (l : ℕ)
    → ((Y : Ob) (env′ : Vec (Tm Y) n) → meaning t Y env′ ＝ meaning t′ Y env′)
    → ((Y : Ob) (env′ : Vec (Tm Y) n) → meaning A Y env′ ＝ meaning A′ Y env′)
    → Typed X env l t A → Typed X env l t′ A′
  typed-pointwise {t = t} {t′} {A} {A′} X env l et eA T = record
    { type-stable =
        stable-pointwise (meaning A) (meaning A′) eA X env
          (Interpretation.Typed.type-stable T)
    ; type-code =
      transport (Code R l) (eA X env) (Interpretation.Typed.type-code T)
    ; term-stable =
        stable-pointwise (meaning t) (meaning t′) et X env
          (Interpretation.Typed.term-stable T)
    ; term-type =
        ap type-of (et X env ⁻¹) ∙
          (Interpretation.Typed.term-type T ∙ eA X env)
    }

  context-meaning-rel :
    {n : ℕ} {Γ Δ : Context C n} → Context-Rel Γ Δ
    → _＝_ {A = Σ Ob (λ X → Vec (Tm X) n)} (object Γ , values Γ)
        (object Δ , values Δ)
  context-meaning-rel empty-rel = refl
  context-meaning-rel (extend-rel {Γ = Γ} {B = B} cr r) =
    ap (λ x → object Γ ▸ x , ext x (values Γ))
        (meaning-rel r (object Γ) (values Γ)) ∙
      ap
        (λ s → pr₁ s ▸ meaning B (pr₁ s) (pr₂ s)
             , ext (meaning B (pr₁ s) (pr₂ s)) (pr₂ s))
        (context-meaning-rel cr)

  valid-context-rel :
    {n : ℕ} {Γ Δ : Context C n} → Context-Rel Γ Δ
    → valid-context Γ → valid-context Δ
  valid-context-rel empty-rel v = v
  valid-context-rel (extend-rel {l = l} {Γ = Γ} {A = A} {B = B} cr r)
    (vΓ , sA , cA) =
    valid-context-rel cr vΓ
    , transport (λ s → Stable (meaning B) (pr₁ s) (pr₂ s))
        (context-meaning-rel cr)
        (stable-pointwise (meaning A) (meaning B) (meaning-rel r)
          (object Γ) (values Γ) sA)
    , transport (λ s → Code R l (meaning B (pr₁ s) (pr₂ s)))
        (context-meaning-rel cr)
        (transport (Code R l) (meaning-rel r (object Γ) (values Γ)) cA)

  valid-rel : {j j′ : Judgment C} → Judgment-Rel j j′ → Valid j → Valid j′
  valid-rel (context-rel cr) v = valid-context-rel cr v
  valid-rel (term-rel {l = l} {Γ = Γ} {t′ = t′} {A′ = A′} cr rt rA) (vΓ , T) =
    valid-context-rel cr vΓ
    , transport (λ s → Typed (pr₁ s) (pr₂ s) l t′ A′)
        (context-meaning-rel cr)
        (typed-pointwise (object Γ) (values Γ) l (meaning-rel rt)
          (meaning-rel rA) T)
  valid-rel
    (term-equal-rel {l = l} {Γ = Γ} {t′ = t′} {u′ = u′} {A′ = A′} cr rt ru rA)
    (vΓ , Tt , Tu , e) =
    valid-context-rel cr vΓ
    , transport (λ s → Typed (pr₁ s) (pr₂ s) l t′ A′)
        (context-meaning-rel cr)
        (typed-pointwise (object Γ) (values Γ) l (meaning-rel rt)
          (meaning-rel rA) Tt)
    , transport (λ s → Typed (pr₁ s) (pr₂ s) l u′ A′)
        (context-meaning-rel cr)
        (typed-pointwise (object Γ) (values Γ) l (meaning-rel ru)
          (meaning-rel rA) Tu)
    , transport
        (λ s → meaning t′ (pr₁ s) (pr₂ s) ＝ meaning u′ (pr₁ s) (pr₂ s))
        (context-meaning-rel cr)
        (meaning-rel rt (object Γ) (values Γ) ⁻¹ ∙
          (e ∙ meaning-rel ru (object Γ) (values Γ)))

  ----------------------------------------------------------------------
  -- Conversion along equal types

  convert :
    {n : ℕ} (X : Ob) (env : Vec (Tm X) n) (l : ℕ)
    (t A B : Raw.Expression C n)
    → Typed X env l t A → Typed X env (suc l) B (Formers.universe l)
    → meaning A X env ＝ meaning B X env → Typed X env l t B
  convert X env l t A B Tt TB e = record
    { type-stable = Interpretation.Typed.term-stable TB
    ; type-code = Interpretation.Typed.term-type TB
    ; term-stable = Interpretation.Typed.term-stable Tt
    ; term-type = Interpretation.Typed.term-type Tt ∙ e
    }

  ----------------------------------------------------------------------
  -- The structural rules

  sound :
    {j : Judgment C} (r : Block.Rule C j)
    → ((i : Fin (length (Block.premises r)))
       → Valid (list-lookup (Block.premises r) i))
    → Valid j
  sound Block.empty h = Universes.lift ⋆
  sound (Block.extend Γ l A) h =
    pr₁ (h fzero)
    , Interpretation.Typed.term-stable (pr₂ (h fzero))
    , Interpretation.Typed.term-type (pr₂ (h fzero))
  sound (Block.assumption Γ i) h = h fzero , variable-typed Γ (h fzero) i
  sound (Block.conversion Γ l t A B) h =
    let (vΓ , Tt) = h fzero
        (_ , TA , TB , e) = h (fsuc fzero)
    in vΓ , convert (object Γ) (values Γ) l t A B Tt TB e
  sound (Block.equal-conversion Γ l t u A B) h =
    let (vΓ , Tt , Tu , e) = h fzero
        (_ , TA , TB , eAB) = h (fsuc fzero)
    in vΓ
       , convert (object Γ) (values Γ) l t A B Tt TB eAB
       , convert (object Γ) (values Γ) l u A B Tu TB eAB
       , e
  sound (Block.reflexive Γ l t A) h =
    let (vΓ , T) = h fzero in vΓ , T , T , refl
  sound (Block.symmetric Γ l t u A) h =
    let (vΓ , Tt , Tu , e) = h fzero in vΓ , Tu , Tt , e ⁻¹
  sound (Block.transitive Γ l t u v A) h =
    let (vΓ , Tt , Tu , e₁) = h fzero
        (_ , _ , Tv , e₂) = h (fsuc fzero)
    in vΓ , Tt , Tv , e₁ ∙ e₂
  sound (Block.extensional j r) h = valid-rel r (h fzero)
