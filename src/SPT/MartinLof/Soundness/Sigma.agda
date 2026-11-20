{-# OPTIONS --safe --without-K --no-projection-like #-}

module SPT.MartinLof.Soundness.Sigma where

-- Soundness of the rules of Σ (`sound`). The value of each Σ-former is
-- the model's operation at the values of its children, the second type
-- read at the extension by the first (`sigma-value`, `pair-value`,
-- `first-value`, `second-value`). It is stable by the stability laws
-- (`sigma-stable`, `pair-stable`, `first-stable`, `second-stable`) and has
-- its type by the typing laws (`sigma-typed`, `pair-typed`,
-- `first-typed`, `second-typed`). The computation rules and η are the
-- model's laws at these values; the congruences retype the primed side
-- along the equal values (`sigma-equal`, `pair-equal`, `first-equal`,
-- `second-equal`).

open import SPT.Base hiding (Lift; _∘_; id; lift; lower; zero)
import SPT.MartinLof.Formers as Formers
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Judgment using (Judgment)
import SPT.MartinLof.Rules.Sigma as Block
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
  (let instantiate-at = Instances.instantiate-at R lifting products pairs
                          paths trees nothing one sums numbers
                          operations subuniverses constant)
  (let as-type = Typing.as-type R lifting products pairs paths trees nothing
                   one sums numbers operations subuniverses constant)
  (let under-stable = Typing.under-stable R lifting products pairs paths
                        trees nothing one sums numbers operations subuniverses
                          constant)
  (let retype = Typing.retype R lifting products pairs paths trees nothing
                  one sums numbers operations subuniverses constant)
  (let typed-along = Typing.typed-along R lifting products pairs paths trees
                       nothing one sums numbers operations subuniverses
                         constant)
  (let instance-as-type = Typing.instance-as-type R lifting products pairs
                            paths trees nothing one sums numbers
                            operations subuniverses constant)
  (let instantiate-equal = Typing.instantiate-equal R lifting products pairs
                             paths trees nothing one sums numbers
                             operations subuniverses constant)
  (let type-stable = Interpretation.Typed.type-stable)
  (let type-code = Interpretation.Typed.type-code)
  (let term-stable = Interpretation.Typed.term-stable)
  (let term-type = Interpretation.Typed.term-type)
  where

  ----------------------------------------------------------------------
  -- Values

  sigma-value :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (X : Ob) (env : Vec (Tm X) n)
    → meaning (Formers.sigma m k A B) X env
      ＝ sigma m k (meaning A X env)
          (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
  sigma-value m k A B X env =
    ap (sigma m k (meaning A X env))
      (bound-meaning 1 B (X ▸ meaning A X env) (ext (meaning A X env) env))

  pair-value :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (x y : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → meaning (Formers.pair m k A B x y) X env
      ＝ pair m k (meaning A X env)
          (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
          (meaning x X env) (meaning y X env)
  pair-value m k A B x y X env =
    ap (λ b → pair m k (meaning A X env) b (meaning x X env)
                  (meaning y X env))
      (bound-meaning 1 B (X ▸ meaning A X env) (ext (meaning A X env) env))

  first-value :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (z : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → meaning (Formers.first m k A B z) X env
      ＝ first m k (meaning A X env)
          (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
          (meaning z X env)
  first-value m k A B z X env =
    ap (λ b → first m k (meaning A X env) b (meaning z X env))
      (bound-meaning 1 B (X ▸ meaning A X env) (ext (meaning A X env) env))

  second-value :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (z : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → meaning (Formers.second m k A B z) X env
      ＝ second m k (meaning A X env)
          (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
          (meaning z X env)
  second-value m k A B z X env =
    ap (λ b → second m k (meaning A X env) b (meaning z X env))
      (bound-meaning 1 B (X ▸ meaning A X env) (ext (meaning A X env) env))

  ----------------------------------------------------------------------
  -- Stability

  sigma-stable :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (X : Ob) (env : Vec (Tm X) n)
    → Stable (meaning A) X env → (cA : Code R m (meaning A X env))
    → Stable (meaning B) (X ▸ meaning A X env) (ext (meaning A X env) env)
    → Code R k (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
    → Stable (meaning (Formers.sigma m k A B)) X env
  sigma-stable m k A B X env sA cA sB cB Y τ =
    let a = meaning A X env
        b = meaning B (X ▸ a) (ext a env)
    in sigma-value m k A B Y (env [ τ ]ᵉ) ∙
         (ap (λ x → sigma m k x (meaning B (Y ▸ x) (ext x (env [ τ ]ᵉ))))
             (sA Y τ) ∙
           (ap (sigma m k (a [ τ ])) (under-stable m B X a env cA sB τ) ∙
             (sigma-[] m k a b τ cA cB ⁻¹ ∙
               ap (λ s → s [ τ ]) (sigma-value m k A B X env ⁻¹))))

  pair-stable :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (x y : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Stable (meaning A) X env → (cA : Code R m (meaning A X env))
    → Stable (meaning B) (X ▸ meaning A X env) (ext (meaning A X env) env)
    → Code R k (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
    → Stable (meaning x) X env → type-of (meaning x X env) ＝ meaning A X env
    → Stable (meaning y) X env
    → type-of (meaning y X env)
      ＝ meaning B (X ▸ meaning A X env) (ext (meaning A X env) env)
          [ id ⨾ meaning x X env ]
    → Stable (meaning (Formers.pair m k A B x y)) X env
  pair-stable m k A B x y X env sA cA sB cB sx tx sy ty Y τ =
    let a = meaning A X env
        b = meaning B (X ▸ a) (ext a env)
    in pair-value m k A B x y Y (env [ τ ]ᵉ) ∙
         (ap
             (λ z → pair m k z (meaning B (Y ▸ z) (ext z (env [ τ ]ᵉ)))
                      (meaning x Y (env [ τ ]ᵉ)) (meaning y Y (env [ τ ]ᵉ)))
             (sA Y τ) ∙
           (ap₃ (pair m k (a [ τ ]))
               (under-stable m B X a env cA sB τ) (sx Y τ) (sy Y τ) ∙
             (pair-[] m k a b (meaning x X env) (meaning y X env) τ cA
                      cB tx ty ⁻¹ ∙
               ap (λ s → s [ τ ]) (pair-value m k A B x y X env ⁻¹))))

  first-stable :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (z : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Stable (meaning A) X env → (cA : Code R m (meaning A X env))
    → Stable (meaning B) (X ▸ meaning A X env) (ext (meaning A X env) env)
    → Code R k (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
    → Stable (meaning z) X env
    → type-of (meaning z X env)
      ＝ sigma m k (meaning A X env)
          (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
    → Stable (meaning (Formers.first m k A B z)) X env
  first-stable m k A B z X env sA cA sB cB sz tz Y τ =
    let a = meaning A X env
        b = meaning B (X ▸ a) (ext a env)
    in first-value m k A B z Y (env [ τ ]ᵉ) ∙
         (ap
             (λ x → first m k x (meaning B (Y ▸ x) (ext x (env [ τ ]ᵉ)))
                      (meaning z Y (env [ τ ]ᵉ)))
             (sA Y τ) ∙
           (ap₂ (first m k (a [ τ ])) (under-stable m B X a env cA sB τ)
               (sz Y τ) ∙
             (first-[] m k a b (meaning z X env) τ cA cB tz ⁻¹ ∙
               ap (λ s → s [ τ ]) (first-value m k A B z X env ⁻¹))))

  second-stable :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (z : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Stable (meaning A) X env → (cA : Code R m (meaning A X env))
    → Stable (meaning B) (X ▸ meaning A X env) (ext (meaning A X env) env)
    → Code R k (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
    → Stable (meaning z) X env
    → type-of (meaning z X env)
      ＝ sigma m k (meaning A X env)
          (meaning B (X ▸ meaning A X env) (ext (meaning A X env) env))
    → Stable (meaning (Formers.second m k A B z)) X env
  second-stable m k A B z X env sA cA sB cB sz tz Y τ =
    let a = meaning A X env
        b = meaning B (X ▸ a) (ext a env)
    in second-value m k A B z Y (env [ τ ]ᵉ) ∙
         (ap
             (λ x → second m k x (meaning B (Y ▸ x) (ext x (env [ τ ]ᵉ)))
                      (meaning z Y (env [ τ ]ᵉ)))
             (sA Y τ) ∙
           (ap₂ (second m k (a [ τ ])) (under-stable m B X a env cA sB τ)
               (sz Y τ) ∙
             (second-[] m k a b (meaning z X env) τ cA cB tz ⁻¹ ∙
               ap (λ s → s [ τ ])
                 (second-value m k A B z X env ⁻¹))))

  ----------------------------------------------------------------------
  -- Typing

  sigma-typed :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (X : Ob) (env : Vec (Tm X) n)
    → Typed X env (suc m) A (Formers.universe m)
    → Typed (X ▸ meaning A X env) (ext (meaning A X env) env) (suc k) B
        (Formers.universe k)
    → Typed X env (suc (m ⊔ℕ k)) (Formers.sigma m k A B)
        (Formers.universe (m ⊔ℕ k))
  sigma-typed m k A B X env TA TB =
    let a = meaning A X env
        cA = term-type TA
        cB = term-type TB
    in as-type X env (m ⊔ℕ k) (Formers.sigma m k A B)
         (sigma-stable m k A B X env (term-stable TA) cA (term-stable TB) cB)
         (transport (Code R (m ⊔ℕ k)) (sigma-value m k A B X env ⁻¹)
           (sigma-type m k a (meaning B (X ▸ a) (ext a env)) cA cB))

  pair-typed :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (x y : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Typed X env (suc m) A (Formers.universe m)
    → Typed (X ▸ meaning A X env) (ext (meaning A X env) env) (suc k) B
        (Formers.universe k)
    → Typed X env m x A → Typed X env k y (Formers.instantiate B x)
    → Typed X env (m ⊔ℕ k) (Formers.pair m k A B x y) (Formers.sigma m k A B)
  pair-typed m k A B x y X env TA TB Tx Ty =
    let a = meaning A X env
        b = meaning B (X ▸ a) (ext a env)
        cA = term-type TA
        cB = term-type TB
        sx = term-stable Tx
        tx = term-type Tx
        ty = term-type Ty ∙
               instantiate-at m B x X a env (term-stable TB) sx tx cA
        T = sigma-typed m k A B X env TA TB
    in record
      { type-stable = term-stable T
      ; type-code = term-type T
      ; term-stable =
          pair-stable m k A B x y X env (term-stable TA) cA (term-stable TB)
            cB sx tx (term-stable Ty) ty
      ; term-type =
          ap type-of (pair-value m k A B x y X env) ∙
            (pair-type m k a b (meaning x X env) (meaning y X env) cA cB tx
                ty ∙
              sigma-value m k A B X env ⁻¹)
      }

  first-typed :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (z : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Typed X env (suc m) A (Formers.universe m)
    → Typed (X ▸ meaning A X env) (ext (meaning A X env) env) (suc k) B
        (Formers.universe k)
    → Typed X env (m ⊔ℕ k) z (Formers.sigma m k A B)
    → Typed X env m (Formers.first m k A B z) A
  first-typed m k A B z X env TA TB Tz =
    let a = meaning A X env
        cA = term-type TA
        cB = term-type TB
        tz = term-type Tz ∙ sigma-value m k A B X env
    in record
      { type-stable = term-stable TA
      ; type-code = cA
      ; term-stable =
          first-stable m k A B z X env (term-stable TA) cA (term-stable TB) cB
            (term-stable Tz) tz
      ; term-type =
          ap type-of (first-value m k A B z X env) ∙
            first-type m k a (meaning B (X ▸ a) (ext a env))
              (meaning z X env) cA cB tz
      }

  second-typed :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (z : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Typed X env (suc m) A (Formers.universe m)
    → Typed (X ▸ meaning A X env) (ext (meaning A X env) env) (suc k) B
        (Formers.universe k)
    → Typed X env (m ⊔ℕ k) z (Formers.sigma m k A B)
    → Typed X env k (Formers.second m k A B z)
        (Formers.instantiate B (Formers.first m k A B z))
  second-typed m k A B z X env TA TB Tz =
    let a = meaning A X env
        b = meaning B (X ▸ a) (ext a env)
        cA = term-type TA
        cB = term-type TB
        tz = term-type Tz ∙ sigma-value m k A B X env
        F = first-typed m k A B z X env TA TB Tz
        T = instance-as-type m k A B (Formers.first m k A B z) X env TB F
    in record
      { type-stable = term-stable T
      ; type-code = term-type T
      ; term-stable =
          second-stable m k A B z X env (term-stable TA) cA (term-stable TB)
            cB (term-stable Tz) tz
      ; term-type =
          ap type-of (second-value m k A B z X env) ∙
            (second-type m k a b (meaning z X env) cA cB tz ∙
              (ap (λ s → b [ id ⨾ s ])
                  (first-value m k A B z X env ⁻¹) ∙
                instantiate-at m B (Formers.first m k A B z) X a env
                    (term-stable TB) (term-stable F) (term-type F) cA ⁻¹))
      }

  ----------------------------------------------------------------------
  -- β and η

  first-pair-value :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (x y : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Typed X env (suc m) A (Formers.universe m)
    → Typed (X ▸ meaning A X env) (ext (meaning A X env) env) (suc k) B
        (Formers.universe k)
    → Typed X env m x A → Typed X env k y (Formers.instantiate B x)
    → meaning (Formers.first m k A B (Formers.pair m k A B x y)) X env
      ＝ meaning x X env
  first-pair-value m k A B x y X env TA TB Tx Ty =
    let a = meaning A X env
        b = meaning B (X ▸ a) (ext a env)
        cA = term-type TA
        tx = term-type Tx
        ty = term-type Ty ∙
               instantiate-at m B x X a env (term-stable TB) (term-stable Tx)
                 tx cA
    in first-value m k A B (Formers.pair m k A B x y) X env ∙
         (ap (first m k a b) (pair-value m k A B x y X env) ∙
           first-pair m k a b (meaning x X env) (meaning y X env) cA
             (term-type TB) tx ty)

  second-pair-value :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (x y : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Typed X env (suc m) A (Formers.universe m)
    → Typed (X ▸ meaning A X env) (ext (meaning A X env) env) (suc k) B
        (Formers.universe k)
    → Typed X env m x A → Typed X env k y (Formers.instantiate B x)
    → meaning (Formers.second m k A B (Formers.pair m k A B x y)) X env
      ＝ meaning y X env
  second-pair-value m k A B x y X env TA TB Tx Ty =
    let a = meaning A X env
        b = meaning B (X ▸ a) (ext a env)
        cA = term-type TA
        tx = term-type Tx
        ty = term-type Ty ∙
               instantiate-at m B x X a env (term-stable TB) (term-stable Tx)
                 tx cA
    in second-value m k A B (Formers.pair m k A B x y) X env ∙
         (ap (second m k a b) (pair-value m k A B x y X env) ∙
           second-pair m k a b (meaning x X env) (meaning y X env) cA
             (term-type TB) tx ty)

  projections-value :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (z : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → Typed X env (suc m) A (Formers.universe m)
    → Typed (X ▸ meaning A X env) (ext (meaning A X env) env) (suc k) B
        (Formers.universe k)
    → Typed X env (m ⊔ℕ k) z (Formers.sigma m k A B)
    → meaning
        (Formers.pair m k A B (Formers.first m k A B z)
          (Formers.second m k A B z)) X env
      ＝ meaning z X env
  projections-value m k A B z X env TA TB Tz =
    let a = meaning A X env
        b = meaning B (X ▸ a) (ext a env)
    in pair-value m k A B (Formers.first m k A B z)
           (Formers.second m k A B z) X env ∙
         (ap₂ (pair m k a b) (first-value m k A B z X env)
             (second-value m k A B z X env) ∙
           pair-projections m k a b (meaning z X env) (term-type TA)
             (term-type TB) (term-type Tz ∙ sigma-value m k A B X env))

  ----------------------------------------------------------------------
  -- Congruence

  sigma-equal :
    {n : ℕ} (m k : ℕ) (A A′ : Raw.Expression C n)
    (B B′ : Raw.Expression C (suc n)) (X : Ob) (env : Vec (Tm X) n)
    → meaning A X env ＝ meaning A′ X env
    → meaning B (X ▸ meaning A X env) (ext (meaning A X env) env)
      ＝ meaning B′ (X ▸ meaning A X env) (ext (meaning A X env) env)
    → meaning (Formers.sigma m k A B) X env
      ＝ meaning (Formers.sigma m k A′ B′) X env
  sigma-equal m k A A′ B B′ X env eA eB =
    sigma-value m k A B X env ∙
      (ap (sigma m k (meaning A X env)) eB ∙
        (ap (λ x → sigma m k x (meaning B′ (X ▸ x) (ext x env))) eA ∙
          sigma-value m k A′ B′ X env ⁻¹))

  pair-equal :
    {n : ℕ} (m k : ℕ) (A A′ : Raw.Expression C n)
    (B B′ : Raw.Expression C (suc n)) (x x′ y y′ : Raw.Expression C n)
    (X : Ob) (env : Vec (Tm X) n)
    → meaning A X env ＝ meaning A′ X env
    → meaning B (X ▸ meaning A X env) (ext (meaning A X env) env)
      ＝ meaning B′ (X ▸ meaning A X env) (ext (meaning A X env) env)
    → meaning x X env ＝ meaning x′ X env → meaning y X env ＝ meaning y′ X env
    → meaning (Formers.pair m k A B x y) X env
      ＝ meaning (Formers.pair m k A′ B′ x′ y′) X env
  pair-equal m k A A′ B B′ x x′ y y′ X env eA eB ex ey =
    pair-value m k A B x y X env ∙
      (ap₃ (pair m k (meaning A X env)) eB ex ey ∙
        (ap
            (λ z → pair m k z (meaning B′ (X ▸ z) (ext z env))
                     (meaning x′ X env) (meaning y′ X env))
            eA ∙
          pair-value m k A′ B′ x′ y′ X env ⁻¹))

  first-equal :
    {n : ℕ} (m k : ℕ) (A A′ : Raw.Expression C n)
    (B B′ : Raw.Expression C (suc n)) (z z′ : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → meaning A X env ＝ meaning A′ X env
    → meaning B (X ▸ meaning A X env) (ext (meaning A X env) env)
      ＝ meaning B′ (X ▸ meaning A X env) (ext (meaning A X env) env)
    → meaning z X env ＝ meaning z′ X env
    → meaning (Formers.first m k A B z) X env
      ＝ meaning (Formers.first m k A′ B′ z′) X env
  first-equal m k A A′ B B′ z z′ X env eA eB ez =
    first-value m k A B z X env ∙
      (ap₂ (first m k (meaning A X env)) eB ez ∙
        (ap
            (λ x → first m k x (meaning B′ (X ▸ x) (ext x env))
                     (meaning z′ X env))
            eA ∙
          first-value m k A′ B′ z′ X env ⁻¹))

  second-equal :
    {n : ℕ} (m k : ℕ) (A A′ : Raw.Expression C n)
    (B B′ : Raw.Expression C (suc n)) (z z′ : Raw.Expression C n) (X : Ob)
    (env : Vec (Tm X) n)
    → meaning A X env ＝ meaning A′ X env
    → meaning B (X ▸ meaning A X env) (ext (meaning A X env) env)
      ＝ meaning B′ (X ▸ meaning A X env) (ext (meaning A X env) env)
    → meaning z X env ＝ meaning z′ X env
    → meaning (Formers.second m k A B z) X env
      ＝ meaning (Formers.second m k A′ B′ z′) X env
  second-equal m k A A′ B B′ z z′ X env eA eB ez =
    second-value m k A B z X env ∙
      (ap₂ (second m k (meaning A X env)) eB ez ∙
        (ap
            (λ x → second m k x (meaning B′ (X ▸ x) (ext x env))
                     (meaning z′ X env))
            eA ∙
          second-value m k A′ B′ z′ X env ⁻¹))

  ----------------------------------------------------------------------
  -- The rules of Σ

  sound :
    {j : Judgment C} (r : Block.Rule C j)
    → ((i : Fin (length (Block.premises r)))
       → Valid (list-lookup (Block.premises r) i))
    → Valid j
  sound (Block.formation Γ m k A B) h =
    let (vΓ , TA) = h fzero
        (_ , TB) = h (fsuc fzero)
    in vΓ , sigma-typed m k A B (object Γ) (values Γ) TA TB
  sound (Block.introduction Γ m k A B a b) h =
    let (vΓ , TA) = h fzero
        (_ , TB) = h (fsuc fzero)
        (_ , Ta) = h (fsuc (fsuc fzero))
        (_ , Tb) = h (fsuc (fsuc (fsuc fzero)))
    in vΓ , pair-typed m k A B a b (object Γ) (values Γ) TA TB Ta Tb
  sound (Block.first-projection Γ m k A B z) h =
    let (vΓ , TA) = h fzero
        (_ , TB) = h (fsuc fzero)
        (_ , Tz) = h (fsuc (fsuc fzero))
    in vΓ , first-typed m k A B z (object Γ) (values Γ) TA TB Tz
  sound (Block.second-projection Γ m k A B z) h =
    let (vΓ , TA) = h fzero
        (_ , TB) = h (fsuc fzero)
        (_ , Tz) = h (fsuc (fsuc fzero))
    in vΓ , second-typed m k A B z (object Γ) (values Γ) TA TB Tz
  sound (Block.first-computation Γ m k A B a b) h =
    let (vΓ , TA) = h fzero
        (_ , TB) = h (fsuc fzero)
        (_ , Ta) = h (fsuc (fsuc fzero))
        (_ , Tb) = h (fsuc (fsuc (fsuc fzero)))
        X = object Γ
        env = values Γ
    in vΓ
       , first-typed m k A B (Formers.pair m k A B a b) X env TA TB
           (pair-typed m k A B a b X env TA TB Ta Tb)
       , Ta
       , first-pair-value m k A B a b X env TA TB Ta Tb
  sound (Block.second-computation Γ m k A B a b) h =
    let (vΓ , TA) = h fzero
        (_ , TB) = h (fsuc fzero)
        (_ , Ta) = h (fsuc (fsuc fzero))
        (_ , Tb) = h (fsuc (fsuc (fsuc fzero)))
        X = object Γ
        env = values Γ
        P = Formers.pair m k A B a b
        TP = pair-typed m k A B a b X env TA TB Ta Tb
        TF = first-typed m k A B P X env TA TB TP
    in vΓ
       , retype X env k (Formers.second m k A B P) (Formers.instantiate B a)
           (Formers.instantiate B (Formers.first m k A B P))
           (second-typed m k A B P X env TA TB TP)
           (type-stable Tb) (type-code Tb)
           (instantiate-equal m A A B B (Formers.first m k A B P) a X env
             (term-stable TB) (term-stable TB) TF Ta refl refl
             (first-pair-value m k A B a b X env TA TB Ta Tb))
       , Tb
       , second-pair-value m k A B a b X env TA TB Ta Tb
  sound (Block.uniqueness Γ m k A B z) h =
    let (vΓ , TA) = h fzero
        (_ , TB) = h (fsuc fzero)
        (_ , Tz) = h (fsuc (fsuc fzero))
        X = object Γ
        env = values Γ
    in vΓ
       , pair-typed m k A B (Formers.first m k A B z)
           (Formers.second m k A B z) X env TA TB
           (first-typed m k A B z X env TA TB Tz)
           (second-typed m k A B z X env TA TB Tz)
       , Tz
       , projections-value m k A B z X env TA TB Tz
  sound (Block.formation-equal Γ m k A A′ B B′) h =
    let (vΓ , TA , TA′ , eA) = h fzero
        (_ , TB , TB′ , eB) = h (fsuc fzero)
        X = object Γ
        env = values Γ
    in vΓ
       , sigma-typed m k A B X env TA TB
       , sigma-typed m k A′ B′ X env TA′
           (typed-along X env (suc k) B′ (Formers.universe k) eA TB′)
       , sigma-equal m k A A′ B B′ X env eA eB
  sound (Block.introduction-equal Γ m k A A′ B B′ a a′ b b′) h =
    let (vΓ , TA , TA′ , eA) = h fzero
        (_ , TB , TB′ , eB) = h (fsuc fzero)
        (_ , Ta , Ta′ , ea) = h (fsuc (fsuc fzero))
        (_ , Tb , Tb′ , eb) = h (fsuc (fsuc (fsuc fzero)))
        X = object Γ
        env = values Γ
        TB″ = typed-along X env (suc k) B′ (Formers.universe k) eA TB′
        Ta″ = retype X env m a′ A′ A Ta′ (term-stable TA′) (term-type TA′) eA
        TI′ = instance-as-type m k A′ B′ a′ X env TB″ Ta″
        Tb″ = retype X env k b′ (Formers.instantiate B′ a′)
                (Formers.instantiate B a) Tb′ (term-stable TI′)
                (term-type TI′)
                (instantiate-equal m A A′ B B′ a a′ X env (term-stable TB)
                  (term-stable TB″) Ta Ta″ eA eB ea)
        TS = sigma-typed m k A B X env TA TB
    in vΓ
       , pair-typed m k A B a b X env TA TB Ta Tb
       , retype X env (m ⊔ℕ k) (Formers.pair m k A′ B′ a′ b′)
           (Formers.sigma m k A B) (Formers.sigma m k A′ B′)
           (pair-typed m k A′ B′ a′ b′ X env TA′ TB″ Ta″ Tb″)
           (term-stable TS) (term-type TS)
           (sigma-equal m k A A′ B B′ X env eA eB ⁻¹)
       , pair-equal m k A A′ B B′ a a′ b b′ X env eA eB ea eb
  sound (Block.first-projection-equal Γ m k A A′ B B′ z z′) h =
    let (vΓ , TA , TA′ , eA) = h fzero
        (_ , TB , TB′ , eB) = h (fsuc fzero)
        (_ , Tz , Tz′ , ez) = h (fsuc (fsuc fzero))
        X = object Γ
        env = values Γ
        TB″ = typed-along X env (suc k) B′ (Formers.universe k) eA TB′
        TS′ = sigma-typed m k A′ B′ X env TA′ TB″
        Tz″ = retype X env (m ⊔ℕ k) z′ (Formers.sigma m k A′ B′)
                (Formers.sigma m k A B) Tz′ (term-stable TS′) (term-type TS′)
                (sigma-equal m k A A′ B B′ X env eA eB)
    in vΓ
       , first-typed m k A B z X env TA TB Tz
       , retype X env m (Formers.first m k A′ B′ z′) A A′
           (first-typed m k A′ B′ z′ X env TA′ TB″ Tz″)
           (term-stable TA) (term-type TA) (eA ⁻¹)
       , first-equal m k A A′ B B′ z z′ X env eA eB ez
  sound (Block.second-projection-equal Γ m k A A′ B B′ z z′) h =
    let (vΓ , TA , TA′ , eA) = h fzero
        (_ , TB , TB′ , eB) = h (fsuc fzero)
        (_ , Tz , Tz′ , ez) = h (fsuc (fsuc fzero))
        X = object Γ
        env = values Γ
        TB″ = typed-along X env (suc k) B′ (Formers.universe k) eA TB′
        TS′ = sigma-typed m k A′ B′ X env TA′ TB″
        Tz″ = retype X env (m ⊔ℕ k) z′ (Formers.sigma m k A′ B′)
                (Formers.sigma m k A B) Tz′ (term-stable TS′) (term-type TS′)
                (sigma-equal m k A A′ B B′ X env eA eB)
        TF = first-typed m k A B z X env TA TB Tz
        TF′ = first-typed m k A′ B′ z′ X env TA′ TB″ Tz″
        TL = second-typed m k A B z X env TA TB Tz
    in vΓ
       , TL
       , retype X env k (Formers.second m k A′ B′ z′)
           (Formers.instantiate B (Formers.first m k A B z))
           (Formers.instantiate B′ (Formers.first m k A′ B′ z′))
           (second-typed m k A′ B′ z′ X env TA′ TB″ Tz″)
           (type-stable TL) (type-code TL)
           (instantiate-equal m A A′ B B′ (Formers.first m k A B z)
               (Formers.first m k A′ B′ z′) X env (term-stable TB)
               (term-stable TB″) TF TF′ eA eB
               (first-equal m k A A′ B B′ z z′ X env eA eB ez) ⁻¹)
       , second-equal m k A A′ B B′ z z′ X env eA eB ez
