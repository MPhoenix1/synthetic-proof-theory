{-# OPTIONS --safe --without-K --no-projection-like #-}

module SPT.MartinLof.Soundness.Environment where

-- Environments over a Russell model, and the calculus of its substitutions
-- that the soundness of the core theory uses.
--
-- An environment over a context X lists terms over X, the values of the
-- variables in scope. It is substituted entrywise (`_[_]ᵉ`, with
-- `lookup-[]ᵉ`, `[]ᵉ-id`, `[]ᵉ-∘`), extended by the variable of an
-- extension (`ext`), and has an outer part past its first c entries
-- (`outer`, `outer-ext`).
--
-- A meaning gives a term at every context and environment. It is stable
-- at an environment when substituting the environment substitutes its
-- value, that is, it is natural there (`Stable`). Stability survives
-- substitution (`stable-[]`), and every variable is stable
-- (`stable-lookup`).
--
-- For a type a, substituting an extended environment along `extend`,
-- `under` or `section` gives the new variable's value followed by the
-- substituted environment (`ext-extend`, `ext-under`, `ext-section`); a
-- meaning stable at the extension is stable at each instance
-- (`stable-section`).
-- Replacing the last variable agrees with these substitutions (`⨾-under`,
-- `⨾-section`), and commutes with substitution (`extend-type`,
-- `extend-∘`, `⨾-[]`).
--
-- Every definition takes the model explicitly: a record variable left
-- implicit is split by Agda into one unknown per field, which unification
-- cannot solve. Other modules bind what they use once, by a let in their
-- section's telescope.

open import SPT.Base hiding (_∘_; id)
open import SPT.Foundation.Vectors.Tabulation using
  (lookup-vector-map; tabulate; tabulate-cong; tabulate-∘; vector-map
  ; vector-map-cong; vector-map-id; vector-map-∘)
open import SPT.MartinLof.Model.Russell using
  (Russell; Code; section; under; under-type)

module _ {ℓ : Level} (R : Russell ℓ) (let open Russell R) where

  infixl 25 _[_]ᵉ

  ----------------------------------------------------------------------
  -- Environments

  -- An environment substituted along τ, entrywise.
  _[_]ᵉ : {X Y : Ob} {k : ℕ} → Vec (Tm X) k → Hom Y X → Vec (Tm Y) k
  env [ τ ]ᵉ = vector-map (λ t → t [ τ ]) env

  lookup-[]ᵉ :
    {X Y : Ob} {k : ℕ} (env : Vec (Tm X) k) (τ : Hom Y X) (i : Fin k)
    → vector-lookup (env [ τ ]ᵉ) i ＝ vector-lookup env i [ τ ]
  lookup-[]ᵉ env τ i = lookup-vector-map i (λ t → t [ τ ]) env

  []ᵉ-id : {X : Ob} {k : ℕ} (env : Vec (Tm X) k) → env [ id ]ᵉ ＝ env
  []ᵉ-id env = vector-map-cong [id] env ∙ vector-map-id env

  []ᵉ-∘ :
    {X Y Z : Ob} {k : ℕ} (env : Vec (Tm X) k) (σ : Hom Y X) (τ : Hom Z Y)
    → env [ σ ∘ τ ]ᵉ ＝ env [ σ ]ᵉ [ τ ]ᵉ
  []ᵉ-∘ env σ τ =
    vector-map-cong (λ t → [∘] t σ τ) env ∙
      vector-map-∘ (λ t → t [ τ ]) (λ t → t [ σ ]) env

  -- The environment of the extension of X by a.
  ext : {X : Ob} (a : Tm X) {k : ℕ} → Vec (Tm X) k → Vec (Tm (X ▸ a)) (suc k)
  ext a env = q a ∷ env [ p ]ᵉ

  -- The entries of an environment past its first c.
  outer : {X : Ob} (c m : ℕ) → Vec (Tm X) (c + m) → Vec (Tm X) m
  outer c m env = tabulate (λ k → vector-lookup env (c ↑ʳ k))

  outer-ext :
    {X : Ob} (a : Tm X) (c m : ℕ) (env : Vec (Tm X) (c + m))
    → outer (suc c) m (ext a env) ＝ outer c m env [ p ]ᵉ
  outer-ext a c m env =
    tabulate-cong (λ k → lookup-[]ᵉ env p (c ↑ʳ k)) ∙
      tabulate-∘ (λ t → t [ p ]) (λ k → vector-lookup env (c ↑ʳ k))

  ----------------------------------------------------------------------
  -- Stability

  -- A meaning is stable at env when substituting env substitutes its
  -- value.
  Stable :
    {k : ℕ} → ((Y : Ob) → Vec (Tm Y) k → Tm Y) → (X : Ob) → Vec (Tm X) k
    → Set ℓ
  Stable μ X env = (Y : Ob) (τ : Hom Y X) → μ Y (env [ τ ]ᵉ) ＝ μ X env [ τ ]

  stable-[] :
    {k : ℕ} (μ : (Y : Ob) → Vec (Tm Y) k → Tm Y) (X : Ob)
    (env : Vec (Tm X) k)
    → Stable μ X env → {Y : Ob} (τ : Hom Y X) → Stable μ Y (env [ τ ]ᵉ)
  stable-[] μ X env N {Y} τ Z υ =
    ap (μ Z) ([]ᵉ-∘ env τ υ ⁻¹) ∙
      (N Z (τ ∘ υ) ∙
        ([∘] (μ X env) τ υ ∙ ap (λ t → t [ υ ]) (N Y τ ⁻¹)))

  stable-lookup :
    {k : ℕ} (i : Fin k) (X : Ob) (env : Vec (Tm X) k)
    → Stable (λ Y env′ → vector-lookup env′ i) X env
  stable-lookup i X env Y τ = lookup-[]ᵉ env τ i

  ----------------------------------------------------------------------
  -- Extending substitutions

  ext-extend :
    {X Y : Ob} {k : ℕ} (l : ℕ) (a : Tm X) (env : Vec (Tm X) k)
    (σ : Hom Y X) (t : Tm Y) (e : type-of t ＝ a [ σ ]) → Code R l a
    → ext a env [ extend a σ t e ]ᵉ ＝ t ∷ env [ σ ]ᵉ
  ext-extend l a env σ t e ta =
    ap₂ _∷_ (q-extend l a σ t e ta)
      ([]ᵉ-∘ env p (extend a σ t e) ⁻¹ ∙
        ap (λ ν → env [ ν ]ᵉ) (p-extend a σ t e))

  ext-under :
    {X Y : Ob} {k : ℕ} (l : ℕ) (a : Tm X) (env : Vec (Tm X) k)
    (τ : Hom Y X) (ta : Code R l a)
    → ext a env [ under R l a τ ta ]ᵉ ＝ ext (a [ τ ]) (env [ τ ]ᵉ)
  ext-under l a env τ ta =
    ext-extend l a env (τ ∘ p) (q (a [ τ ])) (under-type R l a τ ta) ta ∙
      ap (λ e → q (a [ τ ]) ∷ e) ([]ᵉ-∘ env τ p)

  ext-section :
    {X : Ob} {k : ℕ} (l : ℕ) (a x : Tm X) (env : Vec (Tm X) k)
    (tx : type-of x ＝ a) → Code R l a
    → ext a env [ section R a x tx ]ᵉ ＝ x ∷ env
  ext-section l a x env tx ta =
    ext-extend l a env id x (tx ∙ [id] a ⁻¹) ta ∙
      ap (λ e → x ∷ e) ([]ᵉ-id env)

  -- Stable at an extension by a type a: stable at every term of type a
  -- in place of the variable.
  stable-section :
    {X : Ob} {k : ℕ} (l : ℕ) (μ : (Y : Ob) → Vec (Tm Y) (suc k) → Tm Y)
    (a x : Tm X) (env : Vec (Tm X) k) (tx : type-of x ＝ a) → Code R l a
    → Stable μ (X ▸ a) (ext a env) → Stable μ X (x ∷ env)
  stable-section {X} l μ a x env tx ta s =
    transport (Stable μ X) (ext-section l a x env tx ta)
      (stable-[] μ (X ▸ a) (ext a env) s (section R a x tx))

  ----------------------------------------------------------------------
  -- Replacing the last variable

  ⨾-under :
    {X Y : Ob} (l : ℕ) (a : Tm X) (M : Tm (X ▸ a)) (τ : Hom Y X)
    (ta : Code R l a)
    → M [ under R l a τ ta ] ＝ M [ τ ∘ p ⨾ q (a [ τ ]) ]
  ⨾-under l a M τ ta =
    [⨾] a M (τ ∘ p) (q (a [ τ ])) (under-type R l a τ ta) ⁻¹

  ⨾-section :
    {X : Ob} (a x : Tm X) (M : Tm (X ▸ a)) (tx : type-of x ＝ a)
    → M [ section R a x tx ] ＝ M [ id ⨾ x ]
  ⨾-section a x M tx = [⨾] a M id x (tx ∙ [id] a ⁻¹) ⁻¹

  -- A term of type a [ σ ], substituted, has type a [ σ ∘ τ ].
  extend-type :
    {X Y Z : Ob} (a : Tm X) (σ : Hom Y X) (t : Tm Y) (τ : Hom Z Y)
    → type-of t ＝ a [ σ ] → type-of (t [ τ ]) ＝ a [ σ ∘ τ ]
  extend-type a σ t τ e =
    type-of-[] t τ ∙
      (ap (λ s → s [ τ ]) e ∙ [∘] a σ τ ⁻¹)

  extend-∘ :
    {X Y Z : Ob} (l : ℕ) (a : Tm X) (σ : Hom Y X) (t : Tm Y) (τ : Hom Z Y)
    (e : type-of t ＝ a [ σ ]) (e′ : type-of (t [ τ ]) ＝ a [ σ ∘ τ ])
    → Code R l a
    → extend a σ t e ∘ τ ＝ extend a (σ ∘ τ) (t [ τ ]) e′
  extend-∘ l a σ t τ e e′ ta =
    extend-unique a (extend a σ t e ∘ τ) (extend a (σ ∘ τ) (t [ τ ]) e′)
      (associative p (extend a σ t e) τ ⁻¹ ∙
        (ap (λ ν → ν ∘ τ) (p-extend a σ t e) ∙
          p-extend a (σ ∘ τ) (t [ τ ]) e′ ⁻¹))
      ([∘] (q a) (extend a σ t e) τ ∙
        (ap (λ s → s [ τ ]) (q-extend l a σ t e ta) ∙
          q-extend l a (σ ∘ τ) (t [ τ ]) e′ ta ⁻¹))

  ⨾-[] :
    {X Y Z : Ob} (l : ℕ) (a : Tm X) (M : Tm (X ▸ a)) (σ : Hom Y X)
    (t : Tm Y) (τ : Hom Z Y) → Code R l a → type-of t ＝ a [ σ ]
    → M [ σ ⨾ t ] [ τ ] ＝ M [ σ ∘ τ ⨾ t [ τ ] ]
  ⨾-[] l a M σ t τ ta e =
    ap (λ s → s [ τ ]) ([⨾] a M σ t e) ∙
      ([∘] M (extend a σ t e) τ ⁻¹ ∙
        (ap (λ ν → M [ ν ])
            (extend-∘ l a σ t τ e (extend-type a σ t τ e) ta) ∙
          [⨾] a M (σ ∘ τ) (t [ τ ]) (extend-type a σ t τ e) ⁻¹))
