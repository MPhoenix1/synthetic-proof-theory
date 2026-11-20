{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Impredicative.Realizability.Recursion where

-- Recursion in every partial combinatory algebra, with no further
-- constructor. fix f is Turing's fixed point guarded by an abstraction, so
-- it is a value and fix f · a evaluates as f · (fix f) · a (`fix-β`). Pairs
-- of values are read by k and second (`pair`, `pair-first`, `pair-second`)
-- and built by one element (`pair-maker`). `conditional` branches on a
-- value k or second. A numeral is a pair of a tag and a predecessor
-- (`Numeral`); `natural-recursor` and `tree-recursor` run a step over a
-- pair of a parameter and an input, unfolding only the branch that the
-- input selects, so an unused recursive call is never evaluated
-- (`natural-recursor-zero`, `natural-recursor-suc`, `tree-recursor-β`).
-- Outside their module, pair A a b is written ⟪ a , b ⟫⟨ A ⟩, the term
-- pair-of A x y of a pair ⟪ x , y ⟫ᵗ⟨ A ⟩, and conditional A e₁ e₂ is if⟨ A
-- ⟩ e₁ else e₂.

open import SPT.Base
open import SPT.Foundation.Impredicative.Realizability.CombinatoryAlgebra
  using
  ( Partial-Combinatory-Algebra; Term; var; constant; _·_; Evaluates
  ; var-value; constant-value; application-value; empty
  ; abstraction; abstraction-defined; abstraction-β; lambda; lambda-β
  ; lambda-curried; second; second-β; pair-body)

------------------------------------------------------------------------
-- Fixed points, pairs and numerals

module _ {ℓ : Level} (A : Partial-Combinatory-Algebra ℓ) where

  open Partial-Combinatory-Algebra A using
    (Carrier; apply; k; k-defined; k-law)

  ----------------------------------------------------------------------
  -- Fixed points

  -- λa. f (x x) a, for the variables a, x, f.
  self-body : Term A 3
  self-body =
    ( var (fsuc (fsuc fzero))
      · (var (fsuc fzero) · var (fsuc fzero)))
    · var fzero

  -- λx.λa. f (x x) a, at f.
  self : Carrier → Carrier
  self f = lambda A (extend-environment f (empty A)) (abstraction A self-body)

  -- self f at itself, which is λa. f (self f (self f)) a.
  fix : Carrier → Carrier
  fix f =
    lambda A (extend-environment (self f) (extend-environment f (empty A)))
      self-body

  self-at-self : (f : Carrier) → apply (self f) (self f) (fix f)
  self-at-self f =
    lambda-curried A (extend-environment f (empty A)) self-body (self f)

  fix-β : {f a g r : Carrier} → apply f (fix f) g → apply g a r →
    apply (fix f) a r
  fix-β {f} {a} p q =
    lambda-β A (extend-environment (self f) (extend-environment f (empty A)))
      self-body a
      ( application-value
          ( application-value
              ( var-value (fsuc (fsuc fzero)))
              ( application-value
                  ( var-value (fsuc fzero))
                  ( var-value (fsuc fzero))
                  ( self-at-self f))
              p)
          ( var-value fzero)
          q)

  ----------------------------------------------------------------------
  -- Pairs of values

  -- λz. z a b
  pair : Carrier → Carrier → Carrier
  pair a b =
    lambda A (extend-environment b (extend-environment a (empty A)))
      (pair-body A)

  infix 3 pair
  syntax pair A a b = ⟪ a , b ⟫⟨ A ⟩

  pair-first : (a b : Carrier) → apply (pair a b) k a
  pair-first a b =
    let (ka , m) = k-defined a
    in lambda-β A (extend-environment b (extend-environment a (empty A)))
         (pair-body A) k
         ( application-value
             ( application-value
                 ( var-value fzero)
                 ( var-value (fsuc (fsuc fzero)))
                 m)
             ( var-value (fsuc fzero))
             ( k-law m))

  pair-second : (a b : Carrier) → apply (pair a b) (second A) b
  pair-second a b =
    let (m₁ , m₂) = second-β A a b
    in lambda-β A (extend-environment b (extend-environment a (empty A)))
         (pair-body A)
         ( second A)
         ( application-value
             ( application-value
                 ( var-value fzero)
                 ( var-value (fsuc (fsuc fzero)))
                 m₁)
             ( var-value (fsuc fzero))
             m₂)

  -- λa.λb.λz. z a b
  pair-maker : Carrier
  pair-maker =
    lambda A (empty A) (abstraction A (abstraction A (pair-body A)))

  half-pair : Carrier → Carrier
  half-pair a =
    lambda A (extend-environment a (empty A)) (abstraction A (pair-body A))

  pair-maker-first : (a : Carrier) → apply pair-maker a (half-pair a)
  pair-maker-first a =
    lambda-curried A (empty A) (abstraction A (pair-body A)) a

  pair-maker-second : (a b : Carrier) → apply (half-pair a) b (pair a b)
  pair-maker-second a b =
    lambda-curried A (extend-environment a (empty A)) (pair-body A) b

  -- The term of the pair of two terms.
  pair-of : {n : ℕ} → Term A n → Term A n → Term A n
  pair-of x y = (constant pair-maker · x) · y

  infix 3 pair-of
  syntax pair-of A x y = ⟪ x , y ⟫ᵗ⟨ A ⟩

  pair-of-value : {n : ℕ} {ρ : Fin n → Carrier} {x y : Term A n}
    {a b : Carrier} → Evaluates A ρ x a → Evaluates A ρ y b →
    Evaluates A ρ (pair-of x y) (pair a b)
  pair-of-value {a = a} {b = b} ex ey =
    application-value
      ( application-value
          ( constant-value pair-maker)
          ex
          ( pair-maker-first a))
      ey
      ( pair-maker-second a b)

  ----------------------------------------------------------------------
  -- The conditional

  -- λq. ((q second) (e₁ (q k))) (e₂ (q k)): both branches are evaluated,
  -- at the first component of q, and the second component selects one.

  conditional-body : Carrier → Carrier → Term A 1
  conditional-body e₁ e₂ =
    ( (var fzero · constant (second A))
      · (constant e₁ · (var fzero · constant k)))
    · (constant e₂ · (var fzero · constant k))

  conditional : Carrier → Carrier → Carrier
  conditional e₁ e₂ = lambda A (empty A) (conditional-body e₁ e₂)

  infixr 10 conditional
  syntax conditional A e₁ e₂ = if⟨ A ⟩ e₁ else e₂

  conditional-left : {e₁ e₂ q g x y : Carrier} → apply q k g →
    apply q (second A) k → apply e₁ g x → apply e₂ g y →
    apply (conditional e₁ e₂) q x
  conditional-left {e₁} {e₂} {q} {g} {x} {y} qk qs ex ey =
    let (kx , m) = k-defined x
    in lambda-β A (empty A) (conditional-body e₁ e₂) q
         ( application-value
             ( application-value
                 ( application-value
                     ( var-value fzero)
                     ( constant-value (second A))
                     qs)
                 ( application-value
                     ( constant-value e₁)
                     ( application-value
                         ( var-value fzero)
                         ( constant-value k)
                         qk)
                     ex)
                 m)
             ( application-value
                 ( constant-value e₂)
                 ( application-value
                     ( var-value fzero)
                     ( constant-value k)
                     qk)
                 ey)
             ( k-law m))

  conditional-right : {e₁ e₂ q g x y : Carrier} → apply q k g →
    apply q (second A) (second A) → apply e₁ g x → apply e₂ g y →
    apply (conditional e₁ e₂) q y
  conditional-right {e₁} {e₂} {q} {g} {x} {y} qk qs ex ey =
    let (m₁ , m₂) = second-β A x y
    in lambda-β A (empty A) (conditional-body e₁ e₂) q
         ( application-value
             ( application-value
                 ( application-value
                     ( var-value fzero)
                     ( constant-value (second A))
                     qs)
                 ( application-value
                     ( constant-value e₁)
                     ( application-value
                         ( var-value fzero)
                         ( constant-value k)
                         qk)
                     ex)
                 m₁)
             ( application-value
                 ( constant-value e₂)
                 ( application-value
                     ( var-value fzero)
                     ( constant-value k)
                     qk)
                 ey)
             m₂)

  ----------------------------------------------------------------------
  -- Numerals

  -- A numeral is read by k, the tag, and by second, its predecessor.
  Numeral : ℕ → Carrier → Set ℓ
  Numeral zero p = apply p k k × Σ Carrier (λ c → apply p (second A) c)
  Numeral (suc n) p =
    apply p k (second A) ×
    Σ Carrier (λ c → apply p (second A) c × Numeral n c)

  numeral : ℕ → Carrier
  numeral zero = pair k k
  numeral (suc n) = pair (second A) (numeral n)

  numeral-is-numeral : (n : ℕ) → Numeral n (numeral n)
  numeral-is-numeral zero = pair-first k k , k , pair-second k k
  numeral-is-numeral (suc n) =
    pair-first (second A) (numeral n) ,
    numeral n ,
    pair-second (second A) (numeral n) ,
    numeral-is-numeral n

------------------------------------------------------------------------
-- Recursion on numerals

-- The input is a pair q of a parameter g and a numeral p. The branches
-- are abstractions over the predecessor c, so that only the one the tag
-- of p selects is evaluated. In the branch of a successor, the recursive
-- call is at the pair of g and c. The recursor at a base e-zero and a step
-- e-step takes them as the parameters of its module.

module _ {ℓ : Level} (A : Partial-Combinatory-Algebra ℓ) where

  open Partial-Combinatory-Algebra A using (Carrier; k)

  -- The parameter, in the context of the variables c, q, r.
  natural-parameter : Term A 3
  natural-parameter = var (fsuc fzero) · constant k

  natural-zero-branch : Carrier → Term A 3
  natural-zero-branch e-zero = constant e-zero · natural-parameter

  natural-call : Term A 3
  natural-call =
    var (fsuc (fsuc fzero)) · ⟪ natural-parameter , var fzero ⟫ᵗ⟨ A ⟩

  natural-step-branch : Carrier → Term A 3
  natural-step-branch e-step =
    constant e-step
      · ⟪ ⟪ natural-parameter , var fzero ⟫ᵗ⟨ A ⟩ , natural-call ⟫ᵗ⟨ A ⟩

module _ {ℓ : Level} (A : Partial-Combinatory-Algebra ℓ)
  (e-zero e-step : Partial-Combinatory-Algebra.Carrier A) where

  open Partial-Combinatory-Algebra A using
    (Carrier; apply; k; k-defined; k-law)

  -- In the context of the variables q, r.
  natural-body : Term A 2
  natural-body =
    ( ( ( (var fzero · constant (second A)) · constant k)
        · abstraction A (natural-zero-branch A e-zero))
      · abstraction A (natural-step-branch A e-step))
    · ((var fzero · constant (second A)) · constant (second A))

  natural-step : Carrier
  natural-step = lambda A (empty A) (abstraction A natural-body)

  natural-recursor : Carrier
  natural-recursor = fix A natural-step

  -- The value of the body at q, unfolded through the fixed point.
  natural-unfold : {q s : Carrier} →
    Evaluates A
      (extend-environment q (extend-environment natural-recursor (empty A)))
      natural-body s →
    apply natural-recursor q s
  natural-unfold {q} e =
    fix-β A
      ( lambda-curried A (empty A) natural-body natural-recursor)
      ( lambda-β A (extend-environment natural-recursor (empty A))
          natural-body q e)

  natural-recursor-zero : {q g p c z : Carrier} → apply q k g →
    apply q (second A) p → apply p k k → apply p (second A) c →
    apply e-zero g z → apply natural-recursor q z
  natural-recursor-zero {q} {g} {p} {c} qk qs pk ps ez =
    let ρ = extend-environment q (extend-environment natural-recursor (empty A))
        (b₁ , eb₁) = abstraction-defined A ρ (natural-zero-branch A e-zero)
        (b₂ , eb₂) = abstraction-defined A ρ (natural-step-branch A e-step)
        (kb , m) = k-defined b₁
    in natural-unfold
         ( application-value
             ( application-value
                 ( application-value
                     ( application-value
                         ( application-value
                             ( var-value fzero)
                             ( constant-value (second A))
                             qs)
                         ( constant-value k)
                         pk)
                     eb₁
                     m)
                 eb₂
                 ( k-law m))
             ( application-value
                 ( application-value
                     ( var-value fzero)
                     ( constant-value (second A))
                     qs)
                 ( constant-value (second A))
                 ps)
             ( abstraction-β A ρ (natural-zero-branch A e-zero) c eb₁
                 ( application-value
                     ( constant-value e-zero)
                     ( application-value
                         ( var-value (fsuc fzero))
                         ( constant-value k)
                         qk)
                     ez)))

  natural-recursor-suc : {q g p c y s : Carrier} → apply q k g →
    apply q (second A) p → apply p k (second A) → apply p (second A) c →
    apply natural-recursor ⟪ g , c ⟫⟨ A ⟩ y →
    apply e-step ⟪ ⟪ g , c ⟫⟨ A ⟩ , y ⟫⟨ A ⟩ s →
    apply natural-recursor q s
  natural-recursor-suc {q} {g} {p} {c} qk qs pk ps ry es =
    let ρ = extend-environment q (extend-environment natural-recursor (empty A))
        (b₁ , eb₁) = abstraction-defined A ρ (natural-zero-branch A e-zero)
        (b₂ , eb₂) = abstraction-defined A ρ (natural-step-branch A e-step)
        (m₁ , m₂) = second-β A b₁ b₂
        parameter =
          application-value
            ( var-value (fsuc fzero))
            ( constant-value k)
            qk
    in natural-unfold
         ( application-value
             ( application-value
                 ( application-value
                     ( application-value
                         ( application-value
                             ( var-value fzero)
                             ( constant-value (second A))
                             qs)
                         ( constant-value k)
                         pk)
                     eb₁
                     m₁)
                 eb₂
                 m₂)
             ( application-value
                 ( application-value
                     ( var-value fzero)
                     ( constant-value (second A))
                     qs)
                 ( constant-value (second A))
                 ps)
             ( abstraction-β A ρ (natural-step-branch A e-step) c eb₂
                 ( application-value
                     ( constant-value e-step)
                     ( pair-of-value A
                         ( pair-of-value A parameter (var-value fzero))
                         ( application-value
                             ( var-value (fsuc (fsuc fzero)))
                             ( pair-of-value A parameter (var-value fzero))
                             ry))
                     es)))

------------------------------------------------------------------------
-- Recursion on trees

-- The input is a pair q of a parameter g and a pair of a label a and a
-- function f on the branches. The step receives g, a, f and the
-- abstraction h sending a branch b to the recursive call at the pair of
-- g and f b, which is evaluated only when h is applied. The recursor at
-- a step e-step takes it as the parameter of its module.

module _ {ℓ : Level} (A : Partial-Combinatory-Algebra ℓ) where

  open Partial-Combinatory-Algebra A using (k)

  -- In the context of the variables b, q, r.
  tree-call : Term A 3
  tree-call =
    var (fsuc (fsuc fzero))
      · ⟪ var (fsuc fzero) · constant k ,
          ( (var (fsuc fzero) · constant (second A)) · constant (second A))
          · var fzero ⟫ᵗ⟨ A ⟩

module _ {ℓ : Level} (A : Partial-Combinatory-Algebra ℓ)
  (e-step : Partial-Combinatory-Algebra.Carrier A) where

  open Partial-Combinatory-Algebra A using (Carrier; apply; k)

  -- In the context of the variables q, r.
  tree-body : Term A 2
  tree-body =
    constant e-step
      · ⟪ ⟪ ⟪ var fzero · constant k ,
              (var fzero · constant (second A)) · constant k ⟫ᵗ⟨ A ⟩ ,
            (var fzero · constant (second A)) · constant (second A) ⟫ᵗ⟨ A ⟩ ,
          abstraction A (tree-call A) ⟫ᵗ⟨ A ⟩

  tree-step : Carrier
  tree-step = lambda A (empty A) (abstraction A tree-body)

  tree-recursor : Carrier
  tree-recursor = fix A tree-step

  -- The hypotheses at q: the value of the abstraction over the branches.
  tree-hypotheses : Carrier → Carrier
  tree-hypotheses q =
    lambda A
      (extend-environment q (extend-environment tree-recursor (empty A)))
      (tree-call A)

  tree-hypotheses-β : {q g t f b c x : Carrier} → apply q k g →
    apply q (second A) t → apply t (second A) f → apply f b c →
    apply tree-recursor ⟪ g , c ⟫⟨ A ⟩ x → apply (tree-hypotheses q) b x
  tree-hypotheses-β {q} {g} {t} {f} {b} {c} {x} qk qs ts fb rx =
    lambda-β A
      (extend-environment q (extend-environment tree-recursor (empty A)))
      (tree-call A) b
      ( application-value
          ( var-value (fsuc (fsuc fzero)))
          ( pair-of-value A
              ( application-value
                  ( var-value (fsuc fzero))
                  ( constant-value k)
                  qk)
              ( application-value
                  ( application-value
                      ( application-value
                          ( var-value (fsuc fzero))
                          ( constant-value (second A))
                          qs)
                      ( constant-value (second A))
                      ts)
                  ( var-value fzero)
                  fb))
          rx)

  tree-recursor-β : {q g t a f s : Carrier} → apply q k g →
    apply q (second A) t → apply t k a → apply t (second A) f →
    apply e-step ⟪ ⟪ ⟪ g , a ⟫⟨ A ⟩ , f ⟫⟨ A ⟩ , tree-hypotheses q ⟫⟨ A ⟩ s →
    apply tree-recursor q s
  tree-recursor-β {q} qk qs tk ts es =
    fix-β A
      ( lambda-curried A (empty A) tree-body tree-recursor)
      ( lambda-β A (extend-environment tree-recursor (empty A)) tree-body q
          ( application-value
              ( constant-value e-step)
              ( pair-of-value A
                  ( pair-of-value A
                      ( pair-of-value A
                          ( application-value
                              ( var-value fzero)
                              ( constant-value k)
                              qk)
                          ( application-value
                              ( application-value
                                  ( var-value fzero)
                                  ( constant-value (second A))
                                  qs)
                              ( constant-value k)
                              tk))
                      ( application-value
                          ( application-value
                              ( var-value fzero)
                              ( constant-value (second A))
                              qs)
                          ( constant-value (second A))
                          ts))
                  ( pr₂
                      ( abstraction-defined A
                          ( extend-environment q
                              (extend-environment tree-recursor (empty A)))
                          ( tree-call A))))
              es))
