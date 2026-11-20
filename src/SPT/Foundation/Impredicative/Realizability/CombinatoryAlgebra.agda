{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Impredicative.Realizability.CombinatoryAlgebra where

-- Partial combinatory algebras and combinatory completeness. A partial
-- combinatory algebra is a type with a functional partial application,
-- given by its graph (apply a b c: a · b is defined with value c), and
-- combinators k and s with their laws (`Partial-Combinatory-Algebra`):
--
--   k · a ↓,   k · a · b ≃ a,
--   s · a ↓,   s · a · b ↓,   s · a · b · c ≃ (a · c) · (b · c).
--
-- Terms in n variables evaluate partially in an environment (`Term`,
-- `Evaluates`). Bracket abstraction is always defined
-- (`abstraction-defined`) and applies as the abstracted term
-- (`abstraction-β`). From these two laws come the combinators that
-- realizers are built from: `identity`, `composite`, `pairing` and its
-- projections `first-after` and `second-after`, tagged injections
-- (`injection`) and their `copairing`, `curry`, `uncurry` and
-- `constant-after`.

open import SPT.Base

------------------------------------------------------------------------
-- Partial combinatory algebras

-- Mathematical shape:
--   apply a b c   a · b is defined with value c; functional in c,
--   k · a ↓  and  k · a · b ≃ a,
--   s · a ↓, s · a · b ↓  and  s · a · b · c ≃ (a · c) · (b · c).
-- The last Kleene equality is stated in both directions. The values of a
-- law are hidden where its premises determine them.
record Partial-Combinatory-Algebra (ℓ : Level) : Set (lsuc ℓ) where
  field
    Carrier : Set ℓ
    apply : Carrier → Carrier → Carrier → Set ℓ
    functional : {a b c c′ : Carrier} → apply a b c → apply a b c′ → c ＝ c′
    k s : Carrier
    k-defined : (a : Carrier) → Σ Carrier (λ ka → apply k a ka)
    k-law : {a b ka : Carrier} → apply k a ka → apply ka b a
    s-defined : (a : Carrier) → Σ Carrier (λ sa → apply s a sa)
    s-defined₂ : {a sa : Carrier} (b : Carrier) → apply s a sa →
      Σ Carrier (λ sab → apply sa b sab)
    s-law : {a b c sa sab u v r : Carrier} → apply s a sa →
      apply sa b sab → apply a c u → apply b c v → apply u v r →
      apply sab c r
    s-law-converse : {a b c sa sab r : Carrier} → apply s a sa →
      apply sa b sab → apply sab c r →
      Σ Carrier (λ u → Σ Carrier (λ v →
        apply a c u × apply b c v × apply u v r))

------------------------------------------------------------------------
-- Terms and their evaluation

-- A term in n variables is built from variables, points of the algebra
-- and application; it evaluates in an environment exactly when every
-- application in it is defined.

module _ {ℓ : Level} (A : Partial-Combinatory-Algebra ℓ) where

  open Partial-Combinatory-Algebra A using
    (Carrier; apply; k; s; k-defined; k-law; s-defined; s-defined₂; s-law)

  infixl 40 _·_

  data Term (n : ℕ) : Set ℓ where
    var : Fin n → Term n
    constant : Carrier → Term n
    _·_ : Term n → Term n → Term n

  data Evaluates {n : ℕ} (ρ : Fin n → Carrier) : Term n → Carrier → Set ℓ
    where
    var-value : (i : Fin n) → Evaluates ρ (var i) (ρ i)
    constant-value : (a : Carrier) → Evaluates ρ (constant a) a
    application-value : {t u : Term n} {a b c : Carrier} →
      Evaluates ρ t a → Evaluates ρ u b → apply a b c →
      Evaluates ρ (t · u) c

  -- The environment of a closed term.
  empty : Fin 0 → Carrier
  empty ()

  ----------------------------------------------------------------------
  -- Bracket abstraction

  -- λx.x = s k k, λx.y = k y, λx.a = k a and λx.(t u) = s (λx.t) (λx.u).
  -- s · a · b is always defined, so every abstraction is; applied to a,
  -- it evaluates as the term with a at its newest variable.

  abstraction : {n : ℕ} → Term (suc n) → Term n
  abstraction (var fzero) = (constant s · constant k) · constant k
  abstraction (var (fsuc i)) = constant k · var i
  abstraction (constant a) = constant k · constant a
  abstraction (t · u) = (constant s · abstraction t) · abstraction u

  s-defined-twice : {n : ℕ} (ρ : Fin n → Carrier) (t u : Term n)
    {a b : Carrier} → Evaluates ρ t a → Evaluates ρ u b →
    Σ Carrier (λ c → Evaluates ρ ((constant s · t) · u) c)
  s-defined-twice ρ t u {a} {b} et eu =
    let (sa , p) = s-defined a
        (sab , q) = s-defined₂ b p
    in sab , application-value (application-value (constant-value s) et p) eu q

  abstraction-defined : {n : ℕ} (ρ : Fin n → Carrier) (t : Term (suc n)) →
    Σ Carrier (λ f → Evaluates ρ (abstraction t) f)
  abstraction-defined ρ (var fzero) =
    s-defined-twice ρ (constant k) (constant k)
      ( constant-value k)
      ( constant-value k)
  abstraction-defined ρ (var (fsuc i)) =
    let (ka , p) = k-defined (ρ i)
    in ka , application-value (constant-value k) (var-value i) p
  abstraction-defined ρ (constant a) =
    let (ka , p) = k-defined a
    in ka , application-value (constant-value k) (constant-value a) p
  abstraction-defined ρ (t · u) =
    let (f , ef) = abstraction-defined ρ t
        (g , eg) = abstraction-defined ρ u
    in s-defined-twice ρ (abstraction t) (abstraction u) ef eg

  abstraction-β : {n : ℕ} (ρ : Fin n → Carrier) (t : Term (suc n))
    (a : Carrier) {f r : Carrier} → Evaluates ρ (abstraction t) f →
    Evaluates (extend-environment a ρ) t r → apply f a r
  abstraction-β ρ (var fzero) a
    (application-value
      (application-value (constant-value _) (constant-value _) p)
      (constant-value _)
      q)
    (var-value _) =
    let (ka , m) = k-defined a
    in s-law p q m m (k-law m)
  abstraction-β ρ (var (fsuc i)) a
    (application-value (constant-value _) (var-value _) p)
    (var-value _) =
    k-law p
  abstraction-β ρ (constant b) a
    (application-value (constant-value _) (constant-value _) p)
    (constant-value _) =
    k-law p
  abstraction-β ρ (t · u) a
    (application-value
      (application-value (constant-value _) et p)
      eu
      q)
    (application-value dt du w) =
    s-law p q (abstraction-β ρ t a et dt) (abstraction-β ρ u a eu du) w

  ----------------------------------------------------------------------
  -- Abstracted values

  -- lambda ρ t is the value of λx.t in the environment ρ. Nested
  -- abstraction gives curried values (`lambda-curried`).

  lambda : {n : ℕ} → (Fin n → Carrier) → Term (suc n) → Carrier
  lambda ρ t = pr₁ (abstraction-defined ρ t)

  lambda-β : {n : ℕ} (ρ : Fin n → Carrier) (t : Term (suc n)) (a : Carrier)
    {r : Carrier} → Evaluates (extend-environment a ρ) t r →
    apply (lambda ρ t) a r
  lambda-β ρ t a e = abstraction-β ρ t a (pr₂ (abstraction-defined ρ t)) e

  lambda-curried : {n : ℕ} (ρ : Fin n → Carrier) (t : Term (suc (suc n)))
    (a : Carrier) →
    apply (lambda ρ (abstraction t)) a (lambda (extend-environment a ρ) t)
  lambda-curried ρ t a =
    lambda-β ρ (abstraction t) a
      (pr₂ (abstraction-defined (extend-environment a ρ) t))

  ----------------------------------------------------------------------
  -- Combinators

  -- Each combinator is a closed abstraction, and its law is the β-law
  -- applied to an evaluation built from the premises. A pair is read by
  -- applying it to k (first) and to second. The combinators of two
  -- realizers have notation outside this module: composite A e₁ e₂ is
  -- e₂ ∘⟨ A ⟩ e₁, pairing A e₁ e₂ is ⟨ e₁ , e₂ ⟩⟨ A ⟩, and
  -- copairing A e₁ e₂ is [ e₁ , e₂ ]⟨ A ⟩.

  identity : Carrier
  identity = lambda empty (var fzero)

  identity-β : (a : Carrier) → apply identity a a
  identity-β a = lambda-β empty (var fzero) a (var-value fzero)

  -- λx. e₂ (e₁ x)
  composite : Carrier → Carrier → Carrier
  composite e₁ e₂ = lambda empty (constant e₂ · (constant e₁ · var fzero))

  infixr 15 composite
  syntax composite A e₁ e₂ = e₂ ∘⟨ A ⟩ e₁

  composite-β : {e₁ e₂ a b c : Carrier} → apply e₁ a b → apply e₂ b c →
    apply (composite e₁ e₂) a c
  composite-β {e₁} {e₂} {a} p q =
    lambda-β empty (constant e₂ · (constant e₁ · var fzero)) a
      ( application-value
          ( constant-value e₂)
          ( application-value (constant-value e₁) (var-value fzero) p)
          q)

  -- λx.λy.y
  second : Carrier
  second = lambda empty (abstraction (var fzero))

  second-β : (a b : Carrier) →
    apply second a (lambda (extend-environment a empty) (var fzero)) ×
    apply (lambda (extend-environment a empty) (var fzero)) b b
  second-β a b =
    lambda-curried empty (var fzero) a ,
    lambda-β (extend-environment a empty) (var fzero) b (var-value fzero)

  -- λx. (e x) k   and   λx. (e x) second
  first-after : Carrier → Carrier
  first-after e = lambda empty ((constant e · var fzero) · constant k)

  first-after-β : {e a p b : Carrier} → apply e a p → apply p k b →
    apply (first-after e) a b
  first-after-β {e} {a} ep pb =
    lambda-β empty ((constant e · var fzero) · constant k) a
      ( application-value
          ( application-value (constant-value e) (var-value fzero) ep)
          ( constant-value k)
          pb)

  second-after : Carrier → Carrier
  second-after e = lambda empty ((constant e · var fzero) · constant second)

  second-after-β : {e a p b : Carrier} → apply e a p → apply p second b →
    apply (second-after e) a b
  second-after-β {e} {a} ep pb =
    lambda-β empty ((constant e · var fzero) · constant second) a
      ( application-value
          ( application-value (constant-value e) (var-value fzero) ep)
          ( constant-value second)
          pb)

  -- λx.λz. z (e₁ x) (e₂ x)
  pairing-body : Carrier → Carrier → Term 2
  pairing-body e₁ e₂ =
    (var fzero · (constant e₁ · var (fsuc fzero)))
    · (constant e₂ · var (fsuc fzero))

  pairing : Carrier → Carrier → Carrier
  pairing e₁ e₂ = lambda empty (abstraction (pairing-body e₁ e₂))

  infix 3 pairing
  syntax pairing A e₁ e₂ = ⟨ e₁ , e₂ ⟩⟨ A ⟩

  pairing-β : {e₁ e₂ a b c : Carrier} → apply e₁ a b → apply e₂ a c →
    Σ Carrier (λ p →
      apply (pairing e₁ e₂) a p × apply p k b × apply p second c)
  pairing-β {e₁} {e₂} {a} {b} {c} eb ec =
    let (kb , m) = k-defined b
        (m₁ , m₂) = second-β b c
    in lambda (extend-environment a empty) (pairing-body e₁ e₂) ,
       lambda-curried empty (pairing-body e₁ e₂) a ,
       lambda-β (extend-environment a empty) (pairing-body e₁ e₂) k
         ( application-value
             ( application-value
                 ( var-value fzero)
                 ( application-value
                     ( constant-value e₁)
                     ( var-value (fsuc fzero))
                     eb)
                 m)
             ( application-value
                 ( constant-value e₂)
                 ( var-value (fsuc fzero))
                 ec)
             ( k-law m)) ,
       lambda-β (extend-environment a empty) (pairing-body e₁ e₂) second
         ( application-value
             ( application-value
                 ( var-value fzero)
                 ( application-value
                     ( constant-value e₁)
                     ( var-value (fsuc fzero))
                     eb)
                 m₁)
             ( application-value
                 ( constant-value e₂)
                 ( var-value (fsuc fzero))
                 ec)
             m₂)

  -- λx.λz. z t x, for the tag t = k (left) or t = second (right).
  injection-body : Carrier → Term 2
  injection-body t = (var fzero · constant t) · var (fsuc fzero)

  injection : Carrier → Carrier
  injection t = lambda empty (abstraction (injection-body t))

  injection-β : (t a : Carrier) →
    Σ Carrier (λ p →
      apply (injection t) a p × apply p k t × apply p second a)
  injection-β t a =
    let (kt , m) = k-defined t
        (m₁ , m₂) = second-β t a
    in lambda (extend-environment a empty) (injection-body t) ,
       lambda-curried empty (injection-body t) a ,
       lambda-β (extend-environment a empty) (injection-body t) k
         ( application-value
             ( application-value (var-value fzero) (constant-value t) m)
             ( var-value (fsuc fzero))
             ( k-law m)) ,
       lambda-β (extend-environment a empty) (injection-body t) second
         ( application-value
             ( application-value (var-value fzero) (constant-value t) m₁)
             ( var-value (fsuc fzero))
             m₂)

  -- λp. ((p k) e₁ e₂) (p second)
  copairing-body : Carrier → Carrier → Term 1
  copairing-body e₁ e₂ =
    (((var fzero · constant k) · constant e₁) · constant e₂)
    · (var fzero · constant second)

  copairing : Carrier → Carrier → Carrier
  copairing e₁ e₂ = lambda empty (copairing-body e₁ e₂)

  infix 3 copairing
  syntax copairing A e₁ e₂ = [ e₁ , e₂ ]⟨ A ⟩

  copairing-left : {e₁ e₂ p c r : Carrier} → apply p k k →
    apply p second c → apply e₁ c r → apply (copairing e₁ e₂) p r
  copairing-left {e₁} {e₂} {p} pk ps er =
    let (ke , m) = k-defined e₁
    in lambda-β empty (copairing-body e₁ e₂) p
         ( application-value
             ( application-value
                 ( application-value
                     ( application-value
                         ( var-value fzero)
                         ( constant-value k)
                         pk)
                     ( constant-value e₁)
                     m)
                 ( constant-value e₂)
                 ( k-law m))
             ( application-value (var-value fzero) (constant-value second) ps)
             er)

  copairing-right : {e₁ e₂ p c r : Carrier} → apply p k second →
    apply p second c → apply e₂ c r → apply (copairing e₁ e₂) p r
  copairing-right {e₁} {e₂} {p} pk ps er =
    let (m₁ , m₂) = second-β e₁ e₂
    in lambda-β empty (copairing-body e₁ e₂) p
         ( application-value
             ( application-value
                 ( application-value
                     ( application-value
                         ( var-value fzero)
                         ( constant-value k)
                         pk)
                     ( constant-value e₁)
                     m₁)
                 ( constant-value e₂)
                 m₂)
             ( application-value (var-value fzero) (constant-value second) ps)
             er)

  -- λx.λy. e (λz. z x y)
  pair-body : Term 3
  pair-body = (var fzero · var (fsuc (fsuc fzero))) · var (fsuc fzero)

  curry-body : Carrier → Term 2
  curry-body e = constant e · abstraction pair-body

  curry : Carrier → Carrier
  curry e = lambda empty (abstraction (curry-body e))

  curry-β : (e a : Carrier) →
    Σ Carrier (λ g →
      apply (curry e) a g ×
      ((b : Carrier) → Σ Carrier (λ p →
        (apply p k a × apply p second b) ×
        ((r : Carrier) → apply e p r → apply g b r))))
  curry-β e a =
    lambda (extend-environment a empty) (curry-body e) ,
    lambda-curried empty (curry-body e) a ,
    ( λ b →
        let (ka , m) = k-defined a
            (m₁ , m₂) = second-β a b
        in lambda (extend-environment b (extend-environment a empty))
             pair-body ,
           ( lambda-β (extend-environment b (extend-environment a empty))
               pair-body k
               ( application-value
                   ( application-value
                       ( var-value fzero)
                       ( var-value (fsuc (fsuc fzero)))
                       m)
                   ( var-value (fsuc fzero))
                   ( k-law m)) ,
             lambda-β (extend-environment b (extend-environment a empty))
               pair-body second
               ( application-value
                   ( application-value
                       ( var-value fzero)
                       ( var-value (fsuc (fsuc fzero)))
                       m₁)
                   ( var-value (fsuc fzero))
                   m₂)) ,
           ( λ r ep →
               lambda-β (extend-environment a empty) (curry-body e) b
                 ( application-value
                     ( constant-value e)
                     ( pr₂
                         ( abstraction-defined
                             ( extend-environment b
                                 (extend-environment a empty))
                             pair-body))
                     ep)))

  -- λp. (e (p k)) (p second)
  uncurry-body : Carrier → Term 1
  uncurry-body e =
    (constant e · (var fzero · constant k)) · (var fzero · constant second)

  uncurry : Carrier → Carrier
  uncurry e = lambda empty (uncurry-body e)

  uncurry-β : {e p a b g r : Carrier} → apply p k a → apply p second b →
    apply e a g → apply g b r → apply (uncurry e) p r
  uncurry-β {e} {p} pk ps eg gr =
    lambda-β empty (uncurry-body e) p
      ( application-value
          ( application-value
              ( constant-value e)
              ( application-value (var-value fzero) (constant-value k) pk)
              eg)
          ( application-value (var-value fzero) (constant-value second) ps)
          gr)

  -- λx.λy. e x
  constant-after-body : Carrier → Term 2
  constant-after-body e = constant e · var (fsuc fzero)

  constant-after : Carrier → Carrier
  constant-after e = lambda empty (abstraction (constant-after-body e))

  constant-after-β : (e a : Carrier) →
    Σ Carrier (λ g →
      apply (constant-after e) a g ×
      ((b c : Carrier) → apply e a c → apply g b c))
  constant-after-β e a =
    lambda (extend-environment a empty) (constant-after-body e) ,
    lambda-curried empty (constant-after-body e) a ,
    ( λ b c ec →
        lambda-β (extend-environment a empty) (constant-after-body e) b
          ( application-value
              ( constant-value e)
              ( var-value (fsuc fzero))
              ec))
