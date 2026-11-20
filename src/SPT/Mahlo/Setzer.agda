{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Setzer where

-- Setzer's rules for a Mahlo universe (V , S), in the formulation of
-- Dybjer–Setzer, Induction–recursion and initial algebras, §6.1. For every
-- pair f, g of operations on V (`Operators`) there is a subuniverse
-- represented in V (`Subuniverse`): a code whose decoding is its carrier,
-- an inclusion into V, codes reflecting the standard codes of V, and codes
-- result and branch for f and g. Each code carries its decoding equation
-- for the inclusion:
--
--   inclusion (result a b) ＝ f (inclusion a) (inclusion ∘ b),
--   inclusion (branch a b c) ＝ g (inclusion a) (inclusion ∘ b) c.
--
-- Setzer's T is the decoding through the inclusion, `Decode S inclusion`,
-- and a family of the subuniverse is included in V by `map S inclusion`
-- (SPT.Mahlo.Specification). The standard codes are the formers of
-- SPT.Mahlo.Specification (empty, unit, two, natural numbers, Π, Σ, W,
-- identity), together with codes for the finite types Nₖ and binary sums,
-- as in MLM's V (`Coproducts`). All equations are identities, not
-- judgmental rules.
--
-- Resident reflection gives these rules for every f and g with no further
-- hypothesis (`subuniverse`, `reflector`, `from-reflection`). Conversely,
-- under function extensionality at the function types S x → V, the rules
-- give resident reflection (`reflection`, `to-reflection`); extensionality
-- is used only for the whole branch function in the family equation. A
-- pair f, g and an operator on families determine each other by refl
-- (`split-operator`, `operator-split`), and the return to resident
-- reflection keeps the original resident carrier (`carrier-return`,
-- `interpret-return`). The standard codes of any subuniverse form a closure
-- under the identity operator, for constructions that read only those codes
-- (`ordinary`).
--
-- Every subuniverse can be taken closed under Nₖ and + as well (`closed`),
-- by Setzer's augmentation (Dybjer–Setzer §6.2): reflect f and g extended
-- by the output N + (a × a) + 1 + f(a, b) (`augmented`), whose points name
-- a finite type, the sum of two members of a family, f(a, b), or a code of
-- g, and read back to them (`read-finite`, `read-pair`, `read-result`,
-- `read-branch`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Mahlo.Specification using
  (Family; Operator; Formers; Decode; map; Closure; Reflection; Mahlo)
open import SPT.Mahlo.Decoding using (DecodingLaws; MahloReflection)
import SPT.Mahlo.Decoding as Decoding

------------------------------------------------------------------------
-- The rules

-- Setzer's f and g: an output code for each family of V, and a code for
-- each point of the decoded output.
record Operators {κ ℓ : Level} {V : Set κ} (S : V → Set ℓ) : Set (κ ⊔ ℓ)
  where
  field
    f : (a : V) → (S a → V) → V
    g : (a : V) (b : S a → V) → S (f a b) → V

-- The subuniverse for f and g. Its carrier is the decoding of its code, so
-- the subuniverse is represented in V by definition.
record Subuniverse {κ ℓ : Level} {V : Set κ} {S : V → Set ℓ}
  (Q : Formers V S) (o : Operators S) : Set (κ ⊔ ℓ) where
  field
    code : V
    inclusion : S code → V

    empty unit two natural : S code
    empty-β : inclusion empty ＝ Formers.empty Q
    unit-β : inclusion unit ＝ Formers.unit Q
    two-β : inclusion two ＝ Formers.two Q
    natural-β : inclusion natural ＝ Formers.natural Q

    product sum tree :
      (a : S code) → (Decode S inclusion a → S code) → S code
    product-β : (a : S code) (b : Decode S inclusion a → S code) →
      inclusion (product a b) ＝ Formers.product Q (map S inclusion (a , b))
    sum-β : (a : S code) (b : Decode S inclusion a → S code) →
      inclusion (sum a b) ＝ Formers.sum Q (map S inclusion (a , b))
    tree-β : (a : S code) (b : Decode S inclusion a → S code) →
      inclusion (tree a b) ＝ Formers.tree Q (map S inclusion (a , b))

    identity : (a : S code) →
      Decode S inclusion a → Decode S inclusion a → S code
    identity-β : (a : S code) (x y : Decode S inclusion a) →
      inclusion (identity a x y) ＝ Formers.identity Q (inclusion a) x y

    result : (a : S code) → (Decode S inclusion a → S code) → S code
    result-β : (a : S code) (b : Decode S inclusion a → S code) →
      inclusion (result a b) ＝
        Operators.f o (inclusion a) (λ x → inclusion (b x))

    branch : (a : S code) (b : Decode S inclusion a → S code) →
      S (Operators.f o (inclusion a) (λ x → inclusion (b x))) → S code
    branch-β : (a : S code) (b : Decode S inclusion a → S code)
      (c : S (Operators.f o (inclusion a) (λ x → inclusion (b x)))) →
      inclusion (branch a b c) ＝
        Operators.g o (inclusion a) (λ x → inclusion (b x)) c

module _ {κ ℓ : Level} {V : Set κ} {S : V → Set ℓ} where

  -- Setzer's Mahlo rule over fixed standard codes: a subuniverse for every
  -- f and g.
  Reflects : Formers V S → Set (κ ⊔ ℓ)
  Reflects Q = (o : Operators S) → Subuniverse Q o

-- Codes for the finite types Nₖ and for binary sums.
record Coproducts {κ ℓ : Level} {V : Set κ} (S : V → Set ℓ) :
  Set (κ ⊔ lsuc ℓ) where
  field
    finite : ℕ → V
    plus : V → V → V
    finite-β : (k : ℕ) → S (finite k) ＝ Lift ℓ (Fin k)
    plus-β : (a b : V) → S (plus a b) ＝ (S a ⊎ S b)

-- A Mahlo universe: standard codes with their decodings, and a subuniverse
-- for every f and g.
record Universe {κ ℓ : Level} {V : Set κ} (S : V → Set ℓ) :
  Set (κ ⊔ lsuc ℓ) where
  field
    formers : Formers V S
    decoding : DecodingLaws formers
    coproducts : Coproducts S
    reflect : Reflects formers

-- A subuniverse for f and g that also has codes for Nₖ and +.
record Closed {κ ℓ : Level} {V : Set κ} {S : V → Set ℓ} (Q : Formers V S)
  (C : Coproducts S) (o : Operators S) : Set (κ ⊔ ℓ) where
  field
    subuniverse : Subuniverse Q o
    finite : ℕ → S (Subuniverse.code subuniverse)
    finite-β : (k : ℕ) →
      Subuniverse.inclusion subuniverse (finite k) ＝ Coproducts.finite C k
    plus : S (Subuniverse.code subuniverse) →
      S (Subuniverse.code subuniverse) → S (Subuniverse.code subuniverse)
    plus-β : (a b : S (Subuniverse.code subuniverse)) →
      Subuniverse.inclusion subuniverse (plus a b) ＝
        Coproducts.plus C (Subuniverse.inclusion subuniverse a)
          (Subuniverse.inclusion subuniverse b)

module _ {κ ℓ : Level} {V : Set κ} {S : V → Set ℓ} {Q : Formers V S}
  {o : Operators S} where

  -- The standard codes of a subuniverse form a closure under the identity
  -- operator, whose family equation holds by refl. Constructions that read
  -- only the standard codes of a subuniverse take them from this closure.
  ordinary : (s : Subuniverse Q o) →
    Closure Q (λ F → F) (S (Subuniverse.code s))
  ordinary s = let open Subuniverse s in record
    { interpret = inclusion
    ; empty = empty , empty-β
    ; unit = unit , unit-β
    ; two = two , two-β
    ; natural = natural , natural-β
    ; product = λ F → product (pr₁ F) (pr₂ F) ,
        product-β (pr₁ F) (pr₂ F)
    ; sum = λ F → sum (pr₁ F) (pr₂ F) , sum-β (pr₁ F) (pr₂ F)
    ; tree = λ F → tree (pr₁ F) (pr₂ F) , tree-β (pr₁ F) (pr₂ F)
    ; identity = λ a x y → identity a x y , identity-β a x y
    ; inner = λ F → F
    ; inner-β = λ F → refl
    }

------------------------------------------------------------------------
-- Operators on families

module _ {κ ℓ : Level} {V : Set κ} {S : V → Set ℓ} where

  -- f and g packaged as one operator on families of V.
  operator : Operators S → Operator S
  operator o F = Operators.f o (pr₁ F) (pr₂ F) ,
    Operators.g o (pr₁ F) (pr₂ F)

  -- An operator on families split into f and g.
  split : Operator S → Operators S
  split Ψ = record
    { f = λ a b → pr₁ (Ψ (a , b))
    ; g = λ a b → pr₂ (Ψ (a , b))
    }

  split-operator : (o : Operators S) → split (operator o) ＝ o
  split-operator o = refl

  operator-split : (Ψ : Operator S) → operator (split Ψ) ＝ Ψ
  operator-split Ψ = refl

  -- The branch of an identified family, read at a transported point.
  branch-path : {G H : Family S} (e : G ＝ H) (c : S (pr₁ H)) →
    pr₂ G (transport S (ap pr₁ e ⁻¹) c) ＝ pr₂ H c
  branch-path refl c = refl

------------------------------------------------------------------------
-- From resident reflection

module _ {κ ℓ : Level} {V : Set κ} {S : V → Set ℓ} {Q : Formers V S} where

  -- A resident reflection for the packaged operator is Setzer's
  -- subuniverse: result and branch are the two components of the inner
  -- operator, and their equations are the two components of its family
  -- equation.
  subuniverse : (o : Operators S) → Reflection Q (operator o) →
    Subuniverse Q o
  subuniverse o R = let L = Reflection.closure R in record
    { code = Reflection.carrier R
    ; inclusion = Closure.interpret L
    ; empty = pr₁ (Closure.empty L)
    ; empty-β = pr₂ (Closure.empty L)
    ; unit = pr₁ (Closure.unit L)
    ; unit-β = pr₂ (Closure.unit L)
    ; two = pr₁ (Closure.two L)
    ; two-β = pr₂ (Closure.two L)
    ; natural = pr₁ (Closure.natural L)
    ; natural-β = pr₂ (Closure.natural L)
    ; product = λ a b → pr₁ (Closure.product L (a , b))
    ; product-β = λ a b → pr₂ (Closure.product L (a , b))
    ; sum = λ a b → pr₁ (Closure.sum L (a , b))
    ; sum-β = λ a b → pr₂ (Closure.sum L (a , b))
    ; tree = λ a b → pr₁ (Closure.tree L (a , b))
    ; tree-β = λ a b → pr₂ (Closure.tree L (a , b))
    ; identity = λ a x y → pr₁ (Closure.identity L a x y)
    ; identity-β = λ a x y → pr₂ (Closure.identity L a x y)
    ; result = λ a b → pr₁ (Closure.inner L (a , b))
    ; result-β = λ a b → ap pr₁ (Closure.inner-β L (a , b))
    ; branch = λ a b c → pr₂ (Closure.inner L (a , b))
        (transport S (ap pr₁ (Closure.inner-β L (a , b)) ⁻¹) c)
    ; branch-β = λ a b c → branch-path (Closure.inner-β L (a , b)) c
    }

  -- A code-level reflector gives Setzer's rule.
  reflector : Mahlo Q → Reflects Q
  reflector M o = subuniverse o (Mahlo.reflect M (operator o))

  -- A Mahlo reflection with decoding laws, together with codes for Nₖ and
  -- +, is a Mahlo universe.
  from-reflection : MahloReflection Q → Coproducts S → Universe S
  from-reflection M C = record
    { formers = Q
    ; decoding = MahloReflection.decoding M
    ; coproducts = C
    ; reflect = reflector (MahloReflection.codeReflection M)
    }

------------------------------------------------------------------------
-- Setzer's augmentation

-- The output for a family (a , b) is N + (a × a) + 1 + f(a, b); a point of
-- each summand names a finite type, the sum of two members of b, f(a, b),
-- or a code of g.

module _ {κ ℓ : Level} {V : Set κ} {S : V → Set ℓ} (Q : Formers V S)
  (C : Coproducts S) (o : Operators S) where

  -- The summands after the first, and after the first two.
  output₂ : (a : V) → (S a → V) → V
  output₂ a b = Coproducts.plus C (Formers.unit Q) (Operators.f o a b)

  output₁ : (a : V) → (S a → V) → V
  output₁ a b =
    Coproducts.plus C (Formers.sum Q (a , (λ _ → a))) (output₂ a b)

  output : (a : V) → (S a → V) → V
  output a b = Coproducts.plus C (Formers.natural Q) (output₁ a b)

module _ {κ ℓ : Level} {V : Set κ} {S : V → Set ℓ} (Q : Formers V S)
  (o : Operators S) where

  -- The code named by a point of the last two summands.
  read₂ : (a : V) (b : S a → V) →
    S (Formers.unit Q) ⊎ S (Operators.f o a b) → V
  read₂ a b (inl _) = Operators.f o a b
  read₂ a b (inr c) = Operators.g o a b c

module _ {κ ℓ : Level} {V : Set κ} {S : V → Set ℓ} {Q : Formers V S}
  (L : DecodingLaws Q) (C : Coproducts S) (o : Operators S) where

  -- The code named by a point of each summand.
  read₁ : (a : V) (b : S a → V) →
    S (Formers.sum Q (a , (λ _ → a))) ⊎ S (output₂ Q C o a b) → V
  read₁ a b (inl p) =
    let q = transport (λ X → X) (DecodingLaws.sum-β L a (λ _ → a)) p in
    Coproducts.plus C (b (pr₁ q)) (b (pr₂ q))
  read₁ a b (inr r) =
    read₂ Q o a b
      (transport (λ X → X)
        (Coproducts.plus-β C (Formers.unit Q) (Operators.f o a b)) r)

  read : (a : V) (b : S a → V) →
    S (Formers.natural Q) ⊎ S (output₁ Q C o a b) → V
  read a b (inl n) =
    Coproducts.finite C
      (lower (transport (λ X → X) (DecodingLaws.natural-β L) n))
  read a b (inr r) =
    read₁ a b
      (transport (λ X → X)
        (Coproducts.plus-β C (Formers.sum Q (a , (λ _ → a)))
          (output₂ Q C o a b))
        r)

  augmented : Operators S
  augmented = record
    { f = output Q C o
    ; g = λ a b c →
        read a b
          (transport (λ X → X)
            (Coproducts.plus-β C (Formers.natural Q) (output₁ Q C o a b)) c)
    }

  -- Points of the output naming each kind of code.
  finite-point : (a : V) (b : S a → V) → ℕ → S (output Q C o a b)
  finite-point a b k =
    let e₀ = Coproducts.plus-β C (Formers.natural Q) (output₁ Q C o a b)
    in transport (λ X → X) (e₀ ⁻¹)
         (inl (transport (λ X → X) (DecodingLaws.natural-β L ⁻¹) (lift k)))

  pair-point : (a : V) (b : S a → V) → S a → S a → S (output Q C o a b)
  pair-point a b x y =
    let e₀ = Coproducts.plus-β C (Formers.natural Q) (output₁ Q C o a b)
        e₁ = Coproducts.plus-β C (Formers.sum Q (a , (λ _ → a)))
          (output₂ Q C o a b)
        eₛ = DecodingLaws.sum-β L a (λ _ → a)
    in transport (λ X → X) (e₀ ⁻¹)
         (inr (transport (λ X → X) (e₁ ⁻¹)
           (inl (transport (λ X → X) (eₛ ⁻¹) (x , y)))))

  result-point : (a : V) (b : S a → V) → S (output Q C o a b)
  result-point a b =
    let e₀ = Coproducts.plus-β C (Formers.natural Q) (output₁ Q C o a b)
        e₁ = Coproducts.plus-β C (Formers.sum Q (a , (λ _ → a)))
          (output₂ Q C o a b)
        e₂ = Coproducts.plus-β C (Formers.unit Q) (Operators.f o a b)
    in transport (λ X → X) (e₀ ⁻¹)
         (inr (transport (λ X → X) (e₁ ⁻¹)
           (inr (transport (λ X → X) (e₂ ⁻¹)
             (inl (transport (λ X → X) (DecodingLaws.unit-β L ⁻¹)
               (lift ⋆)))))))

  branch-point : (a : V) (b : S a → V) → S (Operators.f o a b) →
    S (output Q C o a b)
  branch-point a b c =
    let e₀ = Coproducts.plus-β C (Formers.natural Q) (output₁ Q C o a b)
        e₁ = Coproducts.plus-β C (Formers.sum Q (a , (λ _ → a)))
          (output₂ Q C o a b)
        e₂ = Coproducts.plus-β C (Formers.unit Q) (Operators.f o a b)
    in transport (λ X → X) (e₀ ⁻¹)
         (inr (transport (λ X → X) (e₁ ⁻¹)
           (inr (transport (λ X → X) (e₂ ⁻¹) (inr c)))))

  -- Each point reads back to the code it names.
  read-finite : (a : V) (b : S a → V) (k : ℕ) →
    Operators.g augmented a b (finite-point a b k) ＝ Coproducts.finite C k
  read-finite a b k =
    let e₀ = Coproducts.plus-β C (Formers.natural Q) (output₁ Q C o a b)
        eₙ = DecodingLaws.natural-β L
    in ap (read a b)
         (back-and-forth-transport (λ X → X) e₀
           (inl (transport (λ X → X) (eₙ ⁻¹) (lift k))))
       ∙ ap (λ z → Coproducts.finite C (lower z))
           (back-and-forth-transport (λ X → X) eₙ (lift k))

  read-pair : (a : V) (b : S a → V) (x y : S a) →
    Operators.g augmented a b (pair-point a b x y) ＝
      Coproducts.plus C (b x) (b y)
  read-pair a b x y =
    let e₀ = Coproducts.plus-β C (Formers.natural Q) (output₁ Q C o a b)
        e₁ = Coproducts.plus-β C (Formers.sum Q (a , (λ _ → a)))
          (output₂ Q C o a b)
        eₛ = DecodingLaws.sum-β L a (λ _ → a)
        p = transport (λ X → X) (eₛ ⁻¹) (x , y)
        r = transport (λ X → X) (e₁ ⁻¹) (inl p)
    in ap (read a b) (back-and-forth-transport (λ X → X) e₀ (inr r))
       ∙ ap (read₁ a b) (back-and-forth-transport (λ X → X) e₁ (inl p))
       ∙ ap (λ q → Coproducts.plus C (b (pr₁ q)) (b (pr₂ q)))
           (back-and-forth-transport (λ X → X) eₛ (x , y))

  read-result : (a : V) (b : S a → V) →
    Operators.g augmented a b (result-point a b) ＝ Operators.f o a b
  read-result a b =
    let e₀ = Coproducts.plus-β C (Formers.natural Q) (output₁ Q C o a b)
        e₁ = Coproducts.plus-β C (Formers.sum Q (a , (λ _ → a)))
          (output₂ Q C o a b)
        e₂ = Coproducts.plus-β C (Formers.unit Q) (Operators.f o a b)
        u = transport (λ X → X) (DecodingLaws.unit-β L ⁻¹) (lift ⋆)
        r₂ = transport (λ X → X) (e₂ ⁻¹) (inl u)
        r₁ = transport (λ X → X) (e₁ ⁻¹) (inr r₂)
    in ap (read a b) (back-and-forth-transport (λ X → X) e₀ (inr r₁))
       ∙ ap (read₁ a b) (back-and-forth-transport (λ X → X) e₁ (inr r₂))
       ∙ ap (read₂ Q o a b) (back-and-forth-transport (λ X → X) e₂ (inl u))

  read-branch : (a : V) (b : S a → V) (c : S (Operators.f o a b)) →
    Operators.g augmented a b (branch-point a b c) ＝ Operators.g o a b c
  read-branch a b c =
    let e₀ = Coproducts.plus-β C (Formers.natural Q) (output₁ Q C o a b)
        e₁ = Coproducts.plus-β C (Formers.sum Q (a , (λ _ → a)))
          (output₂ Q C o a b)
        e₂ = Coproducts.plus-β C (Formers.unit Q) (Operators.f o a b)
        r₂ = transport (λ X → X) (e₂ ⁻¹) (inr c)
        r₁ = transport (λ X → X) (e₁ ⁻¹) (inr r₂)
    in ap (read a b) (back-and-forth-transport (λ X → X) e₀ (inr r₁))
       ∙ ap (read₁ a b) (back-and-forth-transport (λ X → X) e₁ (inr r₂))
       ∙ ap (read₂ Q o a b) (back-and-forth-transport (λ X → X) e₂ (inr c))

------------------------------------------------------------------------
-- The two-point code of a subuniverse

module _ {κ ℓ : Level} {V : Set κ} {S : V → Set ℓ} {Q : Formers V S}
  {o : Operators S} (L : DecodingLaws Q) (s : Subuniverse Q o) where

  -- It decodes to 𝟚.
  two-decoding :
    Decode S (Subuniverse.inclusion s) (Subuniverse.two s) ＝ Lift ℓ 𝟚
  two-decoding = ap S (Subuniverse.two-β s) ∙ DecodingLaws.two-β L

  two-point : 𝟚 → Decode S (Subuniverse.inclusion s) (Subuniverse.two s)
  two-point t = transport (λ X → X) (two-decoding ⁻¹) (lift t)

  -- The family on the two-point code with members x and y.
  choose : S (Subuniverse.code s) → S (Subuniverse.code s) →
    Decode S (Subuniverse.inclusion s) (Subuniverse.two s) →
    S (Subuniverse.code s)
  choose x y t = 𝟚-cases x y (lower (transport (λ X → X) two-decoding t))

  chosen : (x y : S (Subuniverse.code s)) (t : 𝟚) →
    choose x y (two-point t) ＝ 𝟚-cases x y t
  chosen x y t =
    ap (λ z → 𝟚-cases x y (lower z))
      (back-and-forth-transport (λ X → X) two-decoding (lift t))

------------------------------------------------------------------------
-- Finite types and binary sums in every subuniverse

module _ {κ ℓ : Level} {V : Set κ} {S : V → Set ℓ} {Q : Formers V S}
  (L : DecodingLaws Q) (C : Coproducts S) (o : Operators S)
  (s : Subuniverse Q (augmented L C o)) where

  -- The subuniverse of the augmented pair names f, g, the finite types and
  -- the sums of its members through its branch code.
  closing : Closed Q C o
  closing = let open Subuniverse s in record
    { subuniverse = record
      { code = code
      ; inclusion = inclusion
      ; empty = empty
      ; empty-β = empty-β
      ; unit = unit
      ; unit-β = unit-β
      ; two = two
      ; two-β = two-β
      ; natural = natural
      ; natural-β = natural-β
      ; product = product
      ; product-β = product-β
      ; sum = sum
      ; sum-β = sum-β
      ; tree = tree
      ; tree-β = tree-β
      ; identity = identity
      ; identity-β = identity-β
      ; result = λ a b → branch a b
          (result-point L C o (inclusion a) (λ x → inclusion (b x)))
      ; result-β = λ a b →
          branch-β a b
            (result-point L C o (inclusion a) (λ x → inclusion (b x)))
          ∙ read-result L C o (inclusion a) (λ x → inclusion (b x))
      ; branch = λ a b c → branch a b
          (branch-point L C o (inclusion a) (λ x → inclusion (b x)) c)
      ; branch-β = λ a b c →
          branch-β a b
            (branch-point L C o (inclusion a) (λ x → inclusion (b x)) c)
          ∙ read-branch L C o (inclusion a) (λ x → inclusion (b x)) c
      }
    ; finite = λ k → branch natural (λ _ → natural)
        (finite-point L C o (inclusion natural) (λ _ → inclusion natural) k)
    ; finite-β = λ k →
        branch-β natural (λ _ → natural)
          (finite-point L C o (inclusion natural) (λ _ → inclusion natural)
            k)
        ∙ read-finite L C o (inclusion natural) (λ _ → inclusion natural) k
    ; plus = λ x y → branch two (choose L s x y)
        (pair-point L C o (inclusion two) (λ t → inclusion (choose L s x y t))
          (two-point L s ₀) (two-point L s ₁))
    ; plus-β = λ x y →
        branch-β two (choose L s x y)
          (pair-point L C o (inclusion two)
            (λ t → inclusion (choose L s x y t))
            (two-point L s ₀) (two-point L s ₁))
        ∙ read-pair L C o (inclusion two)
            (λ t → inclusion (choose L s x y t))
            (two-point L s ₀) (two-point L s ₁)
        ∙ ap₂ (Coproducts.plus C) (ap inclusion (chosen L s x y ₀))
            (ap inclusion (chosen L s x y ₁))
    }

module _ {κ ℓ : Level} {V : Set κ} {S : V → Set ℓ} where

  -- In a Mahlo universe every subuniverse can be taken closed under Nₖ and
  -- +: the subuniverse of the augmented pair, closed by `closing`.
  closed : (M : Universe S) (o : Operators S) →
    Closed (Universe.formers M) (Universe.coproducts M) o
  closed M o =
    closing (Universe.decoding M) (Universe.coproducts M) o
      (Universe.reflect M
        (augmented (Universe.decoding M) (Universe.coproducts M) o))

------------------------------------------------------------------------
-- Back to resident reflection, under function extensionality

module _ {κ ℓ : Level} {V : Set κ} {S : V → Set ℓ} where

  -- Families agree when their bases agree and their branches agree
  -- pointwise along that identity.
  pair-path : ((x : V) → FunExt (S x) (λ s → V)) → {x y : V}
    {h : S x → V} {k : S y → V} (e : x ＝ y) →
    ((s : S x) → h s ＝ k (transport S e s)) →
    _＝_ {A = Family S} (x , h) (y , k)
  pair-path funext {x} {.x} {h} {k} refl p =
    ap (λ h′ → x , h′) (funext x h k p)

module _ {κ ℓ : Level} {V : Set κ} {S : V → Set ℓ} {Q : Formers V S} where

  -- Setzer's subuniverse for the split operator is a resident reflection.
  reflection : ((x : V) → FunExt (S x) (λ s → V)) → (Ψ : Operator S) →
    Subuniverse Q (split Ψ) → Reflection Q Ψ
  reflection funext Ψ s = let open Subuniverse s in record
    { carrier = code
    ; closure = record
      { interpret = inclusion
      ; empty = empty , empty-β
      ; unit = unit , unit-β
      ; two = two , two-β
      ; natural = natural , natural-β
      ; product = λ F → product (pr₁ F) (pr₂ F) ,
          product-β (pr₁ F) (pr₂ F)
      ; sum = λ F → sum (pr₁ F) (pr₂ F) , sum-β (pr₁ F) (pr₂ F)
      ; tree = λ F → tree (pr₁ F) (pr₂ F) , tree-β (pr₁ F) (pr₂ F)
      ; identity = λ a x y → identity a x y , identity-β a x y
      ; inner = λ F → result (pr₁ F) (pr₂ F) ,
          (λ y → branch (pr₁ F) (pr₂ F)
            (transport S (result-β (pr₁ F) (pr₂ F)) y))
      ; inner-β = λ F → pair-path funext (result-β (pr₁ F) (pr₂ F))
          (λ y → branch-β (pr₁ F) (pr₂ F)
            (transport S (result-β (pr₁ F) (pr₂ F)) y))
      }
    }

module _ {κ ℓ : Level} {V : Set κ} {S : V → Set ℓ} where

  -- A Mahlo universe gives a Mahlo reflection with decoding laws.
  to-reflection : ((x : V) → FunExt (S x) (λ s → V)) → (M : Universe S) →
    MahloReflection (Universe.formers M)
  to-reflection funext M = record
    { codeReflection = record
        { reflect = λ Ψ → reflection funext Ψ (Universe.reflect M (split Ψ))
        }
    ; decoding = Universe.decoding M
    }

module _ {κ ℓ : Level} {V : Set κ} {S : V → Set ℓ} {Q : Formers V S} where

  -- The return to resident reflection keeps the original resident carrier
  -- and its interpretation.
  carrier-return : (funext : (x : V) → FunExt (S x) (λ s → V))
    (M : MahloReflection Q) (C : Coproducts S) (Ψ : Operator S) →
    Reflection.carrier
      (Decoding.reflect (to-reflection funext (from-reflection M C)) Ψ)
      ＝ Reflection.carrier (Decoding.reflect M Ψ)
  carrier-return funext M C Ψ = refl

  interpret-return : (funext : (x : V) → FunExt (S x) (λ s → V))
    (M : MahloReflection Q) (C : Coproducts S) (Ψ : Operator S) →
    Closure.interpret (Reflection.closure
      (Decoding.reflect (to-reflection funext (from-reflection M C)) Ψ))
      ＝ Closure.interpret (Reflection.closure (Decoding.reflect M Ψ))
  interpret-return funext M C Ψ = refl
