{-# OPTIONS --safe --without-K #-}

module SPT.IR.Polynomial.Outputs where

-- Indexed polynomial induction–recursion with outputs polynomial in
-- types: the output type at each index is the information of a one-sort
-- polynomial code over Set ℓ (Σ, Π over small types, constants, Set ℓ;
-- families of types are one). An element of such a type is a tree of
-- types: its components (`Component`, `component`). A scheme with a code
-- for each output (`Outputs`) gives type-valued rules: each recursive input
-- is replaced by its output's code (`at`, `substitute`, the substitution
-- behind the composition of polynomial codes in Ghani, McBride, Nordvall
-- Forsberg and Spahn, §4.2), and each rule selects one component of its
-- output (`types`). A small algebra of those rules gives a small algebra
-- of the scheme, on structured codes (`structured`): an argument over the
-- structured family is an argument of the substituted code
-- (`translate`), and the names of an output's components assemble into a
-- structured code reading out to it (`assemble`, `named`, `algebra`),
-- under extensionality for families of information over the arities.

open import SPT.Base

open import SPT.IR.Polynomial using
  (Poly; var; con; sigma; pi; Family; carrier; readout; Args; info;
   Description; described; shape; output; Scheme; Rules; scheme;
   Extensionality)
open import SPT.IR.Polynomial.Action using (pair-info)
open import SPT.IR.Polynomial.Algebra using (Algebra)

------------------------------------------------------------------------
-- Components of a polynomial type

-- The types inside an element of the information of a one-sort code: one
-- at each recursive input, none at a constant.

module _ {ℓ : Level} where

  Component :
    {X : Set (lsuc ℓ)} → Poly ℓ (lsuc ℓ) (λ (_ : 𝟙) → Set ℓ) X → X
    → Set ℓ
  Component (var _) T = Lift ℓ 𝟙
  Component (con B) b = Lift ℓ 𝟘
  Component (sigma p q) (x , y) = Component p x ⊎ Component (q x) y
  Component (pi A p) f = Σ A (λ a → Component (p a) (f a))

  component :
    {X : Set (lsuc ℓ)} (c : Poly ℓ (lsuc ℓ) (λ (_ : 𝟙) → Set ℓ) X) (x : X)
    → Component c x → Set ℓ
  component (var _) T _ = T
  component (con B) b (lift ())
  component (sigma p q) (x , y) (inl z) = component p x z
  component (sigma p q) (x , y) (inr z) = component (q x) y z
  component (pi A p) f (a , z) = component (p a) (f a) z

  -- A one-sort code with its recursive inputs at the index i.
  at :
    {ι : Level} {I : Set ι} {X : Set (lsuc ℓ)}
    → Poly ℓ (lsuc ℓ) (λ (_ : 𝟙) → Set ℓ) X → I
    → Poly ℓ (lsuc ℓ) (λ (_ : I) → Set ℓ) X
  at (var _) i = var i
  at (con B) i = con B
  at (sigma p q) i = sigma (at p i) (λ x → at (q x) i)
  at (pi A p) i = pi A (λ a → at (p a) i)

------------------------------------------------------------------------
-- Schemes with polynomial outputs

-- A scheme whose output type at each index is the information of a
-- one-sort code.

record Outputs (ℓ : Level) : Set (lsuc (lsuc ℓ)) where
  field
    underlying : Scheme ℓ (lsuc ℓ)
    form :
      (i : Scheme.Index underlying)
      → Poly ℓ (lsuc ℓ) (λ (_ : 𝟙) → Set ℓ) (Scheme.Data underlying i)

module _
  {ℓ : Level} (s : Scheme ℓ (lsuc ℓ))
  (form :
    (i : Scheme.Index s)
    → Poly ℓ (lsuc ℓ) (λ (_ : 𝟙) → Set ℓ) (Scheme.Data s i))
  where

  open Scheme s using (Index; Data; rule)

  -- Each recursive input replaced by the code of its output.
  substitute :
    {X : Set (lsuc ℓ)} → Poly ℓ (lsuc ℓ) Data X
    → Poly ℓ (lsuc ℓ) (λ (_ : Index) → Set ℓ) X
  substitute (var j) = at (form j) j
  substitute (con B) = con B
  substitute (sigma p q) = sigma (substitute p) (λ x → substitute (q x))
  substitute (pi A p) = pi A (λ a → substitute (p a))

  -- The type-valued rules: at each index the substituted rule, followed
  -- by the choice of one component of its output, read out to that
  -- component.
  types : Rules ℓ
  types = record
    { Index = Index
    ; rule = λ i →
        described
          (sigma (substitute (shape (rule i)))
            (λ x → con (Component (form i) (output (rule i) x))))
          (λ v →
            component (form i) (output (rule i) (pr₁ v)) (lower (pr₂ v)))
    }

  -- A type-valued family seen through the output codes: at each index
  -- the structured elements, read out to their information.
  structured :
    Family ℓ (lsuc ℓ) (λ (_ : Index) → Set ℓ) → Family ℓ (lsuc ℓ) Data
  structured Z = record
    { carrier = λ i → Args (at (form i) i) Z
    ; readout = λ i → info (at (form i) i) Z
    }

  -- An argument over the structured family is an argument of the
  -- substituted code, with the same information.
  translate :
    Extensionality ℓ (lsuc ℓ)
    → (Z : Family ℓ (lsuc ℓ) (λ (_ : Index) → Set ℓ))
    → {X : Set (lsuc ℓ)} (p : Poly ℓ (lsuc ℓ) Data X)
    (a : Args p (structured Z))
    → Σ (Args (substitute p) Z)
        (λ b → info (substitute p) Z b ＝ info p (structured Z) a)
  translate extensionality Z (var j) a = a , refl
  translate extensionality Z (con B) a = a , refl
  translate extensionality Z (sigma {X} {Y} p q) (a , b) =
    let left = translate extensionality Z p a
        right = translate extensionality Z (q (info p (structured Z) a)) b
    in
    ( pr₁ left
    , transport (λ x → Args (substitute (q x)) Z) (pr₂ left ⁻¹)
        (pr₁ right)) ,
    ( pair-info (λ x → Args (substitute (q x)) Z) Y
        (λ x → info (substitute (q x)) Z) (pr₂ left ⁻¹) (pr₁ right)
    ∙ ap (λ y → (info p (structured Z) a , y)) (pr₂ right))
  translate extensionality Z (pi A {Y} p) f =
    let branch = λ a → translate extensionality Z (p a) (f a)
    in
    (λ a → pr₁ (branch a)) ,
    extensionality A Y
      (λ a → info (substitute (p a)) Z (pr₁ (branch a)))
      (λ a → info (p a) (structured Z) (f a))
      (λ a → pr₂ (branch a))

------------------------------------------------------------------------
-- Structured codes from names of components

-- An element at index i naming each component of an information x
-- assembles into a structured element whose information is x.

assemble :
  {ℓ ι : Level} → Extensionality ℓ (lsuc ℓ) → {I : Set ι}
  (Z : Family ℓ (lsuc ℓ) (λ (_ : I) → Set ℓ)) (i : I)
  {X : Set (lsuc ℓ)} (c : Poly ℓ (lsuc ℓ) (λ (_ : 𝟙) → Set ℓ) X) (x : X)
  → ((z : Component c x)
    → Σ (carrier Z i) (λ k → readout Z i k ＝ component c x z))
  → Σ (Args (at c i) Z) (λ k → info (at c i) Z k ＝ x)
assemble extensionality Z i (var _) T names = names (lift ⋆)
assemble extensionality Z i (con B) (lift b) names = b , refl
assemble extensionality Z i (sigma {X} {Y} p q) (x , y) names =
  let left = assemble extensionality Z i p x (λ z → names (inl z))
      right = assemble extensionality Z i (q x) y (λ z → names (inr z))
  in
  ( pr₁ left
  , transport (λ u → Args (at (q u) i) Z) (pr₂ left ⁻¹) (pr₁ right)) ,
  ( pair-info (λ u → Args (at (q u) i) Z) Y (λ u → info (at (q u) i) Z)
      (pr₂ left ⁻¹) (pr₁ right)
  ∙ ap (λ v → (x , v)) (pr₂ right))
assemble extensionality Z i (pi A {Y} p) f names =
  let branch =
        λ a → assemble extensionality Z i (p a) (f a) (λ z → names (a , z))
  in
  (λ a → pr₁ (branch a)) ,
  extensionality A Y
    (λ a → info (at (p a) i) Z (pr₁ (branch a))) f
    (λ a → pr₂ (branch a))

-- A component chosen at one information, moved back along an identity of
-- informations, names the same type.
moved :
  {α β ν : Level} {A : Set α} (C : A → Set β) {B : Set ν}
  (g : (x : A) → C x → B) {x y : A} (e : x ＝ y) (z : C y)
  → g x (transport C (e ⁻¹) z) ＝ g y z
moved C g refl z = refl

------------------------------------------------------------------------
-- The small algebra

module _
  {ℓ : Level} (s : Scheme ℓ (lsuc ℓ))
  (form :
    (i : Scheme.Index s)
    → Poly ℓ (lsuc ℓ) (λ (_ : 𝟙) → Set ℓ) (Scheme.Data s i))
  where

  open Scheme s using (Index; Data; rule)

  -- At an argument over the structured family, every component of the
  -- output is named by the type-valued operation at the translated
  -- argument with that component chosen.
  named :
    (extensionality : Extensionality ℓ (lsuc ℓ))
    (N : Algebra (scheme (types s form))) (i : Index)
    (a : Args (shape (rule i)) (structured s form (Algebra.family N)))
    → Σ (Args (at (form i) i) (Algebra.family N))
        (λ k →
          info (at (form i) i) (Algebra.family N) k
          ＝ output (rule i)
              (info (shape (rule i)) (structured s form (Algebra.family N)) a))
  named extensionality N i a =
    let t =
          translate s form extensionality (Algebra.family N) (shape (rule i)) a
    in
    assemble extensionality (Algebra.family N) i (form i)
      (output (rule i)
        (info (shape (rule i)) (structured s form (Algebra.family N)) a))
      (λ z →
        Algebra.operation N i
          ( pr₁ t
          , transport (λ x → Component (form i) (output (rule i) x))
              (pr₂ t ⁻¹) z) ,
        ( Algebra.law N i
            ( pr₁ t
            , transport (λ x → Component (form i) (output (rule i) x))
                (pr₂ t ⁻¹) z)
        ∙ moved (λ x → Component (form i) (output (rule i) x))
            (λ x → component (form i) (output (rule i) x)) (pr₂ t) z))

  algebra :
    Extensionality ℓ (lsuc ℓ) → Algebra (scheme (types s form))
    → Algebra s
  algebra extensionality N = record
    { family = structured s form (Algebra.family N)
    ; operation = λ i a → pr₁ (named extensionality N i a)
    ; law = λ i a → pr₂ (named extensionality N i a)
    }
