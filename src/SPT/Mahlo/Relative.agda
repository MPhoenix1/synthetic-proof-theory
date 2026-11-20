{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Relative where

-- The induction–recursive closure of an operator Ψ over a Tarski family (C , D)
-- with formers Q. Its codes (`Generated Q Ψ`) are the selected formers, the
-- product, sum and tree of a family of codes, the identity type of two points,
-- and Ψ's result and branch codes at a family of codes; `interpret` sends each
-- code to the parent code it names, by recursion alongside the codes:
--
--   interpret (result a b) = pr₁ (Ψ (interpret a , interpret ∘ b)).
--
-- The codes carry a closure of Ψ (`closure`). They have dependent
-- induction, with the hypothesis at every code a code is formed from
-- (`Methods`, `induction`), computing at each constructor by refl
-- (`induction-empty`, …, `induction-branch`). This is the only
-- induction–recursion the Mahlo rule needs.

open import SPT.Base
open import SPT.Mahlo.Specification using (Operator; Formers; Closure)

------------------------------------------------------------------------
-- The codes and the parent codes they name

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} (Q : Formers C D)
  (Ψ : Operator D) where

  data Generated : Set ℓ
  interpret : Generated → C

  data Generated where
    empty unit two natural : Generated
    product sum tree result : (a : Generated) →
      (D (interpret a) → Generated) → Generated
    identity : (a : Generated) → D (interpret a) → D (interpret a) →
      Generated
    branch : (a : Generated) (b : D (interpret a) → Generated) →
      D (pr₁ (Ψ (interpret a , (λ x → interpret (b x))))) → Generated

  interpret empty = Formers.empty Q
  interpret unit = Formers.unit Q
  interpret two = Formers.two Q
  interpret natural = Formers.natural Q
  interpret (product a b) =
    Formers.product Q (interpret a , (λ x → interpret (b x)))
  interpret (sum a b) = Formers.sum Q (interpret a , (λ x → interpret (b x)))
  interpret (tree a b) =
    Formers.tree Q (interpret a , (λ x → interpret (b x)))
  interpret (identity a x y) = Formers.identity Q (interpret a) x y
  interpret (result a b) = pr₁ (Ψ (interpret a , (λ x → interpret (b x))))
  interpret (branch a b y) =
    pr₂ (Ψ (interpret a , (λ x → interpret (b x)))) y

  -- The codes form a closure of Ψ, each name by refl.
  closure : Closure Q Ψ Generated
  closure = record
    { interpret = interpret
    ; empty = empty , refl
    ; unit = unit , refl
    ; two = two , refl
    ; natural = natural , refl
    ; product = λ F → product (pr₁ F) (pr₂ F) , refl
    ; sum = λ F → sum (pr₁ F) (pr₂ F) , refl
    ; tree = λ F → tree (pr₁ F) (pr₂ F) , refl
    ; identity = λ a x y → identity a x y , refl
    ; inner = λ F →
        result (pr₁ F) (pr₂ F) , (λ y → branch (pr₁ F) (pr₂ F) y)
    ; inner-β = λ F → refl
    }

  -- A method for each constructor, with the hypothesis at every code it is
  -- formed from; the branch method also keeps the selected point.
  record Methods {ν : Level} (P : Generated → Set ν) : Set (ℓ ⊔ ν) where
    field
      on-empty : P empty
      on-unit : P unit
      on-two : P two
      on-natural : P natural
      on-product : (a : Generated) (b : D (interpret a) → Generated) →
        P a → ((x : D (interpret a)) → P (b x)) → P (product a b)
      on-sum : (a : Generated) (b : D (interpret a) → Generated) →
        P a → ((x : D (interpret a)) → P (b x)) → P (sum a b)
      on-tree : (a : Generated) (b : D (interpret a) → Generated) →
        P a → ((x : D (interpret a)) → P (b x)) → P (tree a b)
      on-identity : (a : Generated) (x y : D (interpret a)) →
        P a → P (identity a x y)
      on-result : (a : Generated) (b : D (interpret a) → Generated) →
        P a → ((x : D (interpret a)) → P (b x)) → P (result a b)
      on-branch : (a : Generated) (b : D (interpret a) → Generated)
        (y : D (pr₁ (Ψ (interpret a , (λ x → interpret (b x)))))) →
        P a → ((x : D (interpret a)) → P (b x)) → P (branch a b y)

------------------------------------------------------------------------
-- Induction

module _ {κ ℓ ν : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D}
  {Ψ : Operator D} {P : Generated Q Ψ → Set ν} where

  induction : Methods Q Ψ P → (a : Generated Q Ψ) → P a
  induction m empty = Methods.on-empty m
  induction m unit = Methods.on-unit m
  induction m two = Methods.on-two m
  induction m natural = Methods.on-natural m
  induction m (product a b) =
    Methods.on-product m a b (induction m a) (λ x → induction m (b x))
  induction m (sum a b) =
    Methods.on-sum m a b (induction m a) (λ x → induction m (b x))
  induction m (tree a b) =
    Methods.on-tree m a b (induction m a) (λ x → induction m (b x))
  induction m (identity a x y) =
    Methods.on-identity m a x y (induction m a)
  induction m (result a b) =
    Methods.on-result m a b (induction m a) (λ x → induction m (b x))
  induction m (branch a b y) =
    Methods.on-branch m a b y (induction m a) (λ x → induction m (b x))

  induction-empty : (m : Methods Q Ψ P) →
    induction m empty ＝ Methods.on-empty m
  induction-empty m = refl

  induction-unit : (m : Methods Q Ψ P) →
    induction m unit ＝ Methods.on-unit m
  induction-unit m = refl

  induction-two : (m : Methods Q Ψ P) →
    induction m two ＝ Methods.on-two m
  induction-two m = refl

  induction-natural : (m : Methods Q Ψ P) →
    induction m natural ＝ Methods.on-natural m
  induction-natural m = refl

  induction-product : (m : Methods Q Ψ P) (a : Generated Q Ψ)
    (b : D (interpret Q Ψ a) → Generated Q Ψ) →
    induction m (product a b)
      ＝ Methods.on-product m a b (induction m a) (λ x → induction m (b x))
  induction-product m a b = refl

  induction-sum : (m : Methods Q Ψ P) (a : Generated Q Ψ)
    (b : D (interpret Q Ψ a) → Generated Q Ψ) →
    induction m (sum a b)
      ＝ Methods.on-sum m a b (induction m a) (λ x → induction m (b x))
  induction-sum m a b = refl

  induction-tree : (m : Methods Q Ψ P) (a : Generated Q Ψ)
    (b : D (interpret Q Ψ a) → Generated Q Ψ) →
    induction m (tree a b)
      ＝ Methods.on-tree m a b (induction m a) (λ x → induction m (b x))
  induction-tree m a b = refl

  induction-identity : (m : Methods Q Ψ P) (a : Generated Q Ψ)
    (x y : D (interpret Q Ψ a)) →
    induction m (identity a x y) ＝ Methods.on-identity m a x y (induction m a)
  induction-identity m a x y = refl

  induction-result : (m : Methods Q Ψ P) (a : Generated Q Ψ)
    (b : D (interpret Q Ψ a) → Generated Q Ψ) →
    induction m (result a b)
      ＝ Methods.on-result m a b (induction m a) (λ x → induction m (b x))
  induction-result m a b = refl

  induction-branch : (m : Methods Q Ψ P) (a : Generated Q Ψ)
    (b : D (interpret Q Ψ a) → Generated Q Ψ)
    (y : D (pr₁ (Ψ (interpret Q Ψ a , (λ x → interpret Q Ψ (b x)))))) →
    induction m (branch a b y)
      ＝ Methods.on-branch m a b y (induction m a) (λ x → induction m (b x))
  induction-branch m a b y = refl
