{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Residence.Constructors where

-- One layer of constructors over a family interpreted in a fixed parent.
-- `Code` retains the family arguments and the operator's actual result
-- positions; `interpret` reads the selected parent formers and outputs.
-- `inner` returns Ψ's family on the new layer with no transport: the result
-- code's label is Ψ's output itself, so the branches take its decoding as
-- it is. Its square with Ψ under `image`, `inner-square`, holds by refl.
-- `map h k` has source interpretation literally λ a → k (h a). Its
-- interpretation, identity and composition laws follow by constructor
-- cases, each by refl. This is the represented composite source, not a
-- transfer along an arbitrary supplied identity of interpretations.

open import SPT.Base
open import SPT.Mahlo.Specification using (Family; Formers; Operator)
open import SPT.Mahlo.Residence.Families using (image)

------------------------------------------------------------------------
-- One layer, without recursion

data Code
  {κ ℓ α : Level} {C : Set κ} {D : C → Set ℓ}
  (Ψ : Operator D) (A : Set α) (j : A → C) : Set (ℓ ⊔ α) where
  empty unit two natural : Code Ψ A j
  product sum tree result :
    (a : A) → (D (j a) → A) → Code Ψ A j
  identity : (a : A) → D (j a) → D (j a) → Code Ψ A j
  branch :
    (a : A) (b : D (j a) → A)
    → D (pr₁ (Ψ (j a , (λ x → j (b x))))) → Code Ψ A j

module _
  {κ ℓ α : Level} {C : Set κ} {D : C → Set ℓ}
  {Ψ : Operator D} {A : Set α} {j : A → C}
  where

  interpret : Formers C D → Code Ψ A j → C
  interpret Q empty = Formers.empty Q
  interpret Q unit = Formers.unit Q
  interpret Q two = Formers.two Q
  interpret Q natural = Formers.natural Q
  interpret Q (product a b) =
    Formers.product Q (j a , (λ x → j (b x)))
  interpret Q (sum a b) = Formers.sum Q (j a , (λ x → j (b x)))
  interpret Q (tree a b) = Formers.tree Q (j a , (λ x → j (b x)))
  interpret Q (identity a x y) = Formers.identity Q (j a) x y
  interpret Q (result a b) = pr₁ (Ψ (j a , (λ x → j (b x))))
  interpret Q (branch a b i) = pr₂ (Ψ (j a , (λ x → j (b x)))) i

------------------------------------------------------------------------
-- The operator's family on the new layer, without transport

module _
  {κ ℓ α : Level} {C : Set κ} {D : C → Set ℓ} {A : Set α}
  where

  inner : (Q : Formers C D) (Ψ : Operator D) (j : A → C)
    → Family (λ a → D (j a))
    → Family (λ (c : Code Ψ A j) → D (interpret Q c))
  inner Q Ψ j (a , b) = result a b , branch a b

  inner-square : (Q : Formers C D) (Ψ : Operator D) (j : A → C)
    (F : Family (λ a → D (j a)))
    → image D (interpret Q) (inner Q Ψ j F) ＝ Ψ (image D j F)
  inner-square Q Ψ j (a , b) = refl

------------------------------------------------------------------------
-- Maps with the composite source interpretation

module _
  {κ ℓ α β : Level} {C : Set κ} {D : C → Set ℓ}
  {Ψ : Operator D} {A : Set α} {B : Set β}
  where

  map :
    (h : A → B) (k : B → C)
    → Code Ψ A (λ a → k (h a)) → Code Ψ B k
  map h k empty = empty
  map h k unit = unit
  map h k two = two
  map h k natural = natural
  map h k (product a b) = product (h a) (λ x → h (b x))
  map h k (sum a b) = sum (h a) (λ x → h (b x))
  map h k (tree a b) = tree (h a) (λ x → h (b x))
  map h k (identity a x y) = identity (h a) x y
  map h k (result a b) = result (h a) (λ x → h (b x))
  map h k (branch a b i) = branch (h a) (λ x → h (b x)) i

  interpret-map :
    (Q : Formers C D) (h : A → B) (k : B → C)
    (c : Code Ψ A (λ a → k (h a)))
    → interpret Q (map h k c) ＝ interpret Q c
  interpret-map Q h k empty = refl
  interpret-map Q h k unit = refl
  interpret-map Q h k two = refl
  interpret-map Q h k natural = refl
  interpret-map Q h k (product a b) = refl
  interpret-map Q h k (sum a b) = refl
  interpret-map Q h k (tree a b) = refl
  interpret-map Q h k (identity a x y) = refl
  interpret-map Q h k (result a b) = refl
  interpret-map Q h k (branch a b i) = refl

------------------------------------------------------------------------
-- Identity and composition

module _
  {κ ℓ α : Level} {C : Set κ} {D : C → Set ℓ}
  {Ψ : Operator D} {A : Set α}
  where

  map-id :
    (j : A → C) (c : Code Ψ A j) → map (λ a → a) j c ＝ c
  map-id j empty = refl
  map-id j unit = refl
  map-id j two = refl
  map-id j natural = refl
  map-id j (product a b) = refl
  map-id j (sum a b) = refl
  map-id j (tree a b) = refl
  map-id j (identity a x y) = refl
  map-id j (result a b) = refl
  map-id j (branch a b i) = refl

module _
  {κ ℓ α β γ : Level} {C : Set κ} {D : C → Set ℓ}
  {Ψ : Operator D} {A : Set α} {B : Set β} {E : Set γ}
  where

  map-compose :
    (h : A → B) (g : B → E) (k : E → C)
    (c : Code Ψ A (λ a → k (g (h a))))
    → map g k (map h (λ b → k (g b)) c)
      ＝ map (λ a → g (h a)) k c
  map-compose h g k empty = refl
  map-compose h g k unit = refl
  map-compose h g k two = refl
  map-compose h g k natural = refl
  map-compose h g k (product a b) = refl
  map-compose h g k (sum a b) = refl
  map-compose h g k (tree a b) = refl
  map-compose h g k (identity a x y) = refl
  map-compose h g k (result a b) = refl
  map-compose h g k (branch a b i) = refl
