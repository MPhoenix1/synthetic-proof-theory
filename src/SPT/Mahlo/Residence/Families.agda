{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Residence.Families where

-- A family interpreted in a parent is its pullback along the
-- interpretation. `pullback` identifies its total with the identity-witness
-- pullback; `image` maps complete families, with identity and composition
-- laws. `Map` retains a triangle identity, while literal composite sources
-- need no transport. `Resident` retains a parent name for the returned
-- carrier; `compose` composes resident families without independently
-- naming a type.

open import SPT.Base
open import SPT.Foundation.Isomorphisms using (_≅_)
open import SPT.Mahlo.Specification using (Family; Operator)

------------------------------------------------------------------------
-- The pullback of the parent's display map

module _ {κ ℓ α : Level} {C : Set κ} {A : Set α} where

  total : (D : C → Set ℓ) (j : A → C)
    → Σ A (λ a → D (j a)) → Σ C D
  total D j (a , x) = j a , x

  square : (D : C → Set ℓ) (j : A → C)
    (z : Σ A (λ a → D (j a)))
    → pr₁ (total D j z) ＝ j (pr₁ z)
  square D j (a , x) = refl

  -- The comparison retains the commuting identity, not only its endpoints.
  Pullback : (D : C → Set ℓ) → (A → C) → Set (κ ⊔ ℓ ⊔ α)
  Pullback D j =
    Σ A (λ a → Σ (Σ C D) (λ z → j a ＝ pr₁ z))

  cone : (D : C → Set ℓ) (j : A → C)
    → Σ A (λ a → D (j a)) → Pullback D j
  cone D j (a , x) = a , (j a , x) , refl

  resolve : (D : C → Set ℓ) (j : A → C)
    → Pullback D j → Σ A (λ a → D (j a))
  resolve D j (a , (c , x) , p) = a , transport D (p ⁻¹) x

  resolve-cone : (D : C → Set ℓ) (j : A → C)
    (z : Σ A (λ a → D (j a))) → resolve D j (cone D j z) ＝ z
  resolve-cone D j (a , x) = refl

  cone-resolve : (D : C → Set ℓ) (j : A → C)
    (z : Pullback D j) → cone D j (resolve D j z) ＝ z
  cone-resolve D j (a , (c , x) , refl) = refl

  pullback : (D : C → Set ℓ) (j : A → C)
    → Σ A (λ a → D (j a)) ≅ Pullback D j
  pullback D j = record
    { forward = cone D j
    ; backward = resolve D j
    ; backward-forward = resolve-cone D j
    ; forward-backward = cone-resolve D j
    }

------------------------------------------------------------------------
-- Complete families and literal reindexing

module _ {κ ℓ α : Level} {C : Set κ} {A : Set α} where

  image : (D : C → Set ℓ) (j : A → C)
    → Family (λ a → D (j a)) → Family D
  image D j (a , b) = j a , (λ x → j (b x))

module _ {κ ℓ : Level} {C : Set κ} where

  total-id : (D : C → Set ℓ) (z : Σ C D)
    → total D (λ c → c) z ＝ z
  total-id D (c , x) = refl

  image-id : (D : C → Set ℓ) (F : Family D)
    → image D (λ c → c) F ＝ F
  image-id D (a , b) = refl

module _
  {κ ℓ α β : Level} {C : Set κ} {A : Set α} {B : Set β}
  where

  total-compose : (D : C → Set ℓ) (j : B → C) (h : A → B)
    (z : Σ A (λ a → D (j (h a))))
    → total D j (total (λ b → D (j b)) h z)
      ＝ total D (λ a → j (h a)) z
  total-compose D j h (a , x) = refl

  image-compose : (D : C → Set ℓ) (j : B → C) (h : A → B)
    (F : Family (λ a → D (j (h a))))
    → image D j (image (λ b → D (j b)) h F)
      ＝ image D (λ a → j (h a)) F
  image-compose D j h (a , b) = refl

  -- An arbitrary operator receives the same complete parent input.
  operator-input : (D : C → Set ℓ) (Ψ : Operator D)
    (j : B → C) (h : A → B) (F : Family (λ a → D (j (h a))))
    → Ψ (image D j (image (λ b → D (j b)) h F))
      ＝ Ψ (image D (λ a → j (h a)) F)
  operator-input D Ψ j h (a , b) = refl

------------------------------------------------------------------------
-- General comparisons retain their triangle identities

record Map
  {κ α β : Level} {C : Set κ} {A : Set α} {B : Set β}
  (j : A → C) (k : B → C) : Set (κ ⊔ α ⊔ β) where
  field
    arrow : A → B
    triangle : (a : A) → k (arrow a) ＝ j a

module _ {κ ℓ : Level} {C : Set κ} where

  move-total : (D : C → Set ℓ) {c d : C}
    (p : c ＝ d) (x : D d)
    → _＝_ {A = Σ C D} (c , transport D (p ⁻¹) x) (d , x)
  move-total D refl x = refl

module _ {κ α : Level} {C : Set κ} {A : Set α} where

  identity : (j : A → C) → Map j j
  identity j = record { arrow = λ a → a ; triangle = λ a → refl }

module _
  {κ α β γ : Level} {C : Set κ}
  {A : Set α} {B : Set β} {E : Set γ}
  {j : A → C} {k : B → C} {m : E → C}
  where

  compose-map : Map j k → Map k m → Map j m
  compose-map f g = record
    { arrow = λ a → Map.arrow g (Map.arrow f a)
    ; triangle = λ a →
        Map.triangle g (Map.arrow f a) ∙ Map.triangle f a
    }

module _
  {κ ℓ α β : Level} {C : Set κ} {A : Set α} {B : Set β}
  {j : A → C} {k : B → C}
  where

  map-total : (D : C → Set ℓ) (f : Map j k)
    → Σ A (λ a → D (j a)) → Σ B (λ b → D (k b))
  map-total D f (a , x) =
    Map.arrow f a , transport D (Map.triangle f a ⁻¹) x

  total-triangle : (D : C → Set ℓ) (f : Map j k)
    (z : Σ A (λ a → D (j a)))
    → total D k (map-total D f z) ＝ total D j z
  total-triangle D f (a , x) = move-total D (Map.triangle f a) x

------------------------------------------------------------------------
-- The returned carrier is represented in the same parent

record Resident {κ ℓ : Level} {C : Set κ} (D : C → Set ℓ)
  : Set (κ ⊔ ℓ) where
  field
    name : C
    interpret : D name → C

module _ {κ ℓ : Level} {C : Set κ} where

  compose : (D : C → Set ℓ) (r : Resident D)
    → Resident (λ a → D (Resident.interpret r a)) → Resident D
  compose D r s = record
    { name = Resident.interpret r (Resident.name s)
    ; interpret = λ a → Resident.interpret r (Resident.interpret s a)
    }
