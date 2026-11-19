{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Sets.Uniqueness where

-- Unique identifications from one point (`Unique`). A pointed family of
-- propositions mapping into identifications proves their uniqueness
-- (`identifications-from`). Uniqueness passes through retractions,
-- transport and dependent pairs (`retract-unique`, `transported-unique`,
-- `pair-unique`). Under function extensionality at every level, packaged
-- in `Extensionality`, it passes to functions (`function-unique`), and
-- dependent products of sets are sets (`Π-is-set`). `UIP` states that
-- every type at every level is a set; it is not assumed here.

open import SPT.Base
open import SPT.Foundation.Propositions using
  (is-proposition; is-set; Σ-is-proposition)
open import SPT.Foundation.Extensionality using (FunExt; Π-is-proposition)

------------------------------------------------------------------------
-- Identifications from a point

module _ {ℓ : Level} {X : Set ℓ} where

  left-composition-cancels : {x y z : X} (r : x ＝ y) {p q : y ＝ z} →
    r ∙ p ＝ r ∙ q → p ＝ q
  left-composition-cancels refl e = e

module _ {ℓ κ : Level} {X : Set ℓ} {x : X} (R : X → Set κ) (ρ : R x)
  (to : (y : X) → R y → x ＝ y) where

  read : {y : X} (p : x ＝ y) → to y (transport R p ρ) ＝ to x ρ ∙ p
  read refl = refl-right-neutral (to x ρ) ⁻¹

  identifications-from : ((y : X) → is-proposition (R y)) →
    (y : X) → is-proposition (x ＝ y)
  identifications-from props y p q = left-composition-cancels (to x ρ)
    (read p ⁻¹
      ∙ (ap (to y) (props y (transport R p ρ) (transport R q ρ))
        ∙ read q))

module _ {ℓ : Level} {X : Set ℓ} where

  Unique : X → Set ℓ
  Unique x = (y : X) → is-proposition (x ＝ y)

------------------------------------------------------------------------
-- Retractions, transport and pairs

module _ {ℓ κ : Level} {X : Set ℓ} {Y : Set κ} where

  retract-unique : (f : X → Y) (g : Y → X) →
    ((x : X) → g (f x) ＝ x) → (x : X) → Unique (f x) → Unique x
  retract-unique f g gf x unique = identifications-from
    (λ y → f x ＝ f y) refl
    (λ y e → gf x ⁻¹ ∙ (ap g e ∙ gf y))
    (λ y → unique (f y))

module _ {ℓ κ : Level} {A : Set ℓ} (B : A → Set κ) where

  transported-unique : {a a′ : A} (e : a ＝ a′) {b : B a} → Unique b →
    Unique (transport B e b)
  transported-unique refl unique = unique

module _ {ℓ κ : Level} {A : Set ℓ} {B : A → Set κ} where

  pair-unique : {a : A} {b : B a} → Unique a → Unique b → Unique (a , b)
  pair-unique {a} {b} uniqueA uniqueB = identifications-from
    (λ y → Σ (a ＝ pr₁ y) (λ e → transport B e b ＝ pr₂ y)) (refl , refl)
    (λ y s → to-Σ-＝ (pr₁ s) (pr₂ s))
    (λ y → Σ-is-proposition (uniqueA (pr₁ y))
      (λ e → transported-unique B e uniqueB (pr₂ y)))

------------------------------------------------------------------------
-- Extensionality and uniqueness at every level

-- The record keeps the hypothesis literal when it occurs in types.
record Extensionality : Setω where
  field
    extensional : {ℓ κ : Level} {A : Set ℓ} {B : A → Set κ} → FunExt A B

open Extensionality public

UIP : Setω
UIP = {ℓ : Level} {X : Set ℓ} → is-set X

module _ (ext : Extensionality) where

  pointwise : {ℓ κ : Level} {A : Set ℓ} {B : A → Set κ}
    {f g : (a : A) → B a} → ((a : A) → f a ＝ g a) → f ＝ g
  pointwise {f = f} {g = g} h = extensional ext f g h

  function-unique : {ℓ κ : Level} {A : Set ℓ} {B : A → Set κ}
    {f : (a : A) → B a} → ((a : A) → Unique (f a)) → Unique f
  function-unique {A = A} {f = f} unique = identifications-from
    (λ g → (a : A) → f a ＝ g a) (λ a → refl)
    (λ g h → extensional ext f g h)
    (λ g → Π-is-proposition (extensional ext) (λ a → unique a (g a)))

  Π-is-set : {ℓ κ : Level} {A : Set ℓ} {B : A → Set κ} →
    ((a : A) → is-set (B a)) → is-set ((a : A) → B a)
  Π-is-set sets f = function-unique (λ a → sets a (f a))
