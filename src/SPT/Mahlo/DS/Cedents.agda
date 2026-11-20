{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Cedents where

-- Cedents of a family's names and the names derivable from them by the
-- formers and an operator. A cedent of (C , D) is a predicate on names
-- (`Ced`), with membership, inclusion, union, extension by a name and the
-- names of an interpretation (`_∈_`, `_⊆_`, `_∪_`, `_▻_`, `image-map`).
-- A cedent is closed under the formers Q and an operator Φ when it
-- contains the constant formers' names and, at a family of its names, the
-- family formers' names and Φ's index and members (`Closed`). The names
-- derivable from a cedent Γ form an ordinary inductive family over the
-- names, with no induction–recursion (`Derivable`): the least closed
-- cedent containing Γ (`derivable-closed`, `least`). So derivability is a
-- closure operator on cedents (`seeded`, `monotone`, `idempotent`). The
-- names of any closure of the operator form a closed cedent, under
-- extensionality for families of names (`named-closed`), so every closure
-- names every name derivable from nothing (`derivable-named`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
import SPT.Mahlo.Specification as Specification

open import SPT.Mahlo.DS.Realization.Family using (cast)
open import SPT.Mahlo.DS.Naming.Trees using (pair)

------------------------------------------------------------------------
-- Cedents

Ced : {κ : Level} (ν : Level) → Set κ → Set (κ ⊔ lsuc ν)
Ced ν C = C → Set ν

infix 4 _∈_ _⊆_
infixl 5 _▻_
infixr 4 _∪_

_∈_ : {κ ν : Level} {C : Set κ} → C → Ced ν C → Set ν
c ∈ Γ = Γ c

_⊆_ :
  {κ ν μ : Level} {C : Set κ} → Ced ν C → Ced μ C → Set (κ ⊔ ν ⊔ μ)
_⊆_ {κ} {ν} {μ} {C} Γ Δ = {c : C} → Γ c → Δ c

∅ᶜ : {κ : Level} {C : Set κ} → Ced lzero C
∅ᶜ c = 𝟘

_∪_ :
  {κ ν μ : Level} {C : Set κ} → Ced ν C → Ced μ C → Ced (ν ⊔ μ) C
(Γ ∪ Δ) c = Γ c ⊎ Δ c

-- Identity in C lives at κ; extension therefore uses evidence at κ ⊔ ν.
_▻_ : {κ ν : Level} {C : Set κ} → Ced (κ ⊔ ν) C → C → Ced (κ ⊔ ν) C
(Γ ▻ a) c = Γ c ⊎ (c ＝ a)

⊆-refl : {κ ν : Level} {C : Set κ} {Γ : Ced ν C} → Γ ⊆ Γ
⊆-refl p = p

⊆-trans :
  {κ ν μ ξ : Level} {C : Set κ}
  {Γ : Ced ν C} {Δ : Ced μ C} {Θ : Ced ξ C}
  → Γ ⊆ Δ → Δ ⊆ Θ → Γ ⊆ Θ
⊆-trans f g p = g (f p)

∪ˡ : {κ ν μ : Level} {C : Set κ} {Γ : Ced ν C} {Δ : Ced μ C} → Γ ⊆ (Γ ∪ Δ)
∪ˡ = inl

∪ʳ : {κ ν μ : Level} {C : Set κ} {Γ : Ced ν C} {Δ : Ced μ C} → Δ ⊆ (Γ ∪ Δ)
∪ʳ = inr

-- The names an interpretation reaches form the cedent
-- Specification.Name f; a map of interpretations includes them.
image-map :
  {α β κ : Level} {A : Set α} {B : Set β} {C : Set κ}
  {f : A → C} {g : B → C} (h : A → B) → ((a : A) → g (h a) ＝ f a)
  → Specification.Name f ⊆ Specification.Name g
image-map h law n = h (pr₁ n) , (law (pr₁ n) ∙ pr₂ n)

------------------------------------------------------------------------
-- Closed cedents and derivable names

record Closed
  {κ ℓ ν : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Specification.Formers C D) (Φ : Specification.Operator D)
  (Δ : Ced ν C) : Set (κ ⊔ ℓ ⊔ ν) where
  field
    on-empty : Δ (Specification.Formers.empty Q)
    on-unit : Δ (Specification.Formers.unit Q)
    on-two : Δ (Specification.Formers.two Q)
    on-natural : Δ (Specification.Formers.natural Q)
    on-product :
      (a : C) (b : D a → C) → Δ a → ((x : D a) → Δ (b x))
      → Δ (Specification.Formers.product Q (a , b))
    on-sum :
      (a : C) (b : D a → C) → Δ a → ((x : D a) → Δ (b x))
      → Δ (Specification.Formers.sum Q (a , b))
    on-tree :
      (a : C) (b : D a → C) → Δ a → ((x : D a) → Δ (b x))
      → Δ (Specification.Formers.tree Q (a , b))
    on-identity :
      (a : C) (x y : D a) → Δ a
      → Δ (Specification.Formers.identity Q a x y)
    on-result :
      (a : C) (b : D a → C) → Δ a → ((x : D a) → Δ (b x))
      → Δ (pr₁ (Φ (a , b)))
    on-branch :
      (a : C) (b : D a → C) → Δ a → ((x : D a) → Δ (b x))
      → (y : D (pr₁ (Φ (a , b)))) → Δ (pr₂ (Φ (a , b)) y)

-- The names derivable from Γ: Γ's names, the constant formers, and the
-- family formers and Φ's outputs at families of derivable names.
data Derivable
  {κ ℓ ν : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Specification.Formers C D) (Φ : Specification.Operator D)
  (Γ : Ced ν C) : C → Set (κ ⊔ ℓ ⊔ ν) where
  seed : {c : C} → Γ c → Derivable Q Φ Γ c
  empty : Derivable Q Φ Γ (Specification.Formers.empty Q)
  unit : Derivable Q Φ Γ (Specification.Formers.unit Q)
  two : Derivable Q Φ Γ (Specification.Formers.two Q)
  natural : Derivable Q Φ Γ (Specification.Formers.natural Q)
  product :
    (a : C) (b : D a → C) → Derivable Q Φ Γ a
    → ((x : D a) → Derivable Q Φ Γ (b x))
    → Derivable Q Φ Γ (Specification.Formers.product Q (a , b))
  sum :
    (a : C) (b : D a → C) → Derivable Q Φ Γ a
    → ((x : D a) → Derivable Q Φ Γ (b x))
    → Derivable Q Φ Γ (Specification.Formers.sum Q (a , b))
  tree :
    (a : C) (b : D a → C) → Derivable Q Φ Γ a
    → ((x : D a) → Derivable Q Φ Γ (b x))
    → Derivable Q Φ Γ (Specification.Formers.tree Q (a , b))
  identity :
    (a : C) (x y : D a) → Derivable Q Φ Γ a
    → Derivable Q Φ Γ (Specification.Formers.identity Q a x y)
  result :
    (a : C) (b : D a → C) → Derivable Q Φ Γ a
    → ((x : D a) → Derivable Q Φ Γ (b x))
    → Derivable Q Φ Γ (pr₁ (Φ (a , b)))
  branch :
    (a : C) (b : D a → C) → Derivable Q Φ Γ a
    → ((x : D a) → Derivable Q Φ Γ (b x))
    → (y : D (pr₁ (Φ (a , b)))) → Derivable Q Φ Γ (pr₂ (Φ (a , b)) y)

module _
  {κ ℓ ν : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Specification.Formers C D) (Φ : Specification.Operator D)
  (Γ : Ced ν C)
  where

  derivable-closed : Closed Q Φ (Derivable Q Φ Γ)
  derivable-closed = record
    { on-empty = empty
    ; on-unit = unit
    ; on-two = two
    ; on-natural = natural
    ; on-product = product
    ; on-sum = sum
    ; on-tree = tree
    ; on-identity = identity
    ; on-result = result
    ; on-branch = branch
    }

  seeded : Γ ⊆ Derivable Q Φ Γ
  seeded p = seed p

-- Every closed cedent containing Γ contains its derivable names.
module _
  {κ ℓ ν μ : Level} {C : Set κ} {D : C → Set ℓ}
  {Q : Specification.Formers C D} {Φ : Specification.Operator D}
  {Γ : Ced ν C} {Δ : Ced μ C} (into : Γ ⊆ Δ) (rules : Closed Q Φ Δ)
  where

  least : Derivable Q Φ Γ ⊆ Δ
  least (seed p) = into p
  least empty = Closed.on-empty rules
  least unit = Closed.on-unit rules
  least two = Closed.on-two rules
  least natural = Closed.on-natural rules
  least (product a b d e) =
    Closed.on-product rules a b (least d) (λ x → least (e x))
  least (sum a b d e) =
    Closed.on-sum rules a b (least d) (λ x → least (e x))
  least (tree a b d e) =
    Closed.on-tree rules a b (least d) (λ x → least (e x))
  least (identity a x y d) = Closed.on-identity rules a x y (least d)
  least (result a b d e) =
    Closed.on-result rules a b (least d) (λ x → least (e x))
  least (branch a b d e y) =
    Closed.on-branch rules a b (least d) (λ x → least (e x)) y

-- Derivability is monotone and idempotent.
module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Specification.Formers C D) (Φ : Specification.Operator D)
  where

  monotone :
    {ν μ : Level} {Γ : Ced ν C} {Γ' : Ced μ C} → Γ ⊆ Γ'
    → Derivable Q Φ Γ ⊆ Derivable Q Φ Γ'
  monotone {ν} {μ} {Γ} {Γ'} f =
    least (λ p → seed (f p)) (derivable-closed Q Φ Γ')

  idempotent :
    {ν : Level} {Γ : Ced ν C}
    → Derivable Q Φ (Derivable Q Φ Γ) ⊆ Derivable Q Φ Γ
  idempotent {ν} {Γ} = least (λ p → p) (derivable-closed Q Φ Γ)

------------------------------------------------------------------------
-- The names of a closure

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  {Q : Specification.Formers C D} {Φ : Specification.Operator D}
  (extensionality : (X : Set ℓ) → FunExt X (λ _ → C))
  {A : Set ℓ} (M : Specification.Closure Q Φ A)
  where

  open Specification.Closure M using (interpret)

  -- A family of named names, as a family of M's codes.
  coded :
    (a : C) (b : D a → C) → Specification.Name interpret a
    → ((x : D a) → Specification.Name interpret (b x))
    → Specification.Family (Specification.Decode D interpret)
  coded a b n m = pr₁ n , (λ x → pr₁ (m (cast (ap D (pr₂ n)) x)))

  coded-β :
    (a : C) (b : D a → C) (n : Specification.Name interpret a)
    (m : (x : D a) → Specification.Name interpret (b x))
    → Specification.map D interpret (coded a b n m) ＝ (a , b)
  coded-β a b n m =
    pair D extensionality (pr₂ n) (λ x → pr₂ (m (cast (ap D (pr₂ n)) x)))

  -- Each member of a family identified with M's image of a family of
  -- codes is named.
  member-name :
    (G : Specification.Family (Specification.Decode D interpret))
    {H : Specification.Family D}
    → Specification.map D interpret G ＝ H
    → (z : D (pr₁ H)) → Specification.Name interpret (pr₂ H z)
  member-name G refl z = pr₂ G z , refl

  identity-name :
    (a : C) → Specification.Name interpret a → (x y : D a)
    → Specification.Name interpret (Specification.Formers.identity Q a x y)
  identity-name a (k , refl) x y = Specification.Closure.identity M k x y

  named-closed : Closed Q Φ (Specification.Name interpret)
  named-closed = record
    { on-empty = Specification.Closure.empty M
    ; on-unit = Specification.Closure.unit M
    ; on-two = Specification.Closure.two M
    ; on-natural = Specification.Closure.natural M
    ; on-product = λ a b n m →
        transport (Specification.Name interpret)
          (ap (Specification.Formers.product Q) (coded-β a b n m))
          (Specification.Closure.product M (coded a b n m))
    ; on-sum = λ a b n m →
        transport (Specification.Name interpret)
          (ap (Specification.Formers.sum Q) (coded-β a b n m))
          (Specification.Closure.sum M (coded a b n m))
    ; on-tree = λ a b n m →
        transport (Specification.Name interpret)
          (ap (Specification.Formers.tree Q) (coded-β a b n m))
          (Specification.Closure.tree M (coded a b n m))
    ; on-identity = λ a x y n → identity-name a n x y
    ; on-result = λ a b n m →
        pr₁ (Specification.Closure.inner M (coded a b n m)) ,
        ap pr₁
          ( Specification.Closure.inner-β M (coded a b n m)
          ∙ ap Φ (coded-β a b n m))
    ; on-branch = λ a b n m y →
        member-name (Specification.Closure.inner M (coded a b n m))
          ( Specification.Closure.inner-β M (coded a b n m)
          ∙ ap Φ (coded-β a b n m))
          y
    }

  derivable-named : Derivable Q Φ ∅ᶜ ⊆ Specification.Name interpret
  derivable-named = least (λ p → 𝟘-elim p) named-closed
