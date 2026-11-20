{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Residence.Constructors.Discriminator where

-- A constant operator's result and members are retained literally, even
-- when those outputs are variables. Child maps may identify distinct
-- constructor arguments. Changing the parent is different: preserving its
-- decoded types alone need not commute with the chosen operator.

open import SPT.Base
open import SPT.Foundation.Two.Connectives using (not)
open import SPT.Mahlo.Specification using (Family; Operator; Formers)
open import SPT.Mahlo.Residence.Constructors using
  (Code; interpret; map; interpret-map)
import SPT.Mahlo.Residence.Constructors as Constructors
open import SPT.Mahlo.Residence.Families using (image)

------------------------------------------------------------------------
-- The actual output of a constant operator

constant :
  {κ ℓ : Level} {C : Set κ} (D : C → Set ℓ) → Family D → Operator D
constant D G F = G

module _
  {κ ℓ α : Level} {C : Set κ} {A : Set α}
  (D : C → Set ℓ) (j : A → C)
  where

  result :
    (G : Family D) → Family (λ a → D (j a)) → Code (constant D G) A j
  result G (a , b) = Constructors.result a b

  branch :
    (c : C) (b : D c → C) → Family (λ a → D (j a))
    → D c → Code (constant D (c , b)) A j
  branch c b (a , f) y = Constructors.branch a f y

  result-β :
    (Q : Formers C D) (c : C) (b : D c → C)
    (F : Family (λ a → D (j a)))
    → interpret Q (result (c , b) F) ＝ c
  result-β Q c b (a , f) = refl

  branch-β :
    (Q : Formers C D) (c : C) (b : D c → C)
    (F : Family (λ a → D (j a))) (y : D c)
    → interpret Q (branch c b F y) ＝ b y
  branch-β Q c b (a , f) y = refl

------------------------------------------------------------------------
-- A child map may identify distinct family arguments

D : 𝟚 → Set
D a = 𝟙

operator : Operator D
operator F = ₀ , (λ x → ₀)

collapse : 𝟚 → 𝟙
collapse a = ⋆

j : 𝟙 → 𝟚
j x = ₀

seed : (a : 𝟚) → Code operator 𝟚 (λ a → j (collapse a))
seed a = Constructors.result a (λ x → a)

distinct : seed ₀ ＝ seed ₁ → 𝟘
distinct ()

coalesced : map collapse j (seed ₀) ＝ map collapse j (seed ₁)
coalesced = refl

preserved :
  (Q : Formers 𝟚 D) (a : 𝟚)
  → interpret Q (map collapse j (seed a)) ＝ interpret Q (seed a)
preserved Q a = interpret-map Q collapse j (seed a)

------------------------------------------------------------------------
-- Preservation of decoded types does not give a parent comparison

decoding-preserved : (a : 𝟚) → D (not a) ＝ D a
decoding-preserved a = refl

not-commutes :
  (F : Family D)
  → image D not (operator F) ＝ operator (image D not F) → 𝟘
not-commutes F ()
