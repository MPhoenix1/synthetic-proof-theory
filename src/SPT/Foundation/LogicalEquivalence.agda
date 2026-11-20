{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.LogicalEquivalence where

-- Two types are logically equivalent when each maps to the other:
--
--   A ⇔ B = (A → B) × (B → A).
--
-- Logical equivalence is reflexive, symmetric and transitive, and identified
-- types are logically equivalent (`⇔-of-＝`). It is a congruence for the type
-- formers: products, sums and function types (`×-iff`, `⊎-iff`, `→-iff`),
-- decidability (`decidable-iff`), dependent functions and dependent pairs over
-- one index (`Π-iff`, `Σ-iff`), dependent functions guarded by a family, along
-- an isomorphism of their index (`guard-iff`), and a propositional modality
-- (`○-iff`).

open import SPT.Base
open import SPT.Foundation.Isomorphisms using
  (_≅_; forward; backward; forward-backward)
open import SPT.Foundation.Modalities using (Modality; ○-map)

------------------------------------------------------------------------
-- Logical equivalence

infix 5 _⇔_

_⇔_ : {ℓ κ : Level} → Set ℓ → Set κ → Set (ℓ ⊔ κ)
A ⇔ B = (A → B) × (B → A)

module _ {ℓ : Level} {A : Set ℓ} where

  ⇔-refl : A ⇔ A
  ⇔-refl = id , id

module _ {ℓ κ : Level} {A : Set ℓ} {B : Set κ} where

  ⇔-sym : A ⇔ B → B ⇔ A
  ⇔-sym p = pr₂ p , pr₁ p

module _ {ℓ κ μ : Level} {A : Set ℓ} {B : Set κ} {C : Set μ} where

  ⇔-trans : A ⇔ B → B ⇔ C → A ⇔ C
  ⇔-trans p q = (λ a → pr₁ q (pr₁ p a)) , (λ c → pr₂ p (pr₂ q c))

module _ {ℓ : Level} {A B : Set ℓ} where

  ⇔-of-＝ : A ＝ B → A ⇔ B
  ⇔-of-＝ refl = id , id

------------------------------------------------------------------------
-- Products, sums and function types

module _ {ℓ κ ℓ′ κ′ : Level} {A : Set ℓ} {B : Set κ} {A′ : Set ℓ′}
  {B′ : Set κ′} where

  ×-iff : A ⇔ A′ → B ⇔ B′ → (A × B) ⇔ (A′ × B′)
  ×-iff p q =
    (λ c → pr₁ p (pr₁ c) , pr₁ q (pr₂ c)) ,
    (λ c → pr₂ p (pr₁ c) , pr₂ q (pr₂ c))

  ⊎-iff : A ⇔ A′ → B ⇔ B′ → (A ⊎ B) ⇔ (A′ ⊎ B′)
  ⊎-iff p q = ⊎-map (pr₁ p) (pr₁ q) , ⊎-map (pr₂ p) (pr₂ q)

  →-iff : A ⇔ A′ → B ⇔ B′ → (A → B) ⇔ (A′ → B′)
  →-iff p q =
    (λ f a′ → pr₁ q (f (pr₂ p a′))) , (λ g a → pr₂ q (g (pr₁ p a)))

module _ {ℓ κ : Level} {A : Set ℓ} {B : Set κ} where

  decidable-iff : A ⇔ B → is-decidable A ⇔ is-decidable B
  decidable-iff p =
    ⊎-map (pr₁ p) (λ n b → n (pr₂ p b)) , ⊎-map (pr₂ p) (λ n a → n (pr₁ p a))

------------------------------------------------------------------------
-- Dependent functions and dependent pairs over one index

module _ {ℓ κ μ : Level} {X : Set ℓ} {P : X → Set κ} {Q : X → Set μ} where

  Π-iff : ((x : X) → P x ⇔ Q x) → ((x : X) → P x) ⇔ ((x : X) → Q x)
  Π-iff e = (λ f x → pr₁ (e x) (f x)) , (λ g x → pr₂ (e x) (g x))

  Σ-iff : ((x : X) → P x ⇔ Q x) → Σ X P ⇔ Σ X Q
  Σ-iff e =
    (λ w → pr₁ w , pr₁ (e (pr₁ w)) (pr₂ w)) ,
    (λ w → pr₁ w , pr₂ (e (pr₁ w)) (pr₂ w))

-- A bijection of domains carries a guarded dependent function.
guard-iff : {ℓ h k : Level} {C C′ : Set ℓ} (H₁ : C → Set h) (K₁ : C → Set k)
  (H₂ : C′ → Set h) (K₂ : C′ → Set k) (E : C ≅ C′) →
  ((c : C) → H₁ c ⇔ H₂ (forward E c)) →
  ((c : C) → K₁ c ⇔ K₂ (forward E c)) →
  ((c : C) → H₁ c → K₁ c) ⇔ ((c′ : C′) → H₂ c′ → K₂ c′)
guard-iff H₁ K₁ H₂ K₂ E h k =
  ( λ p c′ d →
      transport K₂ (forward-backward E c′)
        ( pr₁ (k (backward E c′))
            ( p (backward E c′)
                ( pr₂ (h (backward E c′))
                    (transport H₂ (forward-backward E c′ ⁻¹) d))))) ,
  (λ q c d → pr₂ (k c) (q (forward E c) (pr₁ (h c) d)))

------------------------------------------------------------------------
-- Modalities

module _ {ℓ : Level} (M : Modality ℓ) where

  open Modality M using (○_)

  ○-iff : {A B : Set ℓ} → A ⇔ B → ○ A ⇔ ○ B
  ○-iff p = ○-map M (pr₁ p) , ○-map M (pr₂ p)
