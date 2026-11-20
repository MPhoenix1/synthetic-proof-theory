{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Retraction where

-- Decoding of the selected formers up to retraction. A retract of `X` on `Y`
-- is a map `out : X → Y` with a section `into` (`Retract`). Each decoded
-- former, the identity of two points included, is a retract of its standard
-- type (`Retracts`); for trees the section is inverse only up to similarity,
-- equal labels with similar children (`Similar`, `Unfolding`), which needs no
-- function extensionality. Retracts compose (`_∘ʳ_`, `_∘ᵘ_`), add (`_⊎ʳ_`)
-- and act fiberwise (`fiberwise`). Decoding laws give the retractions by
-- transport (`retracts-from-laws`), and the child of a closure inherits them
-- through its names (`inherited-retracts`). A binary sum is a sum code over
-- the two-point code (`plus`, written `a ⊎⟨ R ⟩ b`; `plus-retract`), and the
-- unit code is a retract of the unit type (`unit-retract`).
--
--   out (into y) ＝ y,   Similar (out (into w)) w.

open import SPT.Base
open import SPT.Mahlo.Specification using
  (Operator; Formers; Decode; map; Name; Closure)
open import SPT.Foundation.Tree.W using (W; sup)
open import SPT.Mahlo.Decoding using (DecodingLaws; child-formers)

------------------------------------------------------------------------
-- Retracts

record Retract {α β : Level} (X : Set α) (Y : Set β) : Set (α ⊔ β) where
  field
    out : X → Y
    into : Y → X
    out-into : (y : Y) → out (into y) ＝ y

open Retract public

------------------------------------------------------------------------
-- Similar trees and unfoldings

-- Equal labels, and similar children at corresponding positions.

module _ {α β : Level} {A : Set α} {B : A → Set β} where

  Similar : W A B → W A B → Set (α ⊔ β)
  Similar (sup x f) (sup y g) =
    Σ (x ＝ y) (λ e → (i : B x) → Similar (f i) (g (transport B e i)))

  similar-refl : (w : W A B) → Similar w w
  similar-refl (sup x f) = refl , (λ i → similar-refl (f i))

  similar-of-identification : {v w : W A B} → v ＝ w → Similar v w
  similar-of-identification {v} refl = similar-refl v

record Unfolding {α β γ : Level} (X : Set γ) (A : Set α) (B : A → Set β)
  : Set (α ⊔ β ⊔ γ) where
  field
    out : X → W A B
    into : W A B → X
    out-into : (w : W A B) → Similar (out (into w)) w

------------------------------------------------------------------------
-- Decoding of the selected formers, up to retraction

record Retracts {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Formers C D) : Set (κ ⊔ ℓ) where
  field
    empty : D (Formers.empty Q) → 𝟘
    point : D (Formers.unit Q)
    two : Retract (D (Formers.two Q)) 𝟚
    natural : Retract (D (Formers.natural Q)) ℕ
    sum : (a : C) (b : D a → C) →
      Retract (D (Formers.sum Q (a , b))) (Σ (D a) (λ x → D (b x)))
    product : (a : C) (b : D a → C) →
      Retract (D (Formers.product Q (a , b))) ((x : D a) → D (b x))
    tree : (a : C) (b : D a → C) →
      Unfolding (D (Formers.tree Q (a , b))) (D a) (λ x → D (b x))
    identity : (a : C) (x y : D a) →
      Retract (D (Formers.identity Q a x y)) (x ＝ y)

------------------------------------------------------------------------
-- Combinators

module _ {α : Level} {X Y : Set α} where

  retract-of-identification : X ＝ Y → Retract X Y
  retract-of-identification refl =
    record { out = id ; into = id ; out-into = λ y → refl }

module _ {α β : Level} {X : Set α} where

  lowering : Retract (Lift β X) X
  lowering = record { out = lower ; into = lift ; out-into = λ x → refl }

module _ {α β γ : Level} {X : Set α} {Y : Set β} {Z : Set γ} where

  infixr 15 _∘ʳ_

  _∘ʳ_ : Retract X Y → Retract Y Z → Retract X Z
  r ∘ʳ s = record
    { out = λ x → out s (out r x)
    ; into = λ z → into r (into s z)
    ; out-into = λ z → ap (out s) (out-into r (into s z)) ∙ out-into s z
    }

module _ {α β γ δ : Level} {X : Set γ} {Y : Set δ} {A : Set α}
  {B : A → Set β} where

  infixr 15 _∘ᵘ_

  _∘ᵘ_ : Retract X Y → Unfolding Y A B → Unfolding X A B
  r ∘ᵘ u = record
    { out = λ x → Unfolding.out u (out r x)
    ; into = λ w → into r (Unfolding.into u w)
    ; out-into = λ w →
        transport (λ v → Similar v w)
          (ap (Unfolding.out u) (out-into r (Unfolding.into u w)) ⁻¹)
          (Unfolding.out-into u w)
    }

module _ {α β γ δ : Level} {X : Set α} {X′ : Set β} {Y : Set γ}
  {Y′ : Set δ} where

  sum-out : Retract X X′ → Retract Y Y′ → X ⊎ Y → X′ ⊎ Y′
  sum-out r s (inl x) = inl (out r x)
  sum-out r s (inr y) = inr (out s y)

  sum-into : Retract X X′ → Retract Y Y′ → X′ ⊎ Y′ → X ⊎ Y
  sum-into r s (inl x) = inl (into r x)
  sum-into r s (inr y) = inr (into s y)

  sum-out-into : (r : Retract X X′) (s : Retract Y Y′) (z : X′ ⊎ Y′) →
    sum-out r s (sum-into r s z) ＝ z
  sum-out-into r s (inl x) = ap inl (out-into r x)
  sum-out-into r s (inr y) = ap inr (out-into s y)

  infixr 10 _⊎ʳ_

  _⊎ʳ_ : Retract X X′ → Retract Y Y′ → Retract (X ⊎ Y) (X′ ⊎ Y′)
  r ⊎ʳ s = record
    { out = sum-out r s ; into = sum-into r s ; out-into = sum-out-into r s }

module _ {α β γ : Level} {A : Set α} {X : A → Set β} {Y : A → Set γ} where

  fiberwise : ((a : A) → Retract (X a) (Y a)) → Retract (Σ A X) (Σ A Y)
  fiberwise r = record
    { out = λ p → pr₁ p , out (r (pr₁ p)) (pr₂ p)
    ; into = λ p → pr₁ p , into (r (pr₁ p)) (pr₂ p)
    ; out-into = λ p →
        ap (λ y → pr₁ p , y) (out-into (r (pr₁ p)) (pr₂ p))
    }

------------------------------------------------------------------------
-- Decoding laws give retractions

module _ {α β : Level} {X : Set (α ⊔ β)} {A : Set α} {B : A → Set β} where

  unfolding-of-identification : X ＝ W A B → Unfolding X A B
  unfolding-of-identification e = record
    { out = out (retract-of-identification e)
    ; into = into (retract-of-identification e)
    ; out-into = λ w →
        similar-of-identification
          (out-into (retract-of-identification e) w)
    }

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D} where

  retracts-from-laws : DecodingLaws Q → Retracts Q
  retracts-from-laws laws = record
    { empty = λ i →
        lower (out (retract-of-identification (DecodingLaws.empty-β laws)) i)
    ; point =
        into (retract-of-identification (DecodingLaws.unit-β laws)) (lift ⋆)
    ; two = retract-of-identification (DecodingLaws.two-β laws) ∘ʳ lowering
    ; natural =
        retract-of-identification (DecodingLaws.natural-β laws) ∘ʳ lowering
    ; sum = λ a b →
        retract-of-identification (DecodingLaws.sum-β laws a b)
    ; product = λ a b →
        retract-of-identification (DecodingLaws.product-β laws a b)
    ; tree = λ a b →
        unfolding-of-identification (DecodingLaws.tree-β laws a b)
    ; identity = λ a x y →
        retract-of-identification (DecodingLaws.identity-β laws a x y)
    }

------------------------------------------------------------------------
-- The child of a closure inherits the retractions

-- Through the identification each name carries.

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D}
  {Ψ : Operator D} {A : Set ℓ} where

  name-retract : (L : Closure Q Ψ A) (c : C)
    (n : Name (Closure.interpret L) c) →
    Retract (D (Closure.interpret L (pr₁ n))) (D c)
  name-retract L c n = retract-of-identification (ap D (pr₂ n))

  inherited-retracts : Retracts Q → (L : Closure Q Ψ A) →
    Retracts (child-formers L)
  inherited-retracts R L = record
    { empty = λ i →
        Retracts.empty R
          (out (name-retract L (Formers.empty Q) (Closure.empty L)) i)
    ; point =
        into (name-retract L (Formers.unit Q) (Closure.unit L))
          (Retracts.point R)
    ; two =
        name-retract L (Formers.two Q) (Closure.two L) ∘ʳ Retracts.two R
    ; natural =
        name-retract L (Formers.natural Q) (Closure.natural L)
          ∘ʳ Retracts.natural R
    ; sum = λ a b →
        name-retract L
          (Formers.sum Q (map D (Closure.interpret L) (a , b)))
          (Closure.sum L (a , b))
        ∘ʳ Retracts.sum R (Closure.interpret L a)
             (λ x → Closure.interpret L (b x))
    ; product = λ a b →
        name-retract L
          (Formers.product Q (map D (Closure.interpret L) (a , b)))
          (Closure.product L (a , b))
        ∘ʳ Retracts.product R (Closure.interpret L a)
             (λ x → Closure.interpret L (b x))
    ; tree = λ a b →
        name-retract L
          (Formers.tree Q (map D (Closure.interpret L) (a , b)))
          (Closure.tree L (a , b))
        ∘ᵘ Retracts.tree R (Closure.interpret L a)
             (λ x → Closure.interpret L (b x))
    ; identity = λ a x y →
        name-retract L
          (Formers.identity Q (Closure.interpret L a) x y)
          (Closure.identity L a x y)
        ∘ʳ Retracts.identity R (Closure.interpret L a) x y
    }

------------------------------------------------------------------------
-- Binary sums and the unit

module _ {κ : Level} {C : Set κ} where

  choose : 𝟚 → C → C → C
  choose ₀ a b = a
  choose ₁ a b = b

-- A point of the chosen decoding, read in the binary sum.

module _ {κ ℓ : Level} {C : Set κ} (D : C → Set ℓ) (a b : C) where

  read : (k : 𝟚) → D (choose k a b) → D a ⊎ D b
  read ₀ u = inl u
  read ₁ v = inr v

  read-left : (k : 𝟚) (e : k ＝ ₀) (u : D a) →
    read k (transport (λ j → D (choose j a b)) (e ⁻¹) u) ＝ inl u
  read-left k refl u = refl

  read-right : (k : 𝟚) (e : k ＝ ₁) (v : D b) →
    read k (transport (λ j → D (choose j a b)) (e ⁻¹) v) ＝ inr v
  read-right k refl v = refl

-- Mathematical shape: a ⊎⟨ R ⟩ b = Σ (k : two). choose k a b, a retract of
-- D a ⊎ D b.

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D} where

  plus : Retracts Q → C → C → C
  plus R a b =
    Formers.sum Q
      (Formers.two Q , (λ k → choose (out (Retracts.two R) k) a b))

  infixr 10 plus
  syntax plus R a b = a ⊎⟨ R ⟩ b

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D}
  (R : Retracts Q) where

  plus-out : (a b : C) →
    Σ (D (Formers.two Q)) (λ k → D (choose (out (Retracts.two R) k) a b)) →
    D a ⊎ D b
  plus-out a b p = read D a b (out (Retracts.two R) (pr₁ p)) (pr₂ p)

  plus-into : (a b : C) → D a ⊎ D b →
    Σ (D (Formers.two Q)) (λ k → D (choose (out (Retracts.two R) k) a b))
  plus-into a b (inl u) =
    into (Retracts.two R) ₀ ,
    transport (λ j → D (choose j a b)) (out-into (Retracts.two R) ₀ ⁻¹) u
  plus-into a b (inr v) =
    into (Retracts.two R) ₁ ,
    transport (λ j → D (choose j a b)) (out-into (Retracts.two R) ₁ ⁻¹) v

  plus-out-into : (a b : C) (z : D a ⊎ D b) →
    plus-out a b (plus-into a b z) ＝ z
  plus-out-into a b (inl u) =
    read-left D a b (out (Retracts.two R) (into (Retracts.two R) ₀))
      (out-into (Retracts.two R) ₀) u
  plus-out-into a b (inr v) =
    read-right D a b (out (Retracts.two R) (into (Retracts.two R) ₁))
      (out-into (Retracts.two R) ₁) v

  plus-retract : (a b : C) → Retract (D (a ⊎⟨ R ⟩ b)) (D a ⊎ D b)
  plus-retract a b =
    Retracts.sum R (Formers.two Q)
      (λ k → choose (out (Retracts.two R) k) a b)
    ∘ʳ record
      { out = plus-out a b
      ; into = plus-into a b
      ; out-into = plus-out-into a b
      }

  unit-retract : Retract (D (Formers.unit Q)) (Lift ℓ 𝟙)
  unit-retract = record
    { out = λ u → lift ⋆
    ; into = λ u → Retracts.point R
    ; out-into = λ u → refl
    }
