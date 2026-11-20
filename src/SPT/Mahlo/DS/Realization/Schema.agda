{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Realization.Schema where

-- Decoding by conversion at every argument of a fixed spine whose data are
-- all variables. A schema (`Schema`) gives a constructor type I, a first
-- recursive arity A i, a parameter type B i q read from the decodings q of
-- the first group, a second arity C i q b, and an output R i q b r:
--
--   σ I (λ i. δ (A i) (λ q. σ (B i q) (λ b. δ (C i q b)
--     (λ r. ι (R i q b r)))))
--
-- (`description`). Every branch of σ I has the same spine, so the
-- constructor tag may be a variable. With the reflector of
-- Realization.Discriminator, whose names hold by refl, the type that the
-- smallness principle builds satisfies its decoding equation by refl at
-- every argument (`small`, `output-β`); induction computes by refl at every
-- description already (IR.Smallness.ind-β). Empty recursive arities give a
-- point decoding to any given type (`none`, `seed`, `point`, `point-β`).

open import SPT.Base

open import SPT.IR.Description using
  (Desc; ι; σ; δ; indexed; Shape; Mark)
import SPT.Mahlo.DS.Ambient as Reflection
open import SPT.IR.Smallness using (Smallness; G; t; make)
open import SPT.Mahlo.DS.Realization.Discriminator using (reflector)

------------------------------------------------------------------------
-- Schemas

-- I selects the constructor. The decodings q of the first recursive group
-- determine the parameter type B, and with the parameter b the second
-- arity C.

record Schema (ℓ : Level) : Set (lsuc ℓ) where
  field
    I : Set ℓ
    A : I → Set ℓ
    B : (i : I) → (A i → Set ℓ) → Set ℓ
    C : (i : I) (q : A i → Set ℓ) → B i q → Set ℓ
    R : (i : I) (q : A i → Set ℓ) (b : B i q) → (C i q b → Set ℓ) → Set ℓ

description : {ℓ : Level} → Schema ℓ → Desc {s = ℓ} (Set ℓ)
description S =
  σ (Schema.I S) (λ i →
    δ (Schema.A S i) (λ q →
      σ (Schema.B S i q) (λ b →
        δ (Schema.C S i q b) (λ r → ι (Schema.R S i q b r)))))

------------------------------------------------------------------------
-- Decoding by conversion

-- The smallness principle from the reflector whose names hold by refl.

small : (ℓ : Level) → Smallness ℓ
small ℓ = Reflection.smallness (reflector ℓ)

output-β :
  {ℓ : Level} (S : Schema ℓ)
  (z : Shape (description S)
         (indexed (G (small ℓ) (description S))
           (t (small ℓ) (description S))))
  → t (small ℓ) (description S) (make (small ℓ) (description S) z)
    ＝ Mark (description S)
         (indexed (G (small ℓ) (description S))
           (t (small ℓ) (description S)))
         z
output-β S z = refl

------------------------------------------------------------------------
-- A point of every type

-- No recursive inputs.
none : {ℓ κ : Level} {X : Set κ} → Lift ℓ 𝟘 → X
none x = 𝟘-elim (lower x)

-- Empty recursive arities, with the given type as output.
seed : {ℓ : Level} → Set ℓ → Schema ℓ
seed {ℓ} T = record
  { I = Lift ℓ 𝟙
  ; A = λ _ → Lift ℓ 𝟘
  ; B = λ _ _ → Lift ℓ 𝟙
  ; C = λ _ _ _ → Lift ℓ 𝟘
  ; R = λ _ _ _ _ → T
  }

point : {ℓ : Level} (T : Set ℓ) → G (small ℓ) (description (seed T))
point {ℓ} T =
  make (small ℓ) (description (seed T))
    (lift ⋆ , (none , (lift ⋆ , (none , lift ⋆))))

point-β :
  {ℓ : Level} (T : Set ℓ)
  → t (small ℓ) (description (seed T)) (point T) ＝ T
point-β T = refl
