{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Signature.Coproduct where

-- Dependent coproducts of signatures over one judgment type. For a family
-- of signatures over J indexed by a type of choices, an operation at j is a
-- literal choice with an operation of the chosen signature at j; its
-- positions and their boundary judgments are that signature's
-- (`coproduct-operation`, `coproduct-position`,
-- `coproduct-position-boundary`, `coproduct-signature-over`,
-- `coproduct-signature`):
--
--   Operation j = Σ (c : Choice). Operation (S c) j,
--   Position (c , o) = Position (S c) o.
--
-- The choice is operation data: it is neither inferred from the chosen
-- operation nor identified when two signatures have equal operation types.
--
-- A signature lifted to higher levels keeps its operations and positions
-- under `Lift` (`lift-signature-over`). The binary sum of two signatures is
-- the coproduct over 𝟚 of the two, each lifted to the levels of both
-- (`sum-summand`, `sum-signature-over`, `sum-signature`):
--
--   Operation (Σ ⊕ Ω) j = Σ (c : 𝟚). Operation (summand c) j,
--   Position (₀ , lift o) = Lift (Position Σ o),
--
-- so an operation of either summand enters with its exact positions and
-- boundary judgments (`inject-left`, `inject-right`, both injective:
-- `inject-left-is-injective`, `inject-right-is-injective`).

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Signature using (Signature)
open import SPT.Cubical.Foundation.Signature.Sum using
  (Signature-Over; Operation; Position; position-boundary; to-signature)

module _
  {ℓj ℓc ℓo ℓp : Level} {J : Set ℓj} (Choice : Set ℓc)
  (signature : Choice → Signature-Over J ℓo ℓp)
  where

  coproduct-operation : J → Set (ℓc ⊔ ℓo)
  coproduct-operation j = Σ Choice (λ c → Operation (signature c) j)

  coproduct-position : {j : J} → coproduct-operation j → Set ℓp
  coproduct-position (c , o) = Position (signature c) o

  coproduct-position-boundary :
    {j : J} (o : coproduct-operation j) → coproduct-position o → J
  coproduct-position-boundary (c , o) p = position-boundary (signature c) o p

  coproduct-signature-over : Signature-Over J (ℓc ⊔ ℓo) ℓp
  coproduct-signature-over = record
    { Operation = coproduct-operation
    ; Position = coproduct-position
    ; position-boundary = coproduct-position-boundary
    }

  coproduct-signature : Signature ℓj (ℓc ⊔ ℓo) ℓp
  coproduct-signature = to-signature coproduct-signature-over

------------------------------------------------------------------------
-- Lifting the levels of a signature

module _ {ℓj ℓo ℓp : Level} {J : Set ℓj} (ℓo′ ℓp′ : Level)
  (signature : Signature-Over J ℓo ℓp)
  where

  lift-signature-over : Signature-Over J (ℓo ⊔ ℓo′) (ℓp ⊔ ℓp′)
  lift-signature-over = record
    { Operation = λ j → Lift ℓo′ (Operation signature j)
    ; Position = λ o → Lift ℓp′ (Position signature (lower o))
    ; position-boundary = λ o p →
        position-boundary signature (lower o) (lower p)
    }

------------------------------------------------------------------------
-- Binary sums: coproducts over the two-point type

module _ {ℓj ℓo₁ ℓp₁ ℓo₂ ℓp₂ : Level} {J : Set ℓj}
  (left : Signature-Over J ℓo₁ ℓp₁) (right : Signature-Over J ℓo₂ ℓp₂)
  where

  sum-summand : 𝟚 → Signature-Over J (ℓo₁ ⊔ ℓo₂) (ℓp₁ ⊔ ℓp₂)
  sum-summand ₀ = lift-signature-over ℓo₂ ℓp₂ left
  sum-summand ₁ = lift-signature-over ℓo₁ ℓp₁ right

  sum-signature-over : Signature-Over J (ℓo₁ ⊔ ℓo₂) (ℓp₁ ⊔ ℓp₂)
  sum-signature-over = coproduct-signature-over 𝟚 sum-summand

  sum-signature : Signature ℓj (ℓo₁ ⊔ ℓo₂) (ℓp₁ ⊔ ℓp₂)
  sum-signature = to-signature sum-signature-over

  inject-left : {j : J} → Operation left j → Operation sum-signature-over j
  inject-left o = ₀ , lift o

  inject-right : {j : J} → Operation right j → Operation sum-signature-over j
  inject-right o = ₁ , lift o

  inject-left-is-injective : {j : J} {o o′ : Operation left j} →
    inject-left o ＝ inject-left o′ → o ＝ o′
  inject-left-is-injective refl = refl

  inject-right-is-injective : {j : J} {o o′ : Operation right j} →
    inject-right o ＝ inject-right o′ → o ＝ o′
  inject-right-is-injective refl = refl
