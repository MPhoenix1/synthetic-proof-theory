{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Signature.Sum where

-- Signatures over one fixed judgment type. With the judgment type a
-- parameter, distinct fragments share one literal judgment family and
-- enter one signature without transport between separately packaged
-- judgment fields (`Signature-Over`, `to-signature`, `from-signature`).
-- Their binary sums are Signature.Coproduct's coproducts over 𝟚
-- (`sum-signature-over` there).

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Signature using
  (Signature; Judgment; Op; Pos; boundary)

------------------------------------------------------------------------
-- Signatures over one fixed judgment type

record Signature-Over {ℓj : Level} (J : Set ℓj) (ℓo ℓp : Level)
  : Set (lsuc (ℓj ⊔ ℓo ⊔ ℓp)) where
  field
    Operation : J → Set ℓo
    Position : {j : J} → Operation j → Set ℓp
    position-boundary : {j : J} (o : Operation j) → Position o → J

open Signature-Over public

module _ {ℓj ℓo ℓp : Level} {J : Set ℓj} where

  to-signature : Signature-Over J ℓo ℓp → Signature ℓj ℓo ℓp
  to-signature signature = record
    { Judgment = J
    ; Op = Operation signature
    ; Pos = Position signature
    ; boundary = position-boundary signature
    }

module _ {ℓj ℓo ℓp : Level} where

  from-signature : (signature : Signature ℓj ℓo ℓp) →
    Signature-Over (Judgment signature) ℓo ℓp
  from-signature signature = record
    { Operation = Op signature
    ; Position = Pos signature
    ; position-boundary = boundary signature
    }
