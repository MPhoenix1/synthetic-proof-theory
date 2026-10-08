{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.Nat.Pairing where

-- An injective pairing of ℕ × ℕ into ℕ through binary numerals: pair m n
-- is the numeral with m digits 2[1+_] outside n digits 1+[2_], and unpair
-- counts them back, so unpair is a left inverse of pair (unpair-pair).

open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Binary as Binary
import Data.Nat.Binary.Properties as BinaryProperties
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  decode : Binary.ℕᵇ → ℕ × ℕ
  decode Binary.zero = zero , zero
  decode Binary.2[1+ c ] with decode c
  ... | m , n = suc m , n
  decode Binary.1+[2 c ] with decode c
  ... | m , n = m , suc n

  encode : ℕ → ℕ → Binary.ℕᵇ
  encode zero zero = Binary.zero
  encode zero (suc n) = Binary.1+[2 encode zero n ]
  encode (suc m) n = Binary.2[1+ encode m n ]

  decode-encode : (m n : ℕ) → decode (encode m n) ≡ (m , n)
  decode-encode zero zero = refl
  decode-encode zero (suc n) rewrite decode-encode zero n = refl
  decode-encode (suc m) n rewrite decode-encode m n = refl

pair : ℕ → ℕ → ℕ
pair m n = Binary.toℕ (encode m n)

unpair : ℕ → ℕ × ℕ
unpair n = decode (Binary.fromℕ n)

unpair-pair : (m n : ℕ) → unpair (pair m n) ≡ (m , n)
unpair-pair m n
  rewrite BinaryProperties.fromℕ-toℕ (encode m n) = decode-encode m n
