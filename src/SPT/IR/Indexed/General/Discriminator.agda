{-# OPTIONS --safe --without-K #-}

module SPT.IR.Indexed.General.Discriminator where

-- A general code whose constructors land at computed indices (`counter`,
-- IR.Description.Indexed.Counter): a seed at ₀ decoding to 0, and a
-- step taking a child at any index j and landing at the parity of its
-- decoding's successor, decoding to that successor. Elements sit at the
-- indices their arguments compute, and
-- their decodings compute (`one`, `two`, `three`, `three-decodes`).
-- Dybjer–Setzer induction computes at closed arguments, through the
-- transported method (`count`, `count-three`, by refl). At an open child
-- every element's decoding has the parity of its index, with no transport
-- (`parities`, `parity-of-index`). The identification is exact: a code
-- whose only constructor lands at ₀ has no element at ₁ (`seed`,
-- `nothing-at-₁`).

open import SPT.Base

open import SPT.IR.Description.Indexed using
  (IDS; ι; σ; δ; General; Mark; general)
open import SPT.IR.Description.Indexed.Counter using
  (parity; counter)
open import SPT.IR.Indexed using (U; value; family)
import SPT.IR.Indexed as Indexed
open import SPT.IR.General using (intro; Method; ind)
open import SPT.IR.Indexed.General using (universal)

zero-element : U (general counter) ₀
zero-element = intro (universal counter) (₀ , lift ⋆)

one : U (general counter) ₁
one = intro (universal counter) (₁ , ₀ , (λ _ → zero-element) , lift ⋆)

two : U (general counter) ₀
two = intro (universal counter) (₁ , ₁ , (λ _ → one) , lift ⋆)

three : U (general counter) ₁
three = intro (universal counter) (₁ , ₀ , (λ _ → two) , lift ⋆)

three-decodes : value (general counter) ₁ three ＝ 3
three-decodes = refl

------------------------------------------------------------------------
-- Induction at closed arguments

counting : Method (universal counter) (λ i u → ℕ)
counting (₀ , x) h = 0
counting (₁ , j , g , x) (k , h) = suc (k ⋆)

count : (i : 𝟚) → U (general counter) i → ℕ
count = ind (universal counter) (λ i u → ℕ) counting

count-three : count ₁ three ＝ 3
count-three = refl

------------------------------------------------------------------------
-- Decodings have the parity of their index

parities :
  Method (universal counter) (λ i u → parity (value (general counter) i u) ＝ i)
parities (₀ , x) h = refl
parities (₁ , j , g , x) h = refl

parity-of-index :
  (i : 𝟚) (u : U (general counter) i) → parity (value (general counter) i u) ＝ i
parity-of-index =
  ind (universal counter)
    (λ i u → parity (value (general counter) i u) ＝ i) parities

------------------------------------------------------------------------
-- Exactness of the identification

seed : General lzero lzero 𝟚 (λ _ → ℕ)
seed = ι (₀ , 0)

nothing-at-₁ : U (general seed) ₁ → 𝟘
nothing-at-₁ (Indexed.intro (y , ()))
