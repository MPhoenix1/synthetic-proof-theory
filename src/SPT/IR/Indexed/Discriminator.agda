{-# OPTIONS --safe --without-K #-}

module SPT.IR.Indexed.Discriminator where

-- The universal family decodes by refl and keeps its codes, with no
-- hypothesis. The scheme is a universe: base types named by the numbers,
-- 𝟘 at zero and 𝟙 elsewhere, and the dependent sum of a code with a
-- family of codes over its decoding (`universe`, `named`, `sum`). Both
-- decode by refl (`named-β`, `sum-β`), so sums are inhabited or empty
-- with no transport (`pairs`, `no-pairs`). Two codes of 𝟙 decode alike
-- by refl yet stay distinct, as do the sums over them (`same-decoding`,
-- `codes-distinct`, `sum-decoding`, `sums-distinct`). Root recovery
-- returns the literal family (`retains`), and induction sees the nesting
-- (`depth`, `named-depth`, `nested-depth`).

open import SPT.Base

open import SPT.IR.Indexed using
  (U; Args; intro; value; Method; ind; root)
open import SPT.IR.Polynomial using
  (Poly; var; con; sigma; pi; Description; described; Scheme; shape)

------------------------------------------------------------------------
-- A universe of named base types and dependent sums

-- The information of a former is a number at a base name, and a type
-- with a family of types over it at a sum.

base : ℕ → Set
base zero = 𝟘
base (suc n) = 𝟙

Types : 𝟙 → Set (lsuc lzero)
Types i = Set

Shapes : Lift (lsuc lzero) 𝟚 → Set (lsuc lzero)
Shapes (lift ₀) = Lift (lsuc lzero) ℕ
Shapes (lift ₁) = Σ Set (λ A → A → Set)

formers :
  (t : Lift (lsuc lzero) 𝟚) → Poly lzero (lsuc lzero) Types (Shapes t)
formers (lift ₀) = con ℕ
formers (lift ₁) = sigma (var ⋆) (λ A → pi A (λ a → var ⋆))

decode : Σ (Lift (lsuc lzero) 𝟚) Shapes → Set
decode (lift ₀ , lift n) = base n
decode (lift ₁ , (A , B)) = Σ A B

rule : (i : 𝟙) → Description lzero (lsuc lzero) Types (Types i)
rule i = described (sigma (con 𝟚) formers) decode

universe : Scheme lzero (lsuc lzero)
universe = record { Index = 𝟙 ; Data = Types ; rule = rule }

named : ℕ → U universe ⋆
named n = intro (₀ , n)

sum :
  (a : U universe ⋆) → (value universe ⋆ a → U universe ⋆)
  → U universe ⋆
sum a f = intro (₁ , (a , f))

named-β : (n : ℕ) → value universe ⋆ (named n) ＝ base n
named-β n = refl

sum-β :
  (a : U universe ⋆) (f : value universe ⋆ a → U universe ⋆)
  → value universe ⋆ (sum a f)
    ＝ Σ (value universe ⋆ a) (λ x → value universe ⋆ (f x))
sum-β a f = refl

------------------------------------------------------------------------
-- Inhabited and empty sums

-- The decodings are literal types, so a sum over 𝟙 of 𝟙 is inhabited by
-- a pair and a sum over 𝟙 of 𝟘 is refuted by its second part.

empty unit unit′ : U universe ⋆
empty = named zero
unit = named (suc zero)
unit′ = named (suc (suc zero))

pairs : value universe ⋆ (sum unit (λ x → unit))
pairs = ⋆ , ⋆

no-pairs : value universe ⋆ (sum unit (λ x → empty)) → 𝟘
no-pairs (x , y) = y

------------------------------------------------------------------------
-- Equal decodings, distinct codes

-- The two codes of 𝟙 decode to 𝟙 by refl, and root recovery reads their
-- names apart. Sums over them decode alike and are told apart by their
-- first codes.

name : Args universe (shape (Scheme.rule universe ⋆)) → ℕ
name (₀ , n) = n
name (₁ , c) = zero

first : Args universe (shape (Scheme.rule universe ⋆)) → U universe ⋆
first (₀ , n) = named n
first (₁ , (a , f)) = a

same-decoding : value universe ⋆ unit ＝ value universe ⋆ unit′
same-decoding = refl

codes-distinct : unit ＝ unit′ → 𝟘
codes-distinct e =
  zero-is-not-suc (suc-is-injective (ap (λ u → name (root universe ⋆ u)) e))

sum-decoding :
  value universe ⋆ (sum unit (λ x → unit))
  ＝ value universe ⋆ (sum unit′ (λ x → unit))
sum-decoding = refl

sums-distinct : sum unit (λ x → unit) ＝ sum unit′ (λ x → unit) → 𝟘
sums-distinct e = codes-distinct (ap (λ u → first (root universe ⋆ u)) e)

retains :
  (a : U universe ⋆) (f : value universe ⋆ a → U universe ⋆)
  → root universe ⋆ (sum a f) ＝ (₁ , (a , f))
retains a f = refl

------------------------------------------------------------------------
-- Native induction observes the nesting

-- A base name has depth zero, and a sum one more than its first code.

Depth : (i : 𝟙) → U universe i → Set
Depth i u = ℕ

step : Method universe Depth
step i (₀ , n) h = zero
step i (₁ , (a , f)) h = suc (lower (pr₁ (pr₂ h)))

depth : U universe ⋆ → ℕ
depth = ind universe Depth step ⋆

named-depth : (n : ℕ) → depth (named n) ＝ zero
named-depth n = refl

nested-depth :
  depth (sum (sum unit (λ x → unit)) (λ x → unit)) ＝ suc (suc zero)
nested-depth = refl
