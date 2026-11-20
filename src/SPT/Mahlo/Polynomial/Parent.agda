{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Polynomial.Parent where

-- A raised Tarski parent with small values, polynomial tree formation and
-- repeated materialization, Mahlo by the polynomial closures. Its codes
-- (`Generated`, decoded by `Value`) are the given codes of
-- Polynomial.Basis's universe, every type of the level admitted as a code
-- (`admit`), materializations as in Polynomial.Generation (`Capability`,
-- `Materialized`), sums, products, W-types and identity types, and the
-- trees of every polynomial on a decoded code with decoded holes
-- (`trees`). Its formers have their decoding laws by refl (`formers`,
-- `laws`). Every operator Ψ is reflected by admitting the polynomial-block
-- closure of Ψ (Polynomial.Closure) as a code (`reflect`, `reflected`,
-- `reflected-β`):
--
--   Value (reflected Ψ) ＝ Closure.Code (formers ℓ) Ψ,
--
-- so the parent is Mahlo unconditionally (`mahlo`), with its decoding laws
-- (`full`). Functions, their higher types, and twice the power decode as
-- expected (`arrow`, `higher`, `higher-β`, `power-β`, `twice-β`).

open import SPT.Base
open import SPT.Foundation.Signature.Polynomial using
  (Polynomial; bundled-endopolynomial-to-signature)
open import SPT.Foundation.Tree using (Tree)
open import SPT.Mahlo.Specification using
  (Operator; Formers; Reflection; Mahlo)
open import SPT.Foundation.Tree.W using (W)
open import SPT.Mahlo.Decoding using (DecodingLaws; MahloReflection)
import SPT.Mahlo.Universe as Universe
import SPT.Mahlo.Polynomial.Basis as Basis
import SPT.Mahlo.Polynomial.Closure as Block

------------------------------------------------------------------------
-- The codes and their decoding

data Generated (ℓ : Level) : Set (lsuc ℓ)
Value : {ℓ : Level} → Generated ℓ → Set ℓ
data Capability {ℓ : Level} (g : Generated ℓ) : Set ℓ
Materialized : {ℓ : Level} (g : Generated ℓ) → Capability g → Set ℓ

data Generated ℓ where
  given : Basis.Code ℓ → Generated ℓ
  admit : Set ℓ → Generated ℓ
  materialize : (g : Generated ℓ) → Capability g → Generated ℓ
  sum product well-founded : (g : Generated ℓ) →
    (Value g → Generated ℓ) → Generated ℓ
  identity : (g : Generated ℓ) → Value g → Value g → Generated ℓ
  trees : (g : Generated ℓ) → Polynomial (Value g) (Value g) ℓ ℓ →
    (Value g → Generated ℓ) → Value g → Generated ℓ

data Capability {ℓ} g where
  power : Capability g
  fiber : (p : Value g → Basis.Small ℓ) → Value g → Capability g
  total section : (Value g → Basis.Small ℓ) → Capability g

Value (given a) = Universe.decode a
Value (admit A) = A
Value (materialize g c) = Materialized g c
Value (sum g k) = Σ (Value g) (λ x → Value (k x))
Value (product g k) = (x : Value g) → Value (k x)
Value (well-founded g k) = W (Value g) (λ x → Value (k x))
Value (identity g x y) = x ＝ y
Value (trees g P h i) =
  Tree (bundled-endopolynomial-to-signature (Value g , P))
    (λ j → Value (h j)) i

Materialized {ℓ} g power = Value g → Basis.Small ℓ
Materialized g (fiber p x) = Basis.small-decode (p x)
Materialized g (total p) = Σ (Value g) (λ x → Basis.small-decode (p x))
Materialized g (section p) = (x : Value g) → Basis.small-decode (p x)

------------------------------------------------------------------------
-- Formers, laws and reflection

formers : (ℓ : Level) → Formers (Generated ℓ) Value
formers ℓ = record
  { empty = given Universe.empty
  ; unit = given Universe.unit
  ; two = given Universe.two
  ; natural = given Universe.natural
  ; product = λ F → product (pr₁ F) (pr₂ F)
  ; sum = λ F → sum (pr₁ F) (pr₂ F)
  ; tree = λ F → well-founded (pr₁ F) (pr₂ F)
  ; identity = identity
  }

laws : (ℓ : Level) → DecodingLaws (formers ℓ)
laws ℓ = record
  { empty-β = refl
  ; unit-β = refl
  ; two-β = refl
  ; natural-β = refl
  ; product-β = λ a b → refl
  ; sum-β = λ a b → refl
  ; tree-β = λ a b → refl
  ; identity-β = λ a x y → refl
  }

reflect : {ℓ : Level} (Ψ : Operator (Value {ℓ})) →
  Reflection (formers ℓ) Ψ
reflect {ℓ} Ψ = record
  { carrier = admit (Block.Code (formers ℓ) Ψ)
  ; closure = Block.closure (formers ℓ) Ψ
  }

mahlo : (ℓ : Level) → Mahlo (formers ℓ)
mahlo ℓ = record { reflect = reflect }

full : (ℓ : Level) → MahloReflection (formers ℓ)
full ℓ = record { codeReflection = mahlo ℓ ; decoding = laws ℓ }

reflected : {ℓ : Level} → Operator (Value {ℓ}) → Generated ℓ
reflected Ψ = Reflection.carrier (reflect Ψ)

reflected-β : {ℓ : Level} (Ψ : Operator (Value {ℓ})) →
  Value (reflected Ψ) ＝ Block.Code (formers ℓ) Ψ
reflected-β Ψ = refl

------------------------------------------------------------------------
-- Functions and powers

arrow : {ℓ : Level} → Generated ℓ → Generated ℓ → Generated ℓ
arrow g h = product g (λ x → h)

higher : {ℓ : Level} → Generated ℓ → Generated ℓ → Generated ℓ
higher g h = arrow (arrow g h) h

higher-β : {ℓ : Level} (g h : Generated ℓ) →
  Value (higher g h) ＝ ((Value g → Value h) → Value h)
higher-β g h = refl

power-β : {ℓ : Level} (g : Generated ℓ) →
  Value (materialize g power) ＝ (Value g → Basis.Small ℓ)
power-β g = refl

twice-β : {ℓ : Level} (g : Generated ℓ) →
  Value (materialize (materialize g power) power)
    ＝ ((Value g → Basis.Small ℓ) → Basis.Small ℓ)
twice-β g = refl
