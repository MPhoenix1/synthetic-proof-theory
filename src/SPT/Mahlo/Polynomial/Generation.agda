{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Polynomial.Generation where

-- Generated small types with literal polynomial tree carriers. A diagram
-- in a family (C , D) gives a code to every index, operation and position
-- type, its input map retaining the exact index required at each position
-- (`Diagram`); it is a polynomial on the decoded indices
-- (`diagram-polynomial`). The generated codes (`Generated`, decoded by
-- `Value`) are the given codes of Polynomial.Basis's universe, sums and
-- products of families, the closed trees of every diagram of generated
-- codes at each index (`trees`, decoding as the closed trees of its
-- polynomial by refl, `trees-β`), and materializations: the power of a
-- code, or the fiber, total or section of a predicate into the small codes
-- (`Capability`, `Materialized`), repeatable (`power-β`, `twice-β`).
-- Functions and their higher types are products (`arrow`, `higher`,
-- `higher-β`). Basis supplies the given types; the generated codes own the
-- new tree types.

open import SPT.Base
open import SPT.Foundation.Signature.Polynomial using
  (Polynomial; bundled-endopolynomial-to-signature)
open import SPT.Foundation.Tree using (History)
import SPT.Mahlo.Universe as Universe
import SPT.Mahlo.Polynomial.Basis as Basis

------------------------------------------------------------------------
-- Diagrams

-- Every index, operation, and position type has a code. The input map
-- retains the exact index required at each position.

record Diagram {ℓ : Level} (C : Set ℓ) (D : C → Set ℓ) : Set ℓ where
  constructor diagram
  field
    index : C
    operation : D index → C
    position : (i : D index) → D (operation i) → C
    input : (i : D index) (o : D (operation i)) →
      D (position i o) → D index

module _ {ℓ : Level} {C : Set ℓ} {D : C → Set ℓ} where

  diagram-polynomial : (S : Diagram C D) →
    Polynomial (D (Diagram.index S)) (D (Diagram.index S)) ℓ ℓ
  diagram-polynomial S = record
    { Operation = λ i → D (Diagram.operation S i)
    ; Position = λ {i} o → D (Diagram.position S i o)
    ; input = λ {i} o p → Diagram.input S i o p
    }

------------------------------------------------------------------------
-- Generated codes and materializations

data Generated (ℓ : Level) : Set ℓ
Value : {ℓ : Level} → Generated ℓ → Set ℓ
data Capability {ℓ : Level} (g : Generated ℓ) : Set ℓ
Materialized : {ℓ : Level} (g : Generated ℓ) → Capability g → Set ℓ

data Generated ℓ where
  given : Basis.Code ℓ → Generated ℓ
  materialize : (g : Generated ℓ) → Capability g → Generated ℓ
  sum product : (g : Generated ℓ) → (Value g → Generated ℓ) → Generated ℓ
  trees : (S : Diagram (Generated ℓ) Value) → Value (Diagram.index S) →
    Generated ℓ

data Capability {ℓ} g where
  power : Capability g
  fiber : (p : Value g → Basis.Small ℓ) → Value g → Capability g
  total section : (Value g → Basis.Small ℓ) → Capability g

Value (given a) = Universe.decode a
Value (materialize g c) = Materialized g c
Value (sum g k) = Σ (Value g) (λ x → Value (k x))
Value (product g k) = (x : Value g) → Value (k x)
Value (trees (diagram a o p s) i) =
  History
    (bundled-endopolynomial-to-signature
      (Value a , record
        { Operation = λ j → Value (o j)
        ; Position = λ {j} x → Value (p j x)
        ; input = λ {j} x y → s j x y
        }))
    i

Materialized {ℓ} g power = Value g → Basis.Small ℓ
Materialized g (fiber p x) = Basis.small-decode (p x)
Materialized g (total p) = Σ (Value g) (λ x → Basis.small-decode (p x))
Materialized g (section p) = (x : Value g) → Basis.small-decode (p x)

------------------------------------------------------------------------
-- Computation laws

trees-β : {ℓ : Level} (S : Diagram (Generated ℓ) Value)
  (i : Value (Diagram.index S)) →
  Value (trees S i)
    ＝ History
      (bundled-endopolynomial-to-signature
        (Value (Diagram.index S) , diagram-polynomial S))
      i
trees-β S i = refl

materialize-β : {ℓ : Level} (g : Generated ℓ) (c : Capability g) →
  Value (materialize g c) ＝ Materialized g c
materialize-β g c = refl

power-β : {ℓ : Level} (g : Generated ℓ) →
  Value (materialize g power) ＝ (Value g → Basis.Small ℓ)
power-β g = refl

twice-β : {ℓ : Level} (g : Generated ℓ) →
  Value (materialize (materialize g power) power)
    ＝ ((Value g → Basis.Small ℓ) → Basis.Small ℓ)
twice-β g = refl

arrow : {ℓ : Level} → Generated ℓ → Generated ℓ → Generated ℓ
arrow g h = product g (λ x → h)

higher : {ℓ : Level} → Generated ℓ → Generated ℓ → Generated ℓ
higher g h = arrow (arrow g h) h

higher-β : {ℓ : Level} (g h : Generated ℓ) →
  Value (higher g h) ＝ ((Value g → Value h) → Value h)
higher-β g h = refl
