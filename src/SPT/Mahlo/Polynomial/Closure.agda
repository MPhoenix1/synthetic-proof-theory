{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Polynomial.Closure where

-- A small induction–recursive closure of an operator Ψ over a Tarski
-- family (C , D) with formers Q, whose dependent operations are literal
-- open polynomial trees (`Code`, `interpret`). A preceding code a
-- determines each block's arity: a block is a tree of the one-color
-- polynomial whose operations are the four kinds and whose positions are
-- the points of D (interpret a) (`Kind`, `block-polynomial`), and its
-- holes contain closure codes. A block runs to the parent code it names,
-- each node by its kind: a product, sum or tree of the family of its
-- children, or Ψ's result at it (`run`); result points retain their
-- branches (`branch`). The selected formers are blocks of one node over
-- holes (`block-form`), so the codes form a closure of Ψ, each name and
-- the inner law by refl (`closure`).

open import SPT.Base
open import SPT.Foundation.Signature.Polynomial using
  (Polynomial; bundled-endopolynomial-to-signature)
open import SPT.Foundation.Tree using (Tree; hole; node)
open import SPT.Mahlo.Specification using (Operator; Formers; Closure)

------------------------------------------------------------------------
-- Blocks

data Kind : Set where
  pi sigma w apply : Kind

block-polynomial : {ℓ : Level} → Set ℓ → Polynomial 𝟙 𝟙 lzero ℓ
block-polynomial A = record
  { Operation = λ o → Kind
  ; Position = λ k → A
  ; input = λ k x → ⋆
  }

------------------------------------------------------------------------
-- The codes, their interpretation, and the run of a block

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} (Q : Formers C D)
  (Ψ : Operator D) where

  data Code : Set ℓ
  interpret : Code → C

  -- A block at a code a is a tree whose positions are the points of a.

  data Code where
    empty unit two natural : Code
    block : (a : Code) →
      Tree (bundled-endopolynomial-to-signature
        (𝟙 , block-polynomial (D (interpret a))))
        (λ j → Code) ⋆ →
      Code
    identity : (a : Code) → D (interpret a) → D (interpret a) → Code
    branch : (a : Code) (b : D (interpret a) → Code) →
      D (pr₁ (Ψ (interpret a , (λ x → interpret (b x))))) → Code

  run : (a : Code) →
    Tree (bundled-endopolynomial-to-signature
      (𝟙 , block-polynomial (D (interpret a))))
      (λ j → Code) ⋆ →
    C

  interpret empty = Formers.empty Q
  interpret unit = Formers.unit Q
  interpret two = Formers.two Q
  interpret natural = Formers.natural Q
  interpret (block a t) = run a t
  interpret (identity a x y) = Formers.identity Q (interpret a) x y
  interpret (branch a b y) =
    pr₂ (Ψ (interpret a , (λ x → interpret (b x)))) y

  run a (hole b) = interpret b
  run a (node pi k) =
    Formers.product Q (interpret a , (λ x → run a (k x)))
  run a (node sigma k) = Formers.sum Q (interpret a , (λ x → run a (k x)))
  run a (node w k) = Formers.tree Q (interpret a , (λ x → run a (k x)))
  run a (node apply k) = pr₁ (Ψ (interpret a , (λ x → run a (k x))))

  ----------------------------------------------------------------------
  -- The closure

  block-form : Kind → (a : Code) → (D (interpret a) → Code) → Code
  block-form k a b = block a (node k (λ x → hole (b x)))

  closure : Closure Q Ψ Code
  closure = record
    { interpret = interpret
    ; empty = empty , refl
    ; unit = unit , refl
    ; two = two , refl
    ; natural = natural , refl
    ; product = λ F → block-form pi (pr₁ F) (pr₂ F) , refl
    ; sum = λ F → block-form sigma (pr₁ F) (pr₂ F) , refl
    ; tree = λ F → block-form w (pr₁ F) (pr₂ F) , refl
    ; identity = λ a x y → identity a x y , refl
    ; inner = λ F →
        block-form apply (pr₁ F) (pr₂ F) , (λ y → branch (pr₁ F) (pr₂ F) y)
    ; inner-β = λ F → refl
    }
