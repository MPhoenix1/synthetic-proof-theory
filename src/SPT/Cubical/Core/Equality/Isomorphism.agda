{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.Equality.Isomorphism where

-- Isomorphisms of types, A ≅ B: two maps with pointwise inverse laws.  Their
-- identity, inverse and composite, their Σ-closure, and pointwise
-- comparison of two isomorphisms.  The inverse laws are pointwise; function
-- extensionality enters only as a named hypothesis (MapΠExt), to turn them
-- into equalities of functions.

open import Agda.Primitive using (Level; _⊔_)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; sym; trans)

open import SPT.Cubical.Core.Equality using (MapΠExt)

------------------------------------------------------------------------
-- Isomorphisms

--   A ≅ B = (forward : A → B) × (backward : B → A)
--           × (Π a. backward(forward(a)) = a)
--           × (Π b. forward(backward(b)) = b).

infix 4 _≅_

record _≅_ {ℓa ℓb : Level} (A : Set ℓa) (B : Set ℓb) : Set (ℓa ⊔ ℓb) where
  field
    forward : A → B
    backward : B → A
    backward-forward : (a : A) → backward (forward a) ≡ a
    forward-backward : (b : B) → forward (backward b) ≡ b

open _≅_ public

≅-refl :
    ∀ {ℓa : Level}
      {A : Set ℓa}
  → A ≅ A
≅-refl = record
  { forward = λ a → a
  ; backward = λ a → a
  ; backward-forward = λ a → refl
  ; forward-backward = λ a → refl
  }

≅-sym :
    ∀ {ℓa ℓb : Level}
      {A : Set ℓa}
      {B : Set ℓb}
  → A ≅ B
  → B ≅ A
≅-sym E =
  record
    { forward = backward E
    ; backward = forward E
    ; backward-forward = forward-backward E
    ; forward-backward = backward-forward E
    }

≅-trans :
    ∀ {ℓa ℓb ℓc : Level}
      {A : Set ℓa}
      {B : Set ℓb}
      {C : Set ℓc}
  → A ≅ B
  → B ≅ C
  → A ≅ C
≅-trans E F =
  record
    { forward = λ a → forward F (forward E a)
    ; backward = λ c → backward E (backward F c)
    ; backward-forward = λ a →
        trans
          (cong (backward E)
            (backward-forward F (forward E a)))
          (backward-forward E a)
    ; forward-backward = λ c →
        trans
          (cong (forward F)
            (forward-backward E (backward F c)))
          (forward-backward F c)
    }

-- Under extensionality for A → A and B → B, the inverse laws become
-- equalities of functions.

module WithΠExt
    {ℓa ℓb : Level}
    {A : Set ℓa}
    {B : Set ℓb}
    (domain-πext : MapΠExt A A)
    (codomain-πext : MapΠExt B B)
  where

  backward-forward-equality :
      (isomorphism : A ≅ B)
    → (λ point → backward isomorphism (forward isomorphism point))
        ≡ (λ point → point)
  backward-forward-equality isomorphism =
    domain-πext
      (λ point → backward isomorphism (forward isomorphism point))
      (λ point → point)
      (backward-forward isomorphism)

  forward-backward-equality :
      (isomorphism : A ≅ B)
    → (λ point → forward isomorphism (backward isomorphism point))
        ≡ (λ point → point)
  forward-backward-equality isomorphism =
    codomain-πext
      (λ point → forward isomorphism (backward isomorphism point))
      (λ point → point)
      (forward-backward isomorphism)

------------------------------------------------------------------------
-- Isomorphism of dependent sums

-- (Π i. L i ≅ R i) → Σ i. L i ≅ Σ i. R i.  The index is kept unchanged in
-- both directions; only the second component is mapped.

Σ-cong :
    ∀ {ℓ-index ℓ-left ℓ-right : Level}
      {Index : Set ℓ-index}
      {Left : Index → Set ℓ-left}
      {Right : Index → Set ℓ-right}
  → ((index : Index) → Left index ≅ Right index)
  → Σ Index Left ≅ Σ Index Right
Σ-cong pointwise =
  record
    { forward = λ where
        (index , left) →
          index , forward (pointwise index) left
    ; backward = λ where
        (index , right) →
          index , backward (pointwise index) right
    ; backward-forward = λ where
        (index , left) →
          cong
            (λ fiber → index , fiber)
            (backward-forward (pointwise index) left)
    ; forward-backward = λ where
        (index , right) →
          cong
            (λ fiber → index , fiber)
            (forward-backward (pointwise index) right)
    }

------------------------------------------------------------------------
-- Pointwise comparison of two isomorphisms

-- For E F : A ≅ B, a pointwise cell compares both maps:
--
--   PointwiseCell(E,F)
--     = (Π a. forward(E)(a) = forward(F)(a))
--       × (Π b. backward(E)(b) = backward(F)(b)).
--
-- The forward comparison determines the backward one through the inverse
-- laws (`pointwiseCell-from-forward`).

record PointwiseCell
    {ℓa ℓb : Level}
    {A : Set ℓa}
    {B : Set ℓb}
    (E F : A ≅ B)
    : Set (ℓa ⊔ ℓb)
  where
  field
    forward-≡ :
      (a : A) → forward E a ≡ forward F a

    backward-≡ :
      (b : B) → backward E b ≡ backward F b

open PointwiseCell public

pointwiseCell-from-forward :
    ∀ {ℓa ℓb : Level}
      {A : Set ℓa}
      {B : Set ℓb}
  → (E F : A ≅ B)
  → ((a : A) → forward E a ≡ forward F a)
  → PointwiseCell E F
pointwiseCell-from-forward E F forward-cell =
  record
    { forward-≡ = forward-cell
    ; backward-≡ = λ b →
        trans
          (sym
            (cong (backward E)
              (forward-backward F b)))
          (trans
            (cong (backward E)
              (sym (forward-cell (backward F b))))
            (backward-forward E (backward F b)))
    }

-- Under extensionality for A → B and B → A, a pointwise cell gives
-- equalities of the forward and of the backward maps.

module WithPointwiseCellΠExt
    {ℓa ℓb : Level}
    {A : Set ℓa}
    {B : Set ℓb}
    (forward-πext : MapΠExt A B)
    (backward-πext : MapΠExt B A)
  where

  forward-equality :
      {left right : A ≅ B}
    → PointwiseCell left right
    → forward left ≡ forward right
  forward-equality {left} {right} cell =
    forward-πext
      (forward left)
      (forward right)
      (forward-≡ cell)

  backward-equality :
      {left right : A ≅ B}
    → PointwiseCell left right
    → backward left ≡ backward right
  backward-equality {left} {right} cell =
    backward-πext
      (backward left)
      (backward right)
      (backward-≡ cell)
