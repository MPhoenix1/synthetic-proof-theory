{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.Equality.Contractibility where

-- Contractible types, their closure under Σ and, given function
-- extensionality for the function space, under Π; singletons are
-- contractible, and contractible types are sets.

open import Agda.Primitive using (Level)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Product.Properties using (Σ-≡,≡→≡)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans)
open import SPT.Cubical.Core.Equality using (DependentΠExt; IsSet)

-- IsContractible(A) = Σ(center : A). Π(point : A). center = point.

IsContractible :
    ∀ {ℓ : Level}
  → Set ℓ
  → Set ℓ
IsContractible A =
  Σ A (λ center →
    (point : A) →
    center ≡ point)


-- isContr(A) → (Π a. isContr(B(a))) → isContr(Σ a. B(a)).  The contraction
-- of A is eliminated first, so the fiber over the center is used directly.

dependentTotal-contractible :
    ∀ {ℓ-A ℓ-B : Level}
      {A : Set ℓ-A}
      {B : A → Set ℓ-B}
  → IsContractible A
  → ((point : A) → IsContractible (B point))
  → IsContractible (Σ A B)
dependentTotal-contractible
    {B = B}
    (center-A , contraction-A)
    fiber-contractible =
  (center-A , center-B) , contraction
  where
  center-B : B center-A
  center-B = proj₁ (fiber-contractible center-A)

  contraction :
      (point : Σ _ B)
    → (center-A , center-B) ≡ point
  contraction (point-A , point-B)
      with contraction-A point-A
  ... | refl =
    Σ-≡,≡→≡
      ( refl
      , proj₂ (fiber-contractible center-A) point-B
      )


-- Based path spaces are contractible.

basedPathTotal-contractible :
    ∀ {ℓ : Level} {A : Set ℓ}
  → (base : A)
  → IsContractible (Σ A (λ point → base ≡ point))
basedPathTotal-contractible base =
  (base , refl) , λ where
    (.base , refl) → refl


-- A contractible type is a set: every path equals the canonical path
-- obtained from the contraction.

contractible-isSet :
    ∀ {ℓ : Level} {A : Set ℓ}
  → IsContractible A
  → IsSet A
contractible-isSet {A = A} (center , contracts)
    left right first second =
  trans (sym (canonical first)) (canonical second)
  where
  cancel : ∀ {x y : A} (path : x ≡ y)
    → trans (sym path) path ≡ refl
  cancel refl = refl

  canonical : (path : left ≡ right)
    → trans (sym (contracts left)) (contracts right) ≡ path
  canonical refl = cancel (contracts left)


-- Under DependentΠExt(A,B): (Π x. isContr(B(x))) → isContr(Π x. B(x)).
-- Center and contraction are built pointwise; extensionality is used only
-- to turn the pointwise contraction into a path of functions.

module WithContractibleΠExt
    {ℓa ℓb : Level}
    {A : Set ℓa}
    {B : A → Set ℓb}
    (πext : DependentΠExt A B)
  where

  dependentFunction-contractible :
      ((point : A) → IsContractible (B point))
    → IsContractible ((point : A) → B point)
  dependentFunction-contractible fiber-contractible =
    center , contraction
    where
    center : (point : A) → B point
    center point =
      proj₁ (fiber-contractible point)

    contraction :
        (function : (point : A) → B point)
      → center ≡ function
    contraction function =
      πext center function
        (λ point →
          proj₂ (fiber-contractible point) (function point))
