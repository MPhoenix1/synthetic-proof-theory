{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.Equality.Fiber where

-- Homotopy fibers of functions, contractibility of all fibers, and the
-- refutation of a contractible fiber from two separated points in it.

open import Agda.Primitive using (Level; _⊔_)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; sym; trans)

open import SPT.Cubical.Core.Equality.Contractibility public
  using (IsContractible)

-- HomotopyFiber(f,y) = Σ(x : A). f(x) = y, with the path kept: this is
-- not the set-level inverse image.

HomotopyFiber :
    ∀ {ℓ-source ℓ-target : Level}
      {Source : Set ℓ-source}
      {Target : Set ℓ-target}
  → (Source → Target)
  → Target
  → Set (ℓ-source ⊔ ℓ-target)
HomotopyFiber {Source = Source} function target =
  Σ Source (λ source → function source ≡ target)


-- HasContractibleFibers(f) = Π(y : Target). isContr(HomotopyFiber(f,y)).

HasContractibleFibers :
    ∀ {ℓ-source ℓ-target : Level}
      {Source : Set ℓ-source}
      {Target : Set ℓ-target}
  → (Source → Target)
  → Set (ℓ-source ⊔ ℓ-target)
HasContractibleFibers {Target = Target} function =
  (target : Target) → IsContractible (HomotopyFiber function target)


-- Two points of a fiber whose sources are unequal refute contractibility.

separated-not-contractible :
    ∀ {ℓ-source ℓ-target : Level}
      {Source : Set ℓ-source}
      {Target : Set ℓ-target}
      {function : Source → Target}
      {target : Target}
      {left right : Source}
  → function left ≡ target
  → function right ≡ target
  → (left ≡ right → ⊥)
  → IsContractible (HomotopyFiber function target)
  → ⊥
separated-not-contractible
    left-path right-path separated (center , contracts) =
  separated
    (cong proj₁
      (trans
        (sym (contracts (_ , left-path)))
        (contracts (_ , right-path))))
