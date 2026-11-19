{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Groups where

-- Groups: a set with an associative multiplication, a two-sided unit and
-- two-sided inverses (`Group`). Left multiplication by g is an isomorphism
-- of the elements, inverted by left multiplication by the inverse of g
-- (`left-multiplication`), and it sends the unit to g
-- (`left-multiplication-at-the-unit`).

open import SPT.Base
open import SPT.Foundation.Isomorphisms using (_≅_; forward)
open import SPT.Foundation.Propositions using (is-set)

------------------------------------------------------------------------
-- Groups

record Group (ℓ : Level) : Set (lsuc ℓ) where
  field
    elements : Set ℓ
    elements-form-a-set : is-set elements
    unit : elements
    multiplication : elements → elements → elements
    inverse : elements → elements
    multiplication-is-associative : (x y z : elements) →
      multiplication (multiplication x y) z
        ＝ multiplication x (multiplication y z)
    unit-is-left-neutral : (x : elements) → multiplication unit x ＝ x
    unit-is-right-neutral : (x : elements) → multiplication x unit ＝ x
    inverses-are-left-inverses : (x : elements) →
      multiplication (inverse x) x ＝ unit
    inverses-are-right-inverses : (x : elements) →
      multiplication x (inverse x) ＝ unit

module _ {ℓ : Level} (G : Group ℓ) where

  Elements : Set ℓ
  Elements = Group.elements G

multiply : {ℓ : Level} (G : Group ℓ) → Elements G → Elements G → Elements G
multiply G = Group.multiplication G

infixl 40 multiply
syntax multiply G x y = x ·⟨ G ⟩ y

------------------------------------------------------------------------
-- Left multiplication

-- x ↦ g · x is undone by x ↦ g⁻¹ · x on either side, by associativity, the
-- inverse laws and the left unit law.

module _ {ℓ : Level} (G : Group ℓ) where

  -- Mathematical shape: x ↦ g · x, with inverse x ↦ g⁻¹ · x.
  left-multiplication : Elements G → Elements G ≅ Elements G
  left-multiplication g = record
    { forward = λ x → g ·⟨ G ⟩ x
    ; backward = λ x → Group.inverse G g ·⟨ G ⟩ x
    ; backward-forward = λ x →
        Group.multiplication-is-associative G (Group.inverse G g) g x ⁻¹
        ∙ ap (λ y → y ·⟨ G ⟩ x) (Group.inverses-are-left-inverses G g)
        ∙ Group.unit-is-left-neutral G x
    ; forward-backward = λ x →
        Group.multiplication-is-associative G g (Group.inverse G g) x ⁻¹
        ∙ ap (λ y → y ·⟨ G ⟩ x) (Group.inverses-are-right-inverses G g)
        ∙ Group.unit-is-left-neutral G x
    }

  left-multiplication-at-the-unit : (g : Elements G) →
    forward (left-multiplication g) (Group.unit G) ＝ g
  left-multiplication-at-the-unit g = Group.unit-is-right-neutral G g
