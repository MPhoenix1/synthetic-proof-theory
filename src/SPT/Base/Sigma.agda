{-# OPTIONS --safe --without-K #-}

module SPT.Base.Sigma where

-- For a type `A` and a family `B` over it, the dependent pair type
-- `Σ A (λ x → B x)` has as points the pairs `(a , b)` of a point `a` of `A`
-- and a point `b` of `B a`; `pr₁` and `pr₂` project them. It is the record of
-- `Agda.Builtin.Sigma`, with SPT's field names and fixity given in the
-- renaming, so it is also the standard library's Σ. Agda attaches no syntax
-- or fixity to an imported name, so Σ is written prefix, and its points are
-- built with `_,_` (a record expression must name the fields `fst` and
-- `snd`).
--
-- The product `A × B` is the dependent pair type of a constant family. It is
-- written `A × B` whenever the second type does not depend on the first, and
-- never as `Σ A (λ x → B)` with `B` constant, so each type keeps one
-- spelling. Two pairs are identified by an identification of their first
-- components and one of their second components over it (`to-Σ-＝`).

open import Agda.Builtin.Sigma public
  using (Σ)
  renaming (_,_ to infixr 3 _,_; fst to pr₁; snd to pr₂)

open import SPT.Base.Universes
open import SPT.Base.Identity using (_＝_; refl; transport)

------------------------------------------------------------------------
-- Products

infixr 15 _×_

_×_ : {ℓ κ : Level} (A : Set ℓ) (B : Set κ) → Set (ℓ ⊔ κ)
A × B = Σ A (λ _ → B)

------------------------------------------------------------------------
-- Identifications of pairs

module _ {ℓ κ : Level} {A : Set ℓ} {B : A → Set κ} where

  to-Σ-＝ : {a a′ : A} {b : B a} {b′ : B a′} (e : a ＝ a′) →
    transport B e b ＝ b′ → (a , b) ＝ (a′ , b′)
  to-Σ-＝ refl refl = refl
