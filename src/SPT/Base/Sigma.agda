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
-- spelling.
--
-- Two pairs are identified by an identification of their first components
-- and one of their second components over it (`to-Σ-＝`). An identification
-- of pairs built so projects to the identification of the first components
-- (`ap-pr₁-to-Σ-＝`), and every identification of pairs carries the second
-- components along the identification of the first (`from-Σ-＝-pr₂`).
--
-- For a section f of the family z ↦ Σ B (P z), the second component at x,
-- transported along p : x ＝ y in the first argument and then along the
-- induced identification of the first components in the second, is the
-- second component at y (`transport-section-pr₂`).
--
-- Transport through a family of retractions over a map of bases:
-- `section-along-retraction` identifies a transported section and
-- `pair-along-retraction` its dependent pair.

open import Agda.Builtin.Sigma public
  using (Σ)
  renaming (_,_ to infixr 3 _,_; fst to pr₁; snd to pr₂)

open import SPT.Base.Universes
open import SPT.Base.Identity using (_＝_; refl; transport; _⁻¹; ap)

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

  ap-pr₁-to-Σ-＝ : {a a′ : A} {b : B a} {b′ : B a′} (e : a ＝ a′)
    (r : transport B e b ＝ b′) → ap pr₁ (to-Σ-＝ e r) ＝ e
  ap-pr₁-to-Σ-＝ refl refl = refl

  from-Σ-＝-pr₂ : {w w′ : Σ A B} (e : w ＝ w′) →
    transport B (ap pr₁ e) (pr₂ w) ＝ pr₂ w′
  from-Σ-＝-pr₂ refl = refl

------------------------------------------------------------------------
-- Sections and transport in two arguments

module _ {ℓ κ μ : Level} {A : Set ℓ} {B : Set κ} {P : A → B → Set μ} where

  transport-section-pr₂ : (f : (z : A) → Σ B (P z)) {x y : A}
    (p : x ＝ y) →
    transport (P y) (ap (λ z → pr₁ (f z)) p)
      (transport (λ z → P z (pr₁ (f x))) p (pr₂ (f x)))
      ＝ pr₂ (f y)
  transport-section-pr₂ f refl = refl

------------------------------------------------------------------------
-- Transport through retractions

module _ {ℓ μ ν ρ : Level} {X : Set ℓ} {Y : Set μ}
  (o : X → Y) (Q : Y → Set ν) (R : X → Set ρ)
  (enter : (y : X) → Q (o y) → R y) (leave : (y : X) → R y → Q (o y))
  (round : (y : X) (r : R y) → enter y (leave y r) ＝ r) where

  section-along-retraction : (F : (y : X) → R y) {y₀ y : X} (e : y₀ ＝ y) →
    enter y (transport Q (ap o e) (leave y₀ (F y₀))) ＝ F y
  section-along-retraction F {y₀} refl = round y₀ (F y₀)

  pair-along-retraction : {y₀ y : X} (e : y₀ ＝ y) (z : R y) →
    _＝_ {A = Σ X R}
      (y₀ , enter y₀ (transport Q (ap o e ⁻¹) (leave y z))) (y , z)
  pair-along-retraction {y₀} refl z = ap (λ u → _,_ {B = R} y₀ u) (round y₀ z)
