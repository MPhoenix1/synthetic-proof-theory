{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Identifications where

-- Identifications acted on by dependent functions, transport along
-- applications, in constant families and in families of identifications,
-- transposition, identifications of pairs, and homotopies.
--
-- A dependent function sends an identification to one over it, through
-- transport (`apd`). Transport along an application is transport along the
-- action of the function (`transport-ap`), and transport in a constant
-- family is the identity (`transport-const`). A constant function sends
-- every identification to refl (`ap-const`). Transport along an
-- identification and back along its inverse returns the point, in either
-- order (`forth-and-back-transport`, `back-and-forth-transport`).
--
-- Transport in the fiber family of a map moves the source of an
-- identification, inverting the path along the map (`transport-fiber`);
-- transport in the family of identifications out of a point composes
-- (`transport-is-post-composition`):
--
--   transport (λ a → f a ＝ c) e u ＝ ap f e ⁻¹ ∙ u,
--   transport (λ w → x ＝ w) p q ＝ q ∙ p.
--
-- A composite determines its second factor (`left-transpose`); the inverse
-- of a difference cancels (`inverse-difference-cancels`); identifications
-- with trivial difference agree (`trivial-difference`). An identification
-- of pairs built by `to-Σ-＝` projects to its first component
-- (`ap-pr₁-to-Σ-＝`), and every identification of pairs carries the second
-- components along its first (`from-Σ-＝-pr₂`).
--
-- A homotopy between functions `f g : A → B` is an identification
-- `H a : f a ＝ g a` at every point; it is written as that dependent
-- function type, with no notation of its own. Homotopies are natural: along
-- an identification `p : x ＝ y` the square commutes
-- (`homotopies-are-natural`),
--
--   H x ∙ ap g p ＝ ap f p ∙ H y,
--
-- and a homotopy `H` from `h : A → A` to the identity commutes with `h`
-- (`identity-homotopies-are-natural`),
--
--   H (h x) ＝ ap h (H x).
--
-- After TypeTopology (UF.Base: apd, transport-ap, transport-const,
-- ap-const, forth-and-back-transport, back-and-forth-transport,
-- transport-fiber, with ap f e ⁻¹ for ap f (e ⁻¹), ap-pr₁-to-Σ-＝, from-Σ-＝'
-- as from-Σ-＝-pr₂, homotopies-are-natural; UF.Equiv:
-- id-homotopies-are-natural) and agda-unimath (left-transpose-eq-concat),
-- restated over SPT's identity type.

open import SPT.Base

------------------------------------------------------------------------
-- Dependent application

module _ {ℓ κ : Level} {A : Set ℓ} {P : A → Set κ} where

  apd : (f : (x : A) → P x) {x y : A} (p : x ＝ y) →
    transport P p (f x) ＝ f y
  apd f refl = refl

------------------------------------------------------------------------
-- Transport along an application and in a constant family

module _ {ℓ κ μ : Level} {A : Set ℓ} {B : Set κ} (P : B → Set μ) where

  transport-ap : (f : A → B) {x y : A} (p : x ＝ y) (u : P (f x)) →
    transport (λ a → P (f a)) p u ＝ transport P (ap f p) u
  transport-ap f refl u = refl

module _ {ℓ κ : Level} {A : Set ℓ} (P : A → Set κ) where

  forth-and-back-transport : {x y : A} (p : x ＝ y) (u : P x) →
    transport P (p ⁻¹) (transport P p u) ＝ u
  forth-and-back-transport refl u = refl

  back-and-forth-transport : {x y : A} (p : x ＝ y) (u : P y) →
    transport P p (transport P (p ⁻¹) u) ＝ u
  back-and-forth-transport refl u = refl

module _ {ℓ κ : Level} {A : Set ℓ} {B : Set κ} where

  transport-const : {x y : A} (p : x ＝ y) (b : B) →
    transport (λ _ → B) p b ＝ b
  transport-const refl b = refl

  ap-const : (b : B) {x y : A} (p : x ＝ y) → ap (λ _ → b) p ＝ refl
  ap-const b refl = refl

------------------------------------------------------------------------
-- Transport in families of identifications

module _ {ℓ κ : Level} {A : Set ℓ} {C : Set κ} where

  transport-fiber : (f : A → C) {x y : A} (e : x ＝ y) {c : C}
    (u : f x ＝ c) → transport (λ a → f a ＝ c) e u ＝ ap f e ⁻¹ ∙ u
  transport-fiber f refl u = refl

module _ {ℓ : Level} {A : Set ℓ} where

  transport-is-post-composition : {x y z : A} (q : x ＝ y) (p : y ＝ z) →
    transport (λ w → x ＝ w) p q ＝ q ∙ p
  transport-is-post-composition q refl = refl-right-neutral q ⁻¹

------------------------------------------------------------------------
-- Transposition

module _ {ℓ : Level} {A : Set ℓ} where

  left-transpose : {x y z : A} (r : x ＝ y) (p : y ＝ z) (s : x ＝ z) →
    r ∙ p ＝ s → p ＝ r ⁻¹ ∙ s
  left-transpose refl p s e = e

  inverse-difference-cancels : {x y z : A} (r : x ＝ z) (q : y ＝ z) →
    (r ∙ q ⁻¹) ⁻¹ ∙ r ＝ q
  inverse-difference-cancels refl refl = refl

  trivial-difference : {x y : A} (r p : x ＝ y) → r ⁻¹ ∙ p ＝ refl → r ＝ p
  trivial-difference refl p e = e ⁻¹

------------------------------------------------------------------------
-- Identifications of pairs

module _ {ℓ κ : Level} {A : Set ℓ} {B : A → Set κ} where

  ap-pr₁-to-Σ-＝ : {a a′ : A} {b : B a} {b′ : B a′} (e : a ＝ a′)
    (r : transport B e b ＝ b′) → ap pr₁ (to-Σ-＝ e r) ＝ e
  ap-pr₁-to-Σ-＝ refl refl = refl

  from-Σ-＝-pr₂ : {w w′ : Σ A B} (e : w ＝ w′) →
    transport B (ap pr₁ e) (pr₂ w) ＝ pr₂ w′
  from-Σ-＝-pr₂ refl = refl

------------------------------------------------------------------------
-- Homotopies are natural

module _ {ℓ κ : Level} {A : Set ℓ} {B : Set κ} where

  homotopies-are-natural : (f g : A → B) (H : (a : A) → f a ＝ g a)
    {x y : A} (p : x ＝ y) → H x ∙ ap g p ＝ ap f p ∙ H y
  homotopies-are-natural f g H {x} refl = refl-right-neutral (H x)

module _ {ℓ : Level} {A : Set ℓ} where

  identity-homotopies-are-natural : (h : A → A) (H : (a : A) → h a ＝ a)
    (x : A) → H (h x) ＝ ap h (H x)
  identity-homotopies-are-natural h H x =
    H (h x)
      ＝⟨ refl-right-neutral (H (h x)) ⁻¹ ⟩
    H (h x) ∙ refl
      ＝⟨ ap (λ q → H (h x) ∙ q) (right-inverse (H x) ⁻¹) ⟩
    H (h x) ∙ (H x ∙ H x ⁻¹)
      ＝⟨ ∙assoc (H (h x)) (H x) (H x ⁻¹) ⁻¹ ⟩
    (H (h x) ∙ H x) ∙ H x ⁻¹
      ＝⟨ ap (λ q → (H (h x) ∙ q) ∙ H x ⁻¹) (ap-id (H x) ⁻¹) ⟩
    (H (h x) ∙ ap id (H x)) ∙ H x ⁻¹
      ＝⟨ ap (λ q → q ∙ H x ⁻¹) (homotopies-are-natural h id H (H x)) ⟩
    (ap h (H x) ∙ H x) ∙ H x ⁻¹
      ＝⟨ ∙assoc (ap h (H x)) (H x) (H x ⁻¹) ⟩
    ap h (H x) ∙ (H x ∙ H x ⁻¹)
      ＝⟨ ap (λ q → ap h (H x) ∙ q) (right-inverse (H x)) ⟩
    ap h (H x) ∙ refl
      ＝⟨ refl-right-neutral (ap h (H x)) ⟩
    ap h (H x) ∎
