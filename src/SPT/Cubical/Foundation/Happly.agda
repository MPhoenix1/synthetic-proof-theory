{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Happly where

-- An identification of functions gives a homotopy, an identification at
-- every point (`happly`). Under function extensionality for the function
-- type, and for the type of the pointwise identifications from each of its
-- functions, `happly` has an inverse (`funext`), so identifications of
-- functions made by extensionality compute at every point.
--
-- The homotopies from `f`, with their targets, form a contractible type
-- (`homotopies-are-contractible`): it is the product of the based path
-- spaces of the values of `f`, rearranged. So a statement about every
-- homotopy from `f` follows from the one about the constant homotopy
-- (`homotopy-induction`). The inverse is extensionality adjusted to send
-- the constant homotopy to refl (`funext`, `funext-refl`), and the two are
-- inverse (`funext-happly`, `happly-funext`; `happly-is-invertible`):
--
--   funext f g (happly e) ＝ e,   happly (funext f g h) ＝ h.
--
-- `happly` respects composition and inverses (`happly-∙`, `happly-⁻¹`),
-- reads post-composition as `ap` (`happly-post`), and pre-composition as
-- evaluation at the image (`happly-pre`). A loop of functions that is refl
-- at every point is refl (`pointwise-trivial-loops-are-refl`). Transport of
-- a dependent function along an identification of the index function is,
-- at a point, transport along its happly there (`transport-at`).
--
-- After TypeTopology (UF.Base: happly; UF.Yoneda: funext-via-singletons),
-- by homotopy induction instead of the Yoneda lemma. Extensionality here is
-- the dependent hypothesis `FunExt A B`, so a product of contractible types
-- is contractible directly (SPT.Cubical.Foundation.Contractible).

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Extensionality using (FunExt)
open import SPT.Cubical.Foundation.Contractible using
  (is-contractible; based-path-spaces-are-contractible; Π-is-contractible)
open import SPT.Cubical.Foundation.Isomorphisms using (_≅_)

------------------------------------------------------------------------
-- Homotopies from identifications

module _ {ℓ κ : Level} {A : Set ℓ} {B : A → Set κ} where

  happly : {f g : (x : A) → B x} → f ＝ g → (x : A) → f x ＝ g x
  happly refl x = refl

  -- At a point, happly is the action of evaluation.
  happly-is-ap : {f g : (x : A) → B x} (e : f ＝ g) (x : A) →
    happly e x ＝ ap (λ k → k x) e
  happly-is-ap refl x = refl

  happly-∙ : {f g k : (x : A) → B x} (d : f ＝ g) (e : g ＝ k) (x : A) →
    happly (d ∙ e) x ＝ happly d x ∙ happly e x
  happly-∙ refl e x = refl

  happly-⁻¹ : {f g : (x : A) → B x} (e : f ＝ g) (x : A) →
    happly (e ⁻¹) x ＝ happly e x ⁻¹
  happly-⁻¹ refl x = refl

module _ {ℓ κ μ : Level} {A : Set ℓ} {B : Set κ} {C : Set μ} where

  -- Post-composition with k.
  happly-post : (k : B → C) {f g : A → B} (e : f ＝ g) (x : A) →
    happly (ap (λ m y → k (m y)) e) x ＝ ap k (happly e x)
  happly-post k refl x = refl

  -- Pre-composition with m.
  happly-pre : (m : A → B) {f g : B → C} (e : f ＝ g) (x : A) →
    happly (ap (λ k y → k (m y)) e) x ＝ happly e (m x)
  happly-pre m refl x = refl

module _ {ℓ κ μ : Level} {A : Set ℓ} {X : Set κ} (P : X → Set μ) where

  -- Transport of a section over an index function, at a point.
  transport-at : {f g : A → X} (e : f ＝ g) (t : (a : A) → P (f a))
    (a : A) →
    transport (λ k → (b : A) → P (k b)) e t a
      ＝ transport P (happly e a) (t a)
  transport-at refl t a = refl

------------------------------------------------------------------------
-- Homotopy induction

module _ {ℓ κ : Level} {A : Set ℓ} {B : A → Set κ} (f : (x : A) → B x)
  where

  -- The homotopies from f, with their targets, form a contractible type.
  homotopies-are-contractible :
    FunExt A (λ x → Σ (B x) (λ y → f x ＝ y)) →
    is-contractible (Σ ((x : A) → B x) (λ g → (x : A) → f x ＝ g x))
  homotopies-are-contractible extensionality =
    let c = Π-is-contractible extensionality
              (λ x → based-path-spaces-are-contractible (f x))
    in ((λ x → pr₁ (pr₁ c x)) , (λ x → pr₂ (pr₁ c x))) ,
       (λ gh → ap (λ k → (λ x → pr₁ (k x)) , (λ x → pr₂ (k x)))
         (pr₂ c (λ x → pr₁ gh x , pr₂ gh x)))

  -- A statement about every homotopy from f follows from the constant one.
  homotopy-induction : FunExt A (λ x → Σ (B x) (λ y → f x ＝ y)) →
    {μ : Level} (P : (g : (x : A) → B x) → ((x : A) → f x ＝ g x) → Set μ) →
    P f (λ x → refl) →
    (g : (x : A) → B x) (h : (x : A) → f x ＝ g x) → P g h
  homotopy-induction extensionality P p g h =
    let contraction = pr₂ (homotopies-are-contractible extensionality)
    in transport (λ gh → P (pr₁ gh) (pr₂ gh))
         (contraction (f , (λ x → refl)) ⁻¹ ∙ contraction (g , h)) p

------------------------------------------------------------------------
-- The inverse of happly

module _ {ℓ κ : Level} {A : Set ℓ} {B : A → Set κ} where

  -- Extensionality, adjusted to send the constant homotopy to refl.
  funext : FunExt A B → (f g : (x : A) → B x) →
    ((x : A) → f x ＝ g x) → f ＝ g
  funext extensionality f g h =
    extensionality f f (λ x → refl) ⁻¹ ∙ extensionality f g h

  funext-refl : (extensionality : FunExt A B) (f : (x : A) → B x) →
    funext extensionality f f (λ x → refl) ＝ refl
  funext-refl extensionality f =
    left-inverse (extensionality f f (λ x → refl))

  funext-happly : (extensionality : FunExt A B) {f g : (x : A) → B x}
    (e : f ＝ g) → funext extensionality f g (happly e) ＝ e
  funext-happly extensionality {f} refl = funext-refl extensionality f

  happly-funext : (extensionality : FunExt A B)
    (extensionality′ : (f : (x : A) → B x) →
      FunExt A (λ x → Σ (B x) (λ y → f x ＝ y)))
    (f g : (x : A) → B x) (h : (x : A) → f x ＝ g x) →
    happly (funext extensionality f g h) ＝ h
  happly-funext extensionality extensionality′ f g h =
    homotopy-induction f (extensionality′ f)
      (λ g′ h′ → happly (funext extensionality f g′ h′) ＝ h′)
      (ap happly (funext-refl extensionality f)) g h

  -- So happly is invertible.
  happly-is-invertible : (extensionality : FunExt A B)
    (extensionality′ : (f : (x : A) → B x) →
      FunExt A (λ x → Σ (B x) (λ y → f x ＝ y)))
    (f g : (x : A) → B x) → (f ＝ g) ≅ ((x : A) → f x ＝ g x)
  happly-is-invertible extensionality extensionality′ f g = record
    { forward = happly
    ; backward = funext extensionality f g
    ; backward-forward = funext-happly extensionality
    ; forward-backward = happly-funext extensionality extensionality′ f g
    }

  -- A loop of functions refl at every point is refl.
  pointwise-trivial-loops-are-refl : (extensionality : FunExt A B)
    {f : (x : A) → B x} → FunExt A (λ x → f x ＝ f x) →
    (e : f ＝ f) → ((x : A) → happly e x ＝ refl) → e ＝ refl
  pointwise-trivial-loops-are-refl extensionality {f} extensionality′ e h =
    funext-happly extensionality e ⁻¹
      ∙ (ap (funext extensionality f f)
          (extensionality′ (happly e) (λ x → refl) h)
        ∙ funext-refl extensionality f)
