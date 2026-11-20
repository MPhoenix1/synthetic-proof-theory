{-# OPTIONS --safe --without-K #-}

module SPT.IR.Polynomial.Action where

-- Maps of families that keep the readouts act on arguments, keeping their
-- information (`Map`, `action`, `map`, `map-info`). At a sum the identity
-- of first informations moves the continuation's argument, and the pair of
-- informations follows (`pair-info`); at a product extensionality
-- identifies the information functions.

open import SPT.Base

open import SPT.IR.Polynomial using
  (Poly; var; con; sigma; pi; Family; carrier; readout; Args; info;
   Extensionality)

record Map {ι ℓ κ : Level} {I : Set ι} {D : I → Set (ℓ ⊔ κ)}
  (Z W : Family ℓ κ D) : Set (ℓ ⊔ κ ⊔ ι) where
  field
    function : (i : I) → carrier Z i → carrier W i
    preserve :
      (i : I) (x : carrier Z i) → readout Z i x ＝ readout W i (function i x)

-- A pair whose second component is moved along an identity of first
-- components.
pair-info :
  {α β ν : Level} {A : Set α} (B : A → Set β) (C : A → Set ν)
  (f : (x : A) → B x → C x) {x y : A} (e : x ＝ y) (b : B x)
  → _＝_ {A = Σ A C} (y , f y (transport B e b)) (x , f x b)
pair-info B C f refl b = refl

module _ {ι ℓ κ : Level} {I : Set ι} {D : I → Set (ℓ ⊔ κ)} where

  action :
    Extensionality ℓ κ → {Z W : Family ℓ κ D} → Map Z W
    → {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ D X) (a : Args p Z)
    → Σ (Args p W) (λ b → info p W b ＝ info p Z a)
  action extensionality m (var i) a =
    Map.function m i a , Map.preserve m i a ⁻¹
  action extensionality m (con A) a = a , refl
  action extensionality {Z} {W} m (sigma {X} {Y} p q) (a , b) =
    let left = action extensionality m p a
        right = action extensionality m (q (info p Z a)) b
    in
    ( pr₁ left
    , transport (λ x → Args (q x) W) (pr₂ left ⁻¹) (pr₁ right)) ,
    ( pair-info (λ x → Args (q x) W) Y (λ x → info (q x) W)
        (pr₂ left ⁻¹) (pr₁ right)
    ∙ ap (λ y → (info p Z a , y)) (pr₂ right))
  action extensionality {Z} {W} m (pi A {Y} p) f =
    let branch = λ a → action extensionality m (p a) (f a)
    in
    (λ a → pr₁ (branch a)) ,
    extensionality A Y
      (λ a → info (p a) W (pr₁ (branch a)))
      (λ a → info (p a) Z (f a))
      (λ a → pr₂ (branch a))

  map :
    Extensionality ℓ κ → {Z W : Family ℓ κ D} → Map Z W
    → {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ D X) → Args p Z → Args p W
  map extensionality m p a = pr₁ (action extensionality m p a)

  map-info :
    (extensionality : Extensionality ℓ κ) {Z W : Family ℓ κ D}
    (m : Map Z W) {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ D X) (a : Args p Z)
    → info p W (map extensionality m p a) ＝ info p Z a
  map-info extensionality m p a = pr₂ (action extensionality m p a)
