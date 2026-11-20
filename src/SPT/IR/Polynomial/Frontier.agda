{-# OPTIONS --safe --without-K #-}

module SPT.IR.Polynomial.Frontier where

-- Partial arguments of a polynomial code. A path stops at a recursive
-- input, at a constant or at the arity of a product, or continues into a
-- product's component, or into a sum's continuation through a complete
-- first argument (`Path`); it requests the constant or the arity
-- (`requested`). Paths move along an identity of informations (`shift`) and
-- along maps of families (`map`), keeping the requested type
-- (`requested-shift`, `requested-map`).

open import SPT.Base

open import SPT.IR.Polynomial using
  (Poly; var; con; sigma; pi; Family; Args; info; Extensionality)
import SPT.IR.Polynomial.Action as Action

module _ {ι ℓ κ : Level} {I : Set ι} {D : I → Set (ℓ ⊔ κ)} where

  Path : {X : Set (ℓ ⊔ κ)} → Poly ℓ κ D X → Family ℓ κ D → Set ℓ
  Path (var i) Z = Lift ℓ 𝟙
  Path (con A) Z = Lift ℓ 𝟙
  Path (sigma p q) Z =
    Path p Z ⊎ Σ (Args p Z) (λ a → Path (q (info p Z a)) Z)
  Path (pi A p) Z = Lift ℓ 𝟙 ⊎ Σ A (λ a → Path (p a) Z)

  requested :
    {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ D X) (Z : Family ℓ κ D) → Path p Z
    → Set ℓ
  requested (var i) Z _ = Lift ℓ 𝟙
  requested (con A) Z _ = A
  requested (sigma p q) Z (inl z) = requested p Z z
  requested (sigma p q) Z (inr (a , z)) = requested (q (info p Z a)) Z z
  requested (pi A p) Z (inl _) = A
  requested (pi A p) Z (inr (a , z)) = requested (p a) Z z

  shift :
    {X : Set (ℓ ⊔ κ)} {Y : X → Set (ℓ ⊔ κ)}
    (q : (x : X) → Poly ℓ κ D (Y x)) (Z : Family ℓ κ D) {u v : X}
    → u ＝ v → Path (q u) Z → Path (q v) Z
  shift q Z refl z = z

  requested-shift :
    {X : Set (ℓ ⊔ κ)} {Y : X → Set (ℓ ⊔ κ)}
    (q : (x : X) → Poly ℓ κ D (Y x)) (Z : Family ℓ κ D) {u v : X}
    (e : u ＝ v) (z : Path (q u) Z)
    → requested (q v) Z (shift q Z e z) ＝ requested (q u) Z z
  requested-shift q Z refl z = refl

  map :
    Extensionality ℓ κ → {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ D X)
    {Z W : Family ℓ κ D} → Action.Map Z W → Path p Z → Path p W
  map extensionality (var i) m z = z
  map extensionality (con A) m z = z
  map extensionality (sigma p q) m (inl z) =
    inl (map extensionality p m z)
  map extensionality (sigma p q) {Z} {W} m (inr (a , z)) =
    inr
      ( Action.map extensionality m p a
      , shift q W (Action.map-info extensionality m p a ⁻¹)
          (map extensionality (q (info p Z a)) m z))
  map extensionality (pi A p) m (inl z) = inl z
  map extensionality (pi A p) m (inr (a , z)) =
    inr (a , map extensionality (p a) m z)

  requested-map :
    (extensionality : Extensionality ℓ κ) {X : Set (ℓ ⊔ κ)}
    (p : Poly ℓ κ D X) {Z W : Family ℓ κ D} (m : Action.Map Z W)
    (z : Path p Z)
    → requested p W (map extensionality p m z) ＝ requested p Z z
  requested-map extensionality (var i) m z = refl
  requested-map extensionality (con A) m z = refl
  requested-map extensionality (sigma p q) m (inl z) =
    requested-map extensionality p m z
  requested-map extensionality (sigma p q) {Z} {W} m (inr (a , z)) =
    requested-shift q W (Action.map-info extensionality m p a ⁻¹)
      (map extensionality (q (info p Z a)) m z)
    ∙ requested-map extensionality (q (info p Z a)) m z
  requested-map extensionality (pi A p) m (inl z) = refl
  requested-map extensionality (pi A p) m (inr (a , z)) =
    requested-map extensionality (p a) m z
