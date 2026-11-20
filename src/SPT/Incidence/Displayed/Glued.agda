{-# OPTIONS --safe --without-K #-}

module SPT.Incidence.Displayed.Glued where

-- Glued formers for displayed spaces. A Family has a base family and a
-- fiber family depending on both a base point and its fiber point.
-- The formers sigma, pi, identity, and tree act on these two components;
-- a Decoration gives the dependent fiber of a base tree. Split maps
-- reindex families, and identity-closed identifies the identity former
-- with the closed identity family at a pair of points. Over trivial
-- fibers, canonical-decoration is unique under function extensionality
-- for every dependent function family at the given level.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Spaces using (DΣ; Base; Fiber; Total; unit-space)
open import SPT.Foundation.Spaces.Maps using (Split-Map; on-base; on-fiber)
open import SPT.Foundation.Spaces.Vertical using (family-displayed-space)
open import SPT.Foundation.Tree.W using (W; sup)

------------------------------------------------------------------------
-- Families of displayed spaces

record Family {ℓ : Level} (X : DΣ ℓ ℓ) : Set (lsuc ℓ) where
  constructor family
  field
    base : Base X → Set ℓ
    fiber : (b : Base X) → Fiber X b → base b → Set ℓ

open Family public

module _ {ℓ : Level} where

  constant : (X Y : DΣ ℓ ℓ) → Family X
  constant X Y = family (const (Base Y)) (λ _ _ → Fiber Y)

------------------------------------------------------------------------
-- Glued sums, products, identities, and trees

module _ {ℓ : Level} where

  sigma pi : (X : DΣ ℓ ℓ) → Family X → DΣ ℓ ℓ
  sigma X D = family-displayed-space (Σ (Base X) (base D))
    (λ p → Σ (Fiber X (pr₁ p))
      (λ x → fiber D (pr₁ p) x (pr₂ p)))
  pi X D = family-displayed-space ((b : Base X) → base D b)
    (λ g → (b : Base X) (x : Fiber X b) → fiber D b x (g b))

  identity : (X : DΣ ℓ ℓ) → Total X → Total X → DΣ ℓ ℓ
  identity X x y = family-displayed-space (pr₁ x ＝ pr₁ y)
    (λ p → transport (Fiber X) p (pr₂ x) ＝ pr₂ y)

  -- Each base node carries its fiber point, and each branch carries a
  -- decoration for every inhabitant of the corresponding fiber family.

  data Decoration (X : DΣ ℓ ℓ) (D : Family X) :
    W (Base X) (base D) → Set ℓ where
    node : (b : Base X) (k : base D b → W (Base X) (base D)) →
      (x : Fiber X b) →
      ((d : base D b) → fiber D b x d → Decoration X D (k d)) →
      Decoration X D (sup b k)

  tree : (X : DΣ ℓ ℓ) → Family X → DΣ ℓ ℓ
  tree X D = family-displayed-space
    (W (Base X) (base D)) (Decoration X D)

------------------------------------------------------------------------
-- Reindexing and closed families

module _ {ℓ : Level} where

  reindex : (X Y : DΣ ℓ ℓ) → Split-Map X Y → Family Y → Family X
  reindex X Y m D = family (λ b → base D (on-base m b))
    (λ b x → fiber D (on-base m b) (on-fiber m b x))

  identity-family : (X : DΣ ℓ ℓ) → Family (sigma X (constant X X))
  identity-family X = family (λ p → pr₁ p ＝ pr₂ p)
    (λ p q e → transport (Fiber X) e (pr₁ q) ＝ pr₂ q)

  point : (X : DΣ ℓ ℓ) → Total X → Split-Map (unit-space ℓ) X
  point X x = record
    { on-base = const (pr₁ x)
    ; on-fiber = λ _ _ → pr₂ x
    }

  closed : Family (unit-space ℓ) → DΣ ℓ ℓ
  closed D = family-displayed-space
    (base D (lift ⋆)) (fiber D (lift ⋆) (lift ⋆))

  abstract
    identity-closed : (X : DΣ ℓ ℓ) (x y : Total X) →
      identity X x y ＝
        closed (reindex (unit-space ℓ) (sigma X (constant X X))
          (point (sigma X (constant X X))
            ((pr₁ x , pr₁ y) , (pr₂ x , pr₂ y))) (identity-family X))
    identity-closed X x y = refl

------------------------------------------------------------------------
-- Canonical decorations over trivial fibers

module _ {ℓ : Level} where

  shape-family : (X : DΣ ℓ ℓ) → Family X →
    Family (family-displayed-space (Base X) (const (Lift ℓ 𝟙)))
  shape-family X D = family (base D) (λ _ _ _ → Lift ℓ 𝟙)

  canonical-decoration : (X : DΣ ℓ ℓ) (D : Family X)
    (w : W (Base X) (base D)) →
    Decoration (family-displayed-space (Base X) (const (Lift ℓ 𝟙)))
      (shape-family X D) w
  canonical-decoration X D (sup b k) =
    node b k (lift ⋆) (λ d → const (canonical-decoration X D (k d)))

  -- The hypothesis ranges over every dependent function family at ℓ.
  abstract
    canonical-decoration-is-unique :
      ((A : Set ℓ) (B : A → Set ℓ) → FunExt A B) →
      (X : DΣ ℓ ℓ) (D : Family X) (w : W (Base X) (base D))
      (e : Decoration
        (family-displayed-space (Base X) (const (Lift ℓ 𝟙)))
        (shape-family X D) w) →
      canonical-decoration X D w ＝ e
    canonical-decoration-is-unique ext X D (sup b k) (node .b .k x h) =
      ap (node b k x)
        (ext (base D b)
          (λ d → Lift ℓ 𝟙 →
            Decoration
              (family-displayed-space (Base X) (const (Lift ℓ 𝟙)))
              (shape-family X D) (k d))
          (λ d → const (canonical-decoration X D (k d))) h
          (λ d → ext (Lift ℓ 𝟙)
            (const (Decoration
              (family-displayed-space (Base X) (const (Lift ℓ 𝟙)))
              (shape-family X D) (k d)))
            (const (canonical-decoration X D (k d))) (h d)
            (λ e → canonical-decoration-is-unique ext X D (k d) (h d e))))
