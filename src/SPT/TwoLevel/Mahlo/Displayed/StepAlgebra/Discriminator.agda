{-# OPTIONS --safe --without-K --two-level #-}

module SPT.TwoLevel.Mahlo.Displayed.StepAlgebra.Discriminator where

-- Induction–recursion gives fiber codes over each ambient step code.
-- Fiber-Code and read-fiber compute the selected fiber of each former,
-- result and branch. All ten strict laws of displays hold by same.

open import SPT.Base
open import SPT.Mahlo.Specification using (Operator)
import SPT.TwoLevel.Mahlo.StepAlgebra.Discriminator as Base
open import SPT.TwoLevel.Coherence using (same)
open import SPT.TwoLevel.Mahlo.Displayed using
  (Fiber-Operator)
open import SPT.Foundation.Spaces using (Fiber)
open import SPT.Foundation.Spaces.Vertical using (family-displayed-space)
import SPT.Incidence.Displayed.Glued as Glued
open import SPT.TwoLevel.Mahlo.Displayed.StepAlgebra using
  (Labelled-Display)

------------------------------------------------------------------------
-- The fiber codes at a fiber part

-- Over each base code of a summand, a fiber code, read as the fiber label
-- of that summand: the glued fibers of the formers, Φ's fiber family at a
-- family with fiber codes, and Φ's fiber branches.

module _ {ℓ : Level} (Ψ : Operator (λ (A : Set ℓ) → A))
  (Φ : Fiber-Operator Ψ)
  where

  data Fiber-Code : Base.Code Ψ → Set ℓ
  read-fiber : (c : Base.Code Ψ) → Fiber-Code c → Base.decode Ψ c → Set ℓ

  data Fiber-Code where
    empty-fiber : Fiber-Code Base.empty
    unit-fiber : Fiber-Code Base.unit
    two-fiber : Fiber-Code Base.two
    natural-fiber : Fiber-Code Base.natural
    product-fiber :
      (F : Σ (Base.Code Ψ) (λ a → Base.decode Ψ a → Base.Code Ψ))
      → Σ (Fiber-Code (pr₁ F))
          (λ s → (x : Base.decode Ψ (pr₁ F)) → read-fiber (pr₁ F) s x
            → Fiber-Code (pr₂ F x))
      → Fiber-Code (Base.product F)
    sum-fiber :
      (F : Σ (Base.Code Ψ) (λ a → Base.decode Ψ a → Base.Code Ψ))
      → Σ (Fiber-Code (pr₁ F))
          (λ s → (x : Base.decode Ψ (pr₁ F)) → read-fiber (pr₁ F) s x
            → Fiber-Code (pr₂ F x))
      → Fiber-Code (Base.sum F)
    tree-fiber :
      (F : Σ (Base.Code Ψ) (λ a → Base.decode Ψ a → Base.Code Ψ))
      → Σ (Fiber-Code (pr₁ F))
          (λ s → (x : Base.decode Ψ (pr₁ F)) → read-fiber (pr₁ F) s x
            → Fiber-Code (pr₂ F x))
      → Fiber-Code (Base.tree F)
    result-fiber :
      (F : Σ (Base.Code Ψ) (λ a → Base.decode Ψ a → Base.Code Ψ))
      → Σ (Fiber-Code (pr₁ F))
          (λ s → (x : Base.decode Ψ (pr₁ F)) → read-fiber (pr₁ F) s x
            → Fiber-Code (pr₂ F x))
      → Fiber-Code (Base.result F)
    identity-fiber :
      (a : Base.Code Ψ) (a₁ : Fiber-Code a) (x y : Base.decode Ψ a)
      → read-fiber a a₁ x → read-fiber a a₁ y
      → Fiber-Code (Base.identity a x y)
    branch-fiber :
      (F : Σ (Base.Code Ψ) (λ a → Base.decode Ψ a → Base.Code Ψ))
      (G : Σ (Fiber-Code (pr₁ F))
        (λ s → (x : Base.decode Ψ (pr₁ F)) → read-fiber (pr₁ F) s x
          → Fiber-Code (pr₂ F x)))
      (y : pr₁ (Ψ (Base.decode Ψ (pr₁ F) ,
        (λ x → Base.decode Ψ (pr₂ F x)))))
      → pr₁
          (Φ (Base.decode Ψ (pr₁ F) , (λ x → Base.decode Ψ (pr₂ F x)))
            (read-fiber (pr₁ F) (pr₁ G) ,
              (λ x w → read-fiber (pr₂ F x) (pr₂ G x w))))
          y
      → Fiber-Code (Base.branch F y)

  read-fiber c empty-fiber = λ x → Lift ℓ 𝟙
  read-fiber c unit-fiber = λ x → Lift ℓ 𝟙
  read-fiber c two-fiber = λ x → Lift ℓ 𝟙
  read-fiber c natural-fiber = λ x → Lift ℓ 𝟙
  read-fiber c (product-fiber (a , b) (s , t)) =
    Fiber (Glued.pi
      (family-displayed-space (Base.decode Ψ a) (read-fiber a s))
      (Glued.family (λ x → Base.decode Ψ (b x))
        (λ x w → read-fiber (b x) (t x w))))
  read-fiber c (sum-fiber (a , b) (s , t)) =
    Fiber (Glued.sigma
      (family-displayed-space (Base.decode Ψ a) (read-fiber a s))
      (Glued.family (λ x → Base.decode Ψ (b x))
        (λ x w → read-fiber (b x) (t x w))))
  read-fiber c (tree-fiber (a , b) (s , t)) =
    Fiber (Glued.tree
      (family-displayed-space (Base.decode Ψ a) (read-fiber a s))
      (Glued.family (λ x → Base.decode Ψ (b x))
        (λ x w → read-fiber (b x) (t x w))))
  read-fiber c (result-fiber (a , b) (s , t)) =
    pr₁
      (Φ (Base.decode Ψ a , (λ x → Base.decode Ψ (b x)))
        (read-fiber a s , (λ x w → read-fiber (b x) (t x w))))
  read-fiber c (identity-fiber a a₁ x y x₁ y₁) =
    Fiber (Glued.identity
      (family-displayed-space (Base.decode Ψ a) (read-fiber a a₁))
      (x , x₁) (y , y₁))
  read-fiber c (branch-fiber (a , b) (s , t) y w) =
    pr₂
      (Φ (Base.decode Ψ a , (λ x → Base.decode Ψ (b x)))
        (read-fiber a s , (λ x v → read-fiber (b x) (t x v))))
      y w

------------------------------------------------------------------------
-- The labelled display algebra, and the display hypothesis

module _ (ℓ : Level) where

  displays : Labelled-Display ℓ
  displays = record
    { carrier = Base.Code
    ; interpret = Base.decode
    ; fibers = Fiber-Code
    ; read = read-fiber
    ; empty = λ Ψ → Base.empty
    ; unit = λ Ψ → Base.unit
    ; two = λ Ψ → Base.two
    ; natural = λ Ψ → Base.natural
    ; product = λ Ψ F → Base.product F
    ; sum = λ Ψ F → Base.sum F
    ; tree = λ Ψ F → Base.tree F
    ; result = λ Ψ F → Base.result F
    ; identity = λ Ψ a x y → Base.identity a x y
    ; branch = λ Ψ F y → Base.branch F y
    ; empty-fiber = λ Ψ Φ → empty-fiber
    ; unit-fiber = λ Ψ Φ → unit-fiber
    ; two-fiber = λ Ψ Φ → two-fiber
    ; natural-fiber = λ Ψ Φ → natural-fiber
    ; product-fiber = λ Ψ Φ F G → product-fiber F G
    ; sum-fiber = λ Ψ Φ F G → sum-fiber F G
    ; tree-fiber = λ Ψ Φ F G → tree-fiber F G
    ; result-fiber = λ Ψ Φ F G → result-fiber F G
    ; identity-fiber = λ Ψ Φ a a₁ x y x₁ y₁ → identity-fiber a a₁ x y x₁ y₁
    ; branch-fiber = λ Ψ Φ F G y w → branch-fiber F G y w
    ; empty-β = same
    ; unit-β = same
    ; two-β = same
    ; natural-β = same
    ; product-β = same
    ; sum-β = same
    ; tree-β = same
    ; identity-β = same
    ; result-β = same
    ; branch-β = same
    }
