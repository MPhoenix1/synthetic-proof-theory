{-# OPTIONS --safe --without-K --two-level #-}

module SPT.TwoLevel.Mahlo.Displayed.StepAlgebra where

-- Labelled-Display specifies codes for each former and for an operator's
-- result and branches, with fiber codes over them. The branch law uses
-- Branch-Context and Branch-Fiber-Context; fiber-along carries a dependent
-- fiber point along the strict result law. Pairing results with branches
-- gives inner and inner-fiber, whose inner-law constructs the inhabitant
-- strict-display-mahlo of Strict-Display-Mahlo.

open import Agda.Primitive using (SSet)
open import SPT.Base
open import SPT.Foundation.Spaces using (Fiber)
open import SPT.Foundation.Spaces.Vertical using (family-displayed-space)
open import SPT.TwoLevel.Coherence using
  (_≐_; same; transportˢ)
import SPT.Incidence.Displayed.Glued as Glued
open import SPT.Mahlo.Specification using (Family; Decode; map; Formers)
import SPT.Mahlo.Ambient as Ambient
open import SPT.TwoLevel.Mahlo.Displayed using
  (Fiber-Operator; Code-Fibers; map-fibers; Split; Split-Family;
   Family-Context; Family-Fiber-Context; Point-Context; Point-Fiber-Context;
   Strict-Display-Mahlo)

------------------------------------------------------------------------
-- The contexts of the branch law

-- An operator, a family of its codes and a point of the index of Ψ's value
-- there; over it, a fiber part, fiber codes over the family and a point of
-- the fiber part's value over that point.

module _ {ℓ : Level} (carrier : Ambient.Operator ℓ → Set ℓ)
  (interpret : (Ψ : Ambient.Operator ℓ) → carrier Ψ → Set ℓ)
  where

  Branch-Context : Set (lsuc ℓ)
  Branch-Context =
    Σ (Family-Context carrier interpret)
      (λ z → pr₁ (pr₁ z (map (λ (A : Set ℓ) → A) (interpret (pr₁ z)) (pr₂ z))))

module _ {ℓ : Level} (carrier : Ambient.Operator ℓ → Set ℓ)
  (interpret : (Ψ : Ambient.Operator ℓ) → carrier Ψ → Set ℓ)
  (fibers : (Ψ : Ambient.Operator ℓ) → Fiber-Operator Ψ → carrier Ψ →
    Set ℓ)
  (read : (Ψ : Ambient.Operator ℓ) (Φ : Fiber-Operator Ψ) (r : carrier Ψ) →
    fibers Ψ Φ r → interpret Ψ r → Set ℓ)
  where

  Branch-Fiber-Context : Branch-Context carrier interpret → Set (lsuc ℓ)
  Branch-Fiber-Context c =
    Σ (Family-Fiber-Context carrier interpret fibers read (pr₁ c))
      (λ u →
        pr₁
          (pr₁ u
            (map (λ (A : Set ℓ) → A) (interpret (pr₁ (pr₁ c)))
              (pr₂ (pr₁ c)))
            (map-fibers (interpret (pr₁ (pr₁ c))) (fibers (pr₁ (pr₁ c)) (pr₁ u))
              (read (pr₁ (pr₁ c)) (pr₁ u)) (pr₂ (pr₁ c)) (pr₂ u)))
          (pr₂ c))

------------------------------------------------------------------------
-- Moving points along a law

-- A strict identification of two base functions with fiber functions over
-- them moves a point of a base value, and a fiber point over it.

module _ {ι ι′ : Level} (ℓ : Level) (X : Set ι) (Y : X → Set ι′) where

  fiber-along :
    {s t : Split ℓ X Y} (e : s ≐ t) (x : X) (y : Y x) (a : pr₁ s x)
    → pr₂ s x y a → pr₂ t x y
        (transportˢ (λ (u : Split ℓ X Y) → pr₁ u x) e a)
  fiber-along same x y a w = w

------------------------------------------------------------------------
-- Labelled display algebras

-- θ_Q at each summand of the fiber step over θ_R at the base summand, and
-- the label law k ∘ θ_Q = k_H with i ∘ θ_R = d_H at each summand, base and
-- fiber together, in context. The laws of the formers are those of
-- Strict-Display-Mahlo; the result and branch laws replace `inner-β`.

record Labelled-Display (ℓ : Level) : SSet (lsuc ℓ) where
  field
    carrier : Ambient.Operator ℓ → Set ℓ
    interpret : (Ψ : Ambient.Operator ℓ) → carrier Ψ → Set ℓ
    fibers : (Ψ : Ambient.Operator ℓ) → Fiber-Operator Ψ → carrier Ψ →
      Set ℓ
    read : (Ψ : Ambient.Operator ℓ) (Φ : Fiber-Operator Ψ)
      (r : carrier Ψ) → fibers Ψ Φ r → interpret Ψ r → Set ℓ

    -- Base codes of the formers, Ψ's result and Ψ's branches.
    empty unit two natural : (Ψ : Ambient.Operator ℓ) → carrier Ψ
    product sum tree result : (Ψ : Ambient.Operator ℓ) →
      Family (Decode (λ (A : Set ℓ) → A) (interpret Ψ)) → carrier Ψ
    identity : (Ψ : Ambient.Operator ℓ) (a : carrier Ψ) →
      interpret Ψ a → interpret Ψ a → carrier Ψ
    branch : (Ψ : Ambient.Operator ℓ)
      (F : Family (Decode (λ (A : Set ℓ) → A) (interpret Ψ))) →
      pr₁ (Ψ (map (λ (A : Set ℓ) → A) (interpret Ψ) F)) → carrier Ψ

    -- Fiber codes over them.
    empty-fiber : (Ψ : Ambient.Operator ℓ) (Φ : Fiber-Operator Ψ) →
      fibers Ψ Φ (empty Ψ)
    unit-fiber : (Ψ : Ambient.Operator ℓ) (Φ : Fiber-Operator Ψ) →
      fibers Ψ Φ (unit Ψ)
    two-fiber : (Ψ : Ambient.Operator ℓ) (Φ : Fiber-Operator Ψ) →
      fibers Ψ Φ (two Ψ)
    natural-fiber : (Ψ : Ambient.Operator ℓ) (Φ : Fiber-Operator Ψ) →
      fibers Ψ Φ (natural Ψ)
    product-fiber : (Ψ : Ambient.Operator ℓ) (Φ : Fiber-Operator Ψ)
      (F : Family (Decode (λ (A : Set ℓ) → A) (interpret Ψ))) →
      Code-Fibers (interpret Ψ) (fibers Ψ Φ) (read Ψ Φ) F →
      fibers Ψ Φ (product Ψ F)
    sum-fiber : (Ψ : Ambient.Operator ℓ) (Φ : Fiber-Operator Ψ)
      (F : Family (Decode (λ (A : Set ℓ) → A) (interpret Ψ))) →
      Code-Fibers (interpret Ψ) (fibers Ψ Φ) (read Ψ Φ) F →
      fibers Ψ Φ (sum Ψ F)
    tree-fiber : (Ψ : Ambient.Operator ℓ) (Φ : Fiber-Operator Ψ)
      (F : Family (Decode (λ (A : Set ℓ) → A) (interpret Ψ))) →
      Code-Fibers (interpret Ψ) (fibers Ψ Φ) (read Ψ Φ) F →
      fibers Ψ Φ (tree Ψ F)
    result-fiber : (Ψ : Ambient.Operator ℓ) (Φ : Fiber-Operator Ψ)
      (F : Family (Decode (λ (A : Set ℓ) → A) (interpret Ψ))) →
      Code-Fibers (interpret Ψ) (fibers Ψ Φ) (read Ψ Φ) F →
      fibers Ψ Φ (result Ψ F)
    identity-fiber : (Ψ : Ambient.Operator ℓ) (Φ : Fiber-Operator Ψ)
      (a : carrier Ψ) (a₁ : fibers Ψ Φ a) (x y : interpret Ψ a) →
      read Ψ Φ a a₁ x → read Ψ Φ a a₁ y → fibers Ψ Φ (identity Ψ a x y)
    branch-fiber : (Ψ : Ambient.Operator ℓ) (Φ : Fiber-Operator Ψ)
      (F : Family (Decode (λ (A : Set ℓ) → A) (interpret Ψ)))
      (G : Code-Fibers (interpret Ψ) (fibers Ψ Φ) (read Ψ Φ) F)
      (y : pr₁ (Ψ (map (λ (A : Set ℓ) → A) (interpret Ψ) F))) →
      pr₁
        (Φ (map (λ (A : Set ℓ) → A) (interpret Ψ) F)
          (map-fibers (interpret Ψ) (fibers Ψ Φ) (read Ψ Φ) F G))
        y →
      fibers Ψ Φ (branch Ψ F y)

    -- The label laws, each a base function with a fiber function over it.
    empty-β : _≐_ {A = Split ℓ (Ambient.Operator ℓ) Fiber-Operator}
      ((λ Ψ → interpret Ψ (empty Ψ)) ,
        (λ Ψ Φ → read Ψ Φ (empty Ψ) (empty-fiber Ψ Φ)))
      ((λ Ψ → Formers.empty (Ambient.formers ℓ)) ,
        (λ Ψ Φ _ → Lift ℓ 𝟙))
    unit-β : _≐_ {A = Split ℓ (Ambient.Operator ℓ) Fiber-Operator}
      ((λ Ψ → interpret Ψ (unit Ψ)) ,
        (λ Ψ Φ → read Ψ Φ (unit Ψ) (unit-fiber Ψ Φ)))
      ((λ Ψ → Formers.unit (Ambient.formers ℓ)) ,
        (λ Ψ Φ _ → Lift ℓ 𝟙))
    two-β : _≐_ {A = Split ℓ (Ambient.Operator ℓ) Fiber-Operator}
      ((λ Ψ → interpret Ψ (two Ψ)) ,
        (λ Ψ Φ → read Ψ Φ (two Ψ) (two-fiber Ψ Φ)))
      ((λ Ψ → Formers.two (Ambient.formers ℓ)) ,
        (λ Ψ Φ _ → Lift ℓ 𝟙))
    natural-β : _≐_ {A = Split ℓ (Ambient.Operator ℓ) Fiber-Operator}
      ((λ Ψ → interpret Ψ (natural Ψ)) ,
        (λ Ψ Φ → read Ψ Φ (natural Ψ) (natural-fiber Ψ Φ)))
      ((λ Ψ → Formers.natural (Ambient.formers ℓ)) ,
        (λ Ψ Φ _ → Lift ℓ 𝟙))
    product-β : _≐_ {A = Split ℓ (Family-Context carrier interpret)
        (Family-Fiber-Context carrier interpret fibers read)}
      ((λ z → interpret (pr₁ z) (product (pr₁ z) (pr₂ z))) ,
        (λ z y → read (pr₁ z) (pr₁ y) (product (pr₁ z) (pr₂ z))
          (product-fiber (pr₁ z) (pr₁ y) (pr₂ z) (pr₂ y))))
      ((λ z → Formers.product (Ambient.formers ℓ)
          (map (λ (A : Set ℓ) → A) (interpret (pr₁ z)) (pr₂ z))) ,
        (λ z y →
          let F = map (λ (A : Set ℓ) → A) (interpret (pr₁ z)) (pr₂ z)
              G = map-fibers (interpret (pr₁ z)) (fibers (pr₁ z) (pr₁ y))
                (read (pr₁ z) (pr₁ y)) (pr₂ z) (pr₂ y)
          in Fiber (Glued.pi
               (family-displayed-space (pr₁ F) (pr₁ G))
               (Glued.family (pr₂ F) (pr₂ G)))))
    sum-β : _≐_ {A = Split ℓ (Family-Context carrier interpret)
        (Family-Fiber-Context carrier interpret fibers read)}
      ((λ z → interpret (pr₁ z) (sum (pr₁ z) (pr₂ z))) ,
        (λ z y → read (pr₁ z) (pr₁ y) (sum (pr₁ z) (pr₂ z))
          (sum-fiber (pr₁ z) (pr₁ y) (pr₂ z) (pr₂ y))))
      ((λ z → Formers.sum (Ambient.formers ℓ)
          (map (λ (A : Set ℓ) → A) (interpret (pr₁ z)) (pr₂ z))) ,
        (λ z y →
          let F = map (λ (A : Set ℓ) → A) (interpret (pr₁ z)) (pr₂ z)
              G = map-fibers (interpret (pr₁ z)) (fibers (pr₁ z) (pr₁ y))
                (read (pr₁ z) (pr₁ y)) (pr₂ z) (pr₂ y)
          in Fiber (Glued.sigma
               (family-displayed-space (pr₁ F) (pr₁ G))
               (Glued.family (pr₂ F) (pr₂ G)))))
    tree-β : _≐_ {A = Split ℓ (Family-Context carrier interpret)
        (Family-Fiber-Context carrier interpret fibers read)}
      ((λ z → interpret (pr₁ z) (tree (pr₁ z) (pr₂ z))) ,
        (λ z y → read (pr₁ z) (pr₁ y) (tree (pr₁ z) (pr₂ z))
          (tree-fiber (pr₁ z) (pr₁ y) (pr₂ z) (pr₂ y))))
      ((λ z → Formers.tree (Ambient.formers ℓ)
          (map (λ (A : Set ℓ) → A) (interpret (pr₁ z)) (pr₂ z))) ,
        (λ z y →
          let F = map (λ (A : Set ℓ) → A) (interpret (pr₁ z)) (pr₂ z)
              G = map-fibers (interpret (pr₁ z)) (fibers (pr₁ z) (pr₁ y))
                (read (pr₁ z) (pr₁ y)) (pr₂ z) (pr₂ y)
          in Fiber (Glued.tree
               (family-displayed-space (pr₁ F) (pr₁ G))
               (Glued.family (pr₂ F) (pr₂ G)))))
    identity-β : _≐_ {A = Split ℓ (Point-Context carrier interpret)
        (Point-Fiber-Context carrier interpret fibers read)}
      ((λ z → interpret (pr₁ z) (identity (pr₁ z) (pr₁ (pr₂ z))
          (pr₁ (pr₂ (pr₂ z))) (pr₂ (pr₂ (pr₂ z))))) ,
        (λ z y → read (pr₁ z) (pr₁ y) (identity (pr₁ z) (pr₁ (pr₂ z))
            (pr₁ (pr₂ (pr₂ z))) (pr₂ (pr₂ (pr₂ z))))
          (identity-fiber (pr₁ z) (pr₁ y) (pr₁ (pr₂ z)) (pr₁ (pr₂ y))
            (pr₁ (pr₂ (pr₂ z))) (pr₂ (pr₂ (pr₂ z)))
            (pr₁ (pr₂ (pr₂ y))) (pr₂ (pr₂ (pr₂ y))))))
      ((λ z → Formers.identity (Ambient.formers ℓ)
          (interpret (pr₁ z) (pr₁ (pr₂ z)))
          (pr₁ (pr₂ (pr₂ z))) (pr₂ (pr₂ (pr₂ z)))) ,
        (λ z y → Fiber (Glued.identity
          (family-displayed-space (interpret (pr₁ z) (pr₁ (pr₂ z)))
            (read (pr₁ z) (pr₁ y) (pr₁ (pr₂ z)) (pr₁ (pr₂ y))))
          (pr₁ (pr₂ (pr₂ z)) , pr₁ (pr₂ (pr₂ y)))
          (pr₂ (pr₂ (pr₂ z)) , pr₂ (pr₂ (pr₂ y))))))
    result-β : _≐_ {A = Split ℓ (Family-Context carrier interpret)
        (Family-Fiber-Context carrier interpret fibers read)}
      ((λ z → interpret (pr₁ z) (result (pr₁ z) (pr₂ z))) ,
        (λ z y → read (pr₁ z) (pr₁ y) (result (pr₁ z) (pr₂ z))
          (result-fiber (pr₁ z) (pr₁ y) (pr₂ z) (pr₂ y))))
      ((λ z → pr₁ (pr₁ z
          (map (λ (A : Set ℓ) → A) (interpret (pr₁ z)) (pr₂ z)))) ,
        (λ z y → pr₁ (pr₁ y
          (map (λ (A : Set ℓ) → A) (interpret (pr₁ z)) (pr₂ z))
          (map-fibers (interpret (pr₁ z)) (fibers (pr₁ z) (pr₁ y))
            (read (pr₁ z) (pr₁ y)) (pr₂ z) (pr₂ y)))))
    branch-β : _≐_ {A = Split ℓ (Branch-Context carrier interpret)
        (Branch-Fiber-Context carrier interpret fibers read)}
      ((λ c → interpret (pr₁ (pr₁ c))
          (branch (pr₁ (pr₁ c)) (pr₂ (pr₁ c)) (pr₂ c))) ,
        (λ c d → read (pr₁ (pr₁ c)) (pr₁ (pr₁ d))
          (branch (pr₁ (pr₁ c)) (pr₂ (pr₁ c)) (pr₂ c))
          (branch-fiber (pr₁ (pr₁ c)) (pr₁ (pr₁ d)) (pr₂ (pr₁ c))
            (pr₂ (pr₁ d)) (pr₂ c) (pr₂ d))))
      ((λ c → pr₂ (pr₁ (pr₁ c)
          (map (λ (A : Set ℓ) → A) (interpret (pr₁ (pr₁ c)))
            (pr₂ (pr₁ c))))
          (pr₂ c)) ,
        (λ c d → pr₂ (pr₁ (pr₁ d)
          (map (λ (A : Set ℓ) → A) (interpret (pr₁ (pr₁ c)))
            (pr₂ (pr₁ c)))
          (map-fibers (interpret (pr₁ (pr₁ c)))
            (fibers (pr₁ (pr₁ c)) (pr₁ (pr₁ d)))
            (read (pr₁ (pr₁ c)) (pr₁ (pr₁ d))) (pr₂ (pr₁ c))
            (pr₂ (pr₁ d))))
          (pr₂ c) (pr₂ d)))

------------------------------------------------------------------------
-- The display hypothesis

-- `inner` pairs Ψ's result with its branches at the points of the result's
-- decoding moved along its law; `inner-fiber` pairs Φ's result fiber code
-- with its branch fiber codes at the fiber points moved along it. At the
-- two laws the pair is Ψ's value with Φ's fiber value, up to η: the
-- complete inner law in the dependent pair of families.

module _ {ℓ : Level} (M : Labelled-Display ℓ)
  (let open Labelled-Display M using
         (carrier; interpret; fibers; read; empty; unit; two; natural;
          product; sum; tree; result; identity; branch; empty-fiber;
          unit-fiber; two-fiber; natural-fiber; product-fiber; sum-fiber;
          tree-fiber; result-fiber; identity-fiber; branch-fiber;
          empty-β; unit-β; two-β; natural-β; product-β; sum-β; tree-β;
          identity-β; result-β; branch-β)) where

  inner :
    (Ψ : Ambient.Operator ℓ)
    → Family (Decode (λ (A : Set ℓ) → A) (interpret Ψ))
    → Family (Decode (λ (A : Set ℓ) → A) (interpret Ψ))
  inner Ψ F =
    result Ψ F ,
    (λ x →
      branch Ψ F
        (transportˢ
          (λ (u : Split ℓ (Family-Context carrier interpret)
              (Family-Fiber-Context carrier interpret fibers read)) →
            pr₁ u (Ψ , F)) result-β x))

  inner-fiber :
    (Ψ : Ambient.Operator ℓ) (Φ : Fiber-Operator Ψ)
    (F : Family (Decode (λ (A : Set ℓ) → A) (interpret Ψ)))
    → Code-Fibers (interpret Ψ) (fibers Ψ Φ) (read Ψ Φ) F
    → Code-Fibers (interpret Ψ) (fibers Ψ Φ) (read Ψ Φ) (inner Ψ F)
  inner-fiber Ψ Φ F G =
    result-fiber Ψ Φ F G ,
    (λ a w →
      branch-fiber Ψ Φ F G
        (transportˢ
          (λ (u : Split ℓ (Family-Context carrier interpret)
              (Family-Fiber-Context carrier interpret fibers read)) →
            pr₁ u (Ψ , F)) result-β a)
        (fiber-along ℓ (Family-Context carrier interpret)
          (Family-Fiber-Context carrier interpret fibers read) result-β
          (Ψ , F) (Φ , G) a w))

  inner-law :
    (r : Split ℓ (Family-Context carrier interpret)
      (Family-Fiber-Context carrier interpret fibers read))
    (b : Split ℓ (Branch-Context carrier interpret)
      (Branch-Fiber-Context carrier interpret fibers read))
    (e : r ≐
      ((λ z → pr₁ (pr₁ z
          (map (λ (A : Set ℓ) → A) (interpret (pr₁ z)) (pr₂ z)))) ,
        (λ z y → pr₁ (pr₁ y
          (map (λ (A : Set ℓ) → A) (interpret (pr₁ z)) (pr₂ z))
          (map-fibers (interpret (pr₁ z)) (fibers (pr₁ z) (pr₁ y))
            (read (pr₁ z) (pr₁ y)) (pr₂ z) (pr₂ y))))))
    → b ≐
      ((λ c → pr₂ (pr₁ (pr₁ c)
          (map (λ (A : Set ℓ) → A) (interpret (pr₁ (pr₁ c)))
            (pr₂ (pr₁ c))))
          (pr₂ c)) ,
        (λ c d → pr₂ (pr₁ (pr₁ d)
          (map (λ (A : Set ℓ) → A) (interpret (pr₁ (pr₁ c)))
            (pr₂ (pr₁ c)))
          (map-fibers (interpret (pr₁ (pr₁ c)))
            (fibers (pr₁ (pr₁ c)) (pr₁ (pr₁ d)))
            (read (pr₁ (pr₁ c)) (pr₁ (pr₁ d))) (pr₂ (pr₁ c))
            (pr₂ (pr₁ d))))
          (pr₂ c) (pr₂ d)))
    → _≐_ {A = Split-Family ℓ (Family-Context carrier interpret)
        (Family-Fiber-Context carrier interpret fibers read)}
      ((λ z →
          pr₁ r z ,
          (λ x →
            pr₁ b
              (z ,
                transportˢ
                  (λ (u : Split ℓ (Family-Context carrier interpret)
                      (Family-Fiber-Context carrier interpret fibers read)) →
                    pr₁ u z) e x))) ,
        (λ z y →
          pr₂ r z y ,
          (λ a w →
            pr₂ b
              (z ,
                transportˢ
                  (λ (u : Split ℓ (Family-Context carrier interpret)
                      (Family-Fiber-Context carrier interpret fibers read)) →
                    pr₁ u z) e a)
              (y ,
                fiber-along ℓ (Family-Context carrier interpret)
                  (Family-Fiber-Context carrier interpret fibers read) e
                  z y a w))))
      ((λ z → pr₁ z (map (λ (A : Set ℓ) → A) (interpret (pr₁ z)) (pr₂ z))) ,
        (λ z y → pr₁ y (map (λ (A : Set ℓ) → A) (interpret (pr₁ z)) (pr₂ z))
          (map-fibers (interpret (pr₁ z)) (fibers (pr₁ z) (pr₁ y))
            (read (pr₁ z) (pr₁ y)) (pr₂ z) (pr₂ y))))
  inner-law r b same same = same

  strict-display-mahlo : Strict-Display-Mahlo ℓ
  strict-display-mahlo = record
    { carrier = carrier
    ; interpret = interpret
    ; fibers = fibers
    ; read = read
    ; empty = empty
    ; unit = unit
    ; two = two
    ; natural = natural
    ; product = product
    ; sum = sum
    ; tree = tree
    ; identity = identity
    ; inner = inner
    ; empty-fiber = empty-fiber
    ; unit-fiber = unit-fiber
    ; two-fiber = two-fiber
    ; natural-fiber = natural-fiber
    ; product-fiber = product-fiber
    ; sum-fiber = sum-fiber
    ; tree-fiber = tree-fiber
    ; identity-fiber = identity-fiber
    ; inner-fiber = inner-fiber
    ; empty-β = empty-β
    ; unit-β = unit-β
    ; two-β = two-β
    ; natural-β = natural-β
    ; product-β = product-β
    ; sum-β = sum-β
    ; tree-β = tree-β
    ; identity-β = identity-β
    ; inner-β =
        inner-law
          ( (λ z → interpret (pr₁ z) (result (pr₁ z) (pr₂ z))) ,
            (λ z y → read (pr₁ z) (pr₁ y) (result (pr₁ z) (pr₂ z))
              (result-fiber (pr₁ z) (pr₁ y) (pr₂ z) (pr₂ y))))
          ( (λ c → interpret (pr₁ (pr₁ c))
              (branch (pr₁ (pr₁ c)) (pr₂ (pr₁ c)) (pr₂ c))) ,
            (λ c d → read (pr₁ (pr₁ c)) (pr₁ (pr₁ d))
              (branch (pr₁ (pr₁ c)) (pr₂ (pr₁ c)) (pr₂ c))
              (branch-fiber (pr₁ (pr₁ c)) (pr₁ (pr₁ d)) (pr₂ (pr₁ c))
                (pr₂ (pr₁ d)) (pr₂ c) (pr₂ d))))
          result-β branch-β
    }
