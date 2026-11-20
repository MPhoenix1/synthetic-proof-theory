{-# OPTIONS --safe --without-K --two-level #-}

module SPT.TwoLevel.Mahlo.Displayed where

-- Strict-Display-Mahlo specifies base codes at each ambient operator and
-- fiber codes over them at each fiber operator. Its nine decoding laws
-- identify entire pairs of base and fiber functions in their dependent
-- contexts. The fibers of sums, products, trees and identities are the
-- existing glued formers. The projection ambient gives Strict-Mahlo for
-- the base codes. The record is a hypothesis, with no inhabitant here.

open import Agda.Primitive using (SSet)
open import SPT.Base
open import SPT.Foundation.Spaces using (Fiber)
open import SPT.Foundation.Spaces.Vertical using (family-displayed-space)
open import SPT.TwoLevel.Coherence using (_≐_; apˢ)
import SPT.Incidence.Displayed.Glued as Glued
open import SPT.Mahlo.Specification using (Family; Decode; map; Formers)
import SPT.Mahlo.Ambient as Ambient
open import SPT.TwoLevel.Mahlo using (Strict-Mahlo)

------------------------------------------------------------------------
-- Fibers and fiber operators

module _ {ℓ : Level} where

  -- Over a family of sets: a family over its index and, over a point of
  -- the index and a point of that family, a family over the member.
  Fibers : Family (λ (A : Set ℓ) → A) → Set (lsuc ℓ)
  Fibers F =
    Σ (pr₁ F → Set ℓ) (λ P → (a : pr₁ F) → P a → pr₂ F a → Set ℓ)

  -- The fiber part of an operator, over its base part.
  Fiber-Operator : Ambient.Operator ℓ → Set (lsuc ℓ)
  Fiber-Operator Ψ =
    (F : Family (λ (A : Set ℓ) → A)) → Fibers F → Fibers (Ψ F)

------------------------------------------------------------------------
-- Fiber codes over a family of codes, and the fibers they name

module _ {ℓ : Level} {R : Set ℓ} (j : R → Set ℓ) (S : R → Set ℓ)
  (k : (r : R) → S r → j r → Set ℓ) where

  -- A fiber code over the family's code and, over each point and fiber
  -- point, a fiber code over the branch.
  Code-Fibers : Family (Decode (λ (A : Set ℓ) → A) j) → Set ℓ
  Code-Fibers F =
    Σ (S (pr₁ F)) (λ s → (a : j (pr₁ F)) → k (pr₁ F) s a → S (pr₂ F a))

  map-fibers : (F : Family (Decode (λ (A : Set ℓ) → A) j)) → Code-Fibers F →
    Fibers (map (λ (A : Set ℓ) → A) j F)
  map-fibers F G = k (pr₁ F) (pr₁ G) , λ a y → k (pr₂ F a) (pr₂ G a y)

------------------------------------------------------------------------
-- The shapes of the decoding laws

-- A function of the base arguments X into sets with, over it, a function
-- of the fiber arguments Y into families over those sets.
Split : {ι ι′ : Level} (ℓ : Level) (X : Set ι) → (X → Set ι′) →
  Set (ι ⊔ ι′ ⊔ lsuc ℓ)
Split ℓ X Y = Σ (X → Set ℓ) (λ f → (x : X) → Y x → f x → Set ℓ)

-- The same into families of sets, with fibers over them.
Split-Family : {ι ι′ : Level} (ℓ : Level) (X : Set ι) → (X → Set ι′) →
  Set (ι ⊔ ι′ ⊔ lsuc ℓ)
Split-Family ℓ X Y =
  Σ (X → Family (λ (A : Set ℓ) → A)) (λ f → (x : X) → Y x → Fibers (f x))

module _ {ℓ : Level} (carrier : Ambient.Operator ℓ → Set ℓ)
  (interpret : (Ψ : Ambient.Operator ℓ) → carrier Ψ → Set ℓ)
  where

  -- An operator with a family of its codes.
  Family-Context : Set (lsuc ℓ)
  Family-Context = Σ (Ambient.Operator ℓ)
    (λ Ψ → Family (Decode (λ (A : Set ℓ) → A) (interpret Ψ)))

  -- An operator with a code and two points of the set it names.
  Point-Context : Set (lsuc ℓ)
  Point-Context = Σ (Ambient.Operator ℓ)
    (λ Ψ → Σ (carrier Ψ) (λ a → interpret Ψ a × interpret Ψ a))

module _ {ℓ : Level} (carrier : Ambient.Operator ℓ → Set ℓ)
  (interpret : (Ψ : Ambient.Operator ℓ) → carrier Ψ → Set ℓ)
  (fibers : (Ψ : Ambient.Operator ℓ) → Fiber-Operator Ψ → carrier Ψ →
    Set ℓ)
  (read : (Ψ : Ambient.Operator ℓ) (Φ : Fiber-Operator Ψ) (r : carrier Ψ) →
    fibers Ψ Φ r → interpret Ψ r → Set ℓ)
  where

  -- Over an operator and a family of its codes: a fiber part with fiber
  -- codes over the family.
  Family-Fiber-Context : Family-Context carrier interpret → Set (lsuc ℓ)
  Family-Fiber-Context z = Σ (Fiber-Operator (pr₁ z))
    (λ Φ → Code-Fibers (interpret (pr₁ z)) (fibers (pr₁ z) Φ)
      (read (pr₁ z) Φ) (pr₂ z))

  -- Over an operator, a code and two points: a fiber part, a fiber code,
  -- and fiber points over the two points.
  Point-Fiber-Context : Point-Context carrier interpret → Set (lsuc ℓ)
  Point-Fiber-Context z = Σ (Fiber-Operator (pr₁ z))
    (λ Φ → Σ (fibers (pr₁ z) Φ (pr₁ (pr₂ z)))
      (λ a₁ → read (pr₁ z) Φ (pr₁ (pr₂ z)) a₁ (pr₁ (pr₂ (pr₂ z)))
        × read (pr₁ z) Φ (pr₁ (pr₂ z)) a₁ (pr₂ (pr₂ (pr₂ z)))))

------------------------------------------------------------------------
-- The Mahlo rule of the universe of displays, with strict laws in context

record Strict-Display-Mahlo (ℓ : Level) : SSet (lsuc ℓ) where
  field
    -- At an operator: base codes and their reading, from its base part.
    carrier : Ambient.Operator ℓ → Set ℓ
    interpret : (Ψ : Ambient.Operator ℓ) → carrier Ψ → Set ℓ

    -- Over each base code: fiber codes and their reading.
    fibers : (Ψ : Ambient.Operator ℓ) → Fiber-Operator Ψ → carrier Ψ →
      Set ℓ
    read : (Ψ : Ambient.Operator ℓ) (Φ : Fiber-Operator Ψ)
      (r : carrier Ψ) → fibers Ψ Φ r → interpret Ψ r → Set ℓ

    -- Base codes of the formers, and the operator's value on a family.
    empty unit two natural : (Ψ : Ambient.Operator ℓ) → carrier Ψ
    product sum tree : (Ψ : Ambient.Operator ℓ) →
      Family (Decode (λ (A : Set ℓ) → A) (interpret Ψ)) → carrier Ψ
    identity : (Ψ : Ambient.Operator ℓ) (a : carrier Ψ) →
      interpret Ψ a → interpret Ψ a → carrier Ψ
    inner : (Ψ : Ambient.Operator ℓ) →
      Family (Decode (λ (A : Set ℓ) → A) (interpret Ψ)) →
      Family (Decode (λ (A : Set ℓ) → A) (interpret Ψ))

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
    identity-fiber : (Ψ : Ambient.Operator ℓ) (Φ : Fiber-Operator Ψ)
      (a : carrier Ψ) (a₁ : fibers Ψ Φ a) (x y : interpret Ψ a) →
      read Ψ Φ a a₁ x → read Ψ Φ a a₁ y → fibers Ψ Φ (identity Ψ a x y)
    inner-fiber : (Ψ : Ambient.Operator ℓ) (Φ : Fiber-Operator Ψ)
      (F : Family (Decode (λ (A : Set ℓ) → A) (interpret Ψ))) →
      Code-Fibers (interpret Ψ) (fibers Ψ Φ) (read Ψ Φ) F →
      Code-Fibers (interpret Ψ) (fibers Ψ Φ) (read Ψ Φ) (inner Ψ F)

    -- The decoding laws, each a strict equality of a base function with a
    -- fiber function over it.
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
    inner-β : _≐_ {A = Split-Family ℓ (Family-Context carrier interpret)
        (Family-Fiber-Context carrier interpret fibers read)}
      ((λ z → map (λ (A : Set ℓ) → A) (interpret (pr₁ z))
          (inner (pr₁ z) (pr₂ z))) ,
        (λ z y → map-fibers (interpret (pr₁ z)) (fibers (pr₁ z) (pr₁ y))
          (read (pr₁ z) (pr₁ y)) (inner (pr₁ z) (pr₂ z))
          (inner-fiber (pr₁ z) (pr₁ y) (pr₂ z) (pr₂ y))))
      ((λ z → pr₁ z (map (λ (A : Set ℓ) → A) (interpret (pr₁ z)) (pr₂ z))) ,
        (λ z y → pr₁ y (map (λ (A : Set ℓ) → A) (interpret (pr₁ z)) (pr₂ z))
          (map-fibers (interpret (pr₁ z)) (fibers (pr₁ z) (pr₁ y))
            (read (pr₁ z) (pr₁ y)) (pr₂ z) (pr₂ y))))

------------------------------------------------------------------------
-- Its base half is the standard model's hypothesis

module _ {ℓ : Level} (M : Strict-Display-Mahlo ℓ)
  (let open Strict-Display-Mahlo M using
         (carrier; interpret; empty; unit; two; natural; product; sum;
          tree; identity; inner; empty-β; unit-β; two-β; natural-β;
          product-β; sum-β; tree-β; identity-β; inner-β)) where

  ambient : Strict-Mahlo (Ambient.formers ℓ)
  ambient = record
    { carrier = carrier
    ; interpret = interpret
    ; empty = empty
    ; unit = unit
    ; two = two
    ; natural = natural
    ; product = product
    ; sum = sum
    ; tree = tree
    ; identity = identity
    ; inner = inner
    ; empty-β = apˢ pr₁ empty-β
    ; unit-β = apˢ pr₁ unit-β
    ; two-β = apˢ pr₁ two-β
    ; natural-β = apˢ pr₁ natural-β
    ; product-β = apˢ (λ h Ψ F → pr₁ h (Ψ , F)) product-β
    ; sum-β = apˢ (λ h Ψ F → pr₁ h (Ψ , F)) sum-β
    ; tree-β = apˢ (λ h Ψ F → pr₁ h (Ψ , F)) tree-β
    ; identity-β = apˢ (λ h Ψ a x y → pr₁ h (Ψ , a , x , y)) identity-β
    ; inner-β = apˢ (λ h Ψ F → pr₁ h (Ψ , F)) inner-β
    }
