{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Heights.Hartogs where

-- The Hartogs height of a closure, and its regularity under unique names.
-- The Hartogs height is the fan of the heights of the code-valued
-- well-founded relations on the closure's decodings (`Coded-Order`,
-- `order-height`, `hartogs-height`):
--
--   hartogs-height = node (Σ c. Coded-Order (interpret c)) order-height.
--
-- It asks no classifier, unlike OrdinalGeometry's Height.Hartogs, whose
-- H(a) asks one of every code: a closure with unique names cannot have one
-- under univalence, since on the component of the two-point type it would
-- be a section of the universal two-point family. The relations here are
-- valued in the closure's codes, so the index of the fan is a small type.
--
-- A height is regular for named families (`Regular-For-Named-Families`)
-- when the join of the heights of any family of coded orders on merely
-- named types, indexed by a decoding, lies strictly below it. The family
-- is data and only its naming is mere: an ordinal is a canonical type with
-- its order, and lying below is a property, as in the classical
-- definition.
--
-- With unique names the Hartogs height is regular for named families,
-- with no excluded middle, choice or resizing
-- (`unique-names-give-regularity`). Unique choice names every member
-- (Univalent.Completion's `unique-names-name-covered-codes`), each order
-- pulls back to its member's code (`pulled-order`), the sum code names the
-- members' total, and the order within the total's fibers lies above every
-- member's (`fiber-family`, `fiber-relation`, `fiber-order`, `fiber-step`,
-- `fiber-below`). That order is well-founded through the dependent
-- lexicographic order with no steps between first components
-- (`no-steps`, `within-fiber`), and a map keeping an order raises its
-- ranks (`rank-at-along`, `whole-along`, for any relations;
-- Height.Presentation's `rank-at-map` is their instance at
-- presentations). In every closure every coded order on the natural
-- numbers lies below the Hartogs height (`countable-below`), and the Mahlo
-- rule with unique names gives, for every operator, a closure whose
-- Hartogs height is regular (`reflector-gives-regular-heights`). Whether
-- the plain rule does is declared and not inhabited
-- (`Regular-Hartogs-Heights`). Read classically, in a closure with power
-- sets, regularity with `countable-below` makes the Hartogs height an
-- uncountable regular cardinal, which ZF does not prove to exist (Gitik's
-- model), so a model of the plain rule refuting `Regular-Hartogs-Heights`
-- would refute the passage to unique names.

open import SPT.Base
open import SPT.Foundation.Accessibility using
  (is-accessible; acc; is-well-founded)
open import SPT.Foundation.Covers using (Covered)
open import SPT.Foundation.Isomorphisms using
  (_≅_; forward; backward; forward-backward)
open import SPT.Foundation.WellFounded.Lexicographic using
  ( dependent-lexicographic; within
  ; dependent-lexicographic-is-well-founded )
open import SPT.Foundation.WellFounded.Pullback using
  (pullback-is-well-founded)
open import SPT.Foundation.WellFounded.Subrelation using
  (subrelations-are-well-founded)
import SPT.Foundation.Tree as Tree
import SPT.Mahlo.Ambient as Ambient
import SPT.Mahlo.Specification as Specification
open import SPT.Mahlo.DS.Naming using (recast)
open import SPT.Mahlo.DS.Realization.Family using (cast)
open import SPT.Mahlo.DS.Univalent.Completion using
  (Has-Unique-Names; unique-names-name-covered-codes)
open import SPT.Mahlo.DS.Univalent.Names using (Isomorphic-Name)
open import SPT.Mahlo.DS.Univalent.Reflector using (Reflector)
open import SPT.Mahlo.DS.Univalent.Types using
  (Type-Hypotheses; type-parent)
open import SPT.OrdinalGeometry.Height.Ordinals using
  (Height; rank-at; whole; join; join-least)
open import SPT.OrdinalGeometry.Height.Simulation using
  (_⊑_; _⊏_; below; under; ⊑-refl; ⊑-trans; ⊑-⊏-trans)

------------------------------------------------------------------------
-- The Hartogs height of a closure

module _ {ℓ : Level} {Φ : Ambient.Operator ℓ} {K : Set ℓ}
  (L : Specification.Closure (Ambient.formers ℓ) Φ K) where

  open Specification.Closure L using (interpret)

  -- Mathematical shape: a relation on X valued in the closure's codes,
  -- well-founded where its codes decode to inhabited types (y below x).
  record Coded-Order (X : Set ℓ) : Set ℓ where
    field
      relation : X → X → K
      founded : is-well-founded (λ y x → interpret (relation y x))

  -- The height of a coded order: the node over its points of their ranks.
  order-height : (X : Set ℓ) → Coded-Order X → Height ℓ
  order-height X O =
    whole (λ y x → interpret (Coded-Order.relation O y x))
      (Coded-Order.founded O)

  -- Mathematical shape: node (Σ c. Coded-Order (interpret c)) order-height.
  hartogs-height : Height ℓ
  hartogs-height =
    Tree.node (Σ K (λ c → Coded-Order (interpret c)))
      (λ i → order-height (interpret (pr₁ i)) (pr₂ i))

  -- Mathematical shape: Π a X. (Π y. merely a name of X y) →
  --   Π (O : Π y. Coded-Order (X y)). join_y order-height (O y) ⊏ hartogs.
  Regular-For-Named-Families : Set (lsuc ℓ)
  Regular-For-Named-Families =
    (a : K) (X : interpret a → Set ℓ) →
    ((y : interpret a) →
      Covered ℓ
        (Isomorphic-Name
          (Specification.Decode (λ (A : Set ℓ) → A) interpret) (X y))) →
    (O : (y : interpret a) → Coded-Order (X y)) →
    join (interpret a) (λ y → order-height (X y) (O y)) ⊏ hartogs-height

------------------------------------------------------------------------
-- Ranks along maps that keep the order

module _ {ℓ : Level} {A B : Set ℓ} (less : A → A → Set ℓ)
  (less′ : B → B → Set ℓ) (m : A → B)
  (keeps : (y x : A) → less y x → less′ (m y) (m x)) where

  rank-at-along : (x : A) (a : is-accessible less x)
    (b : is-accessible less′ (m x)) →
    rank-at less x a ⊑ rank-at less′ (m x) b
  rank-at-along x (acc smaller) (acc smaller′) =
    below (λ p →
      under (m (pr₁ p) , keeps (pr₁ p) x (pr₂ p))
        (rank-at-along (pr₁ p) (smaller (pr₁ p) (pr₂ p))
          (smaller′ (m (pr₁ p)) (keeps (pr₁ p) x (pr₂ p)))))

  whole-along : (wf : is-well-founded less) (wf′ : is-well-founded less′) →
    whole less wf ⊑ whole less′ wf′
  whole-along wf wf′ =
    below (λ x → under (m x) (rank-at-along x (wf x) (wf′ (m x))))

------------------------------------------------------------------------
-- Coded orders along identifications and isomorphisms

module _ {ℓ : Level} {Φ : Ambient.Operator ℓ} {K : Set ℓ}
  (L : Specification.Closure (Ambient.formers ℓ) Φ K) where

  open Specification.Closure L using (interpret)

  -- An order moves along an identification of types, with its height.
  moved-order : {X Y : Set ℓ} (e : X ＝ Y) (O : Coded-Order L Y) →
    Σ (Coded-Order L X) (λ O′ → order-height L Y O ⊑ order-height L X O′)
  moved-order {X} refl O = O , ⊑-refl (order-height L X O)

  -- An order pulls back along an isomorphism, its height raised: the
  -- backward map keeps the order, read through forward-backward.
  pulled-order : {X′ X : Set ℓ} (i : X′ ≅ X) (O : Coded-Order L X) →
    Σ (Coded-Order L X′) (λ O′ → order-height L X O ⊑ order-height L X′ O′)
  pulled-order i O =
    record
      { relation = λ y x →
          Coded-Order.relation O (forward i y) (forward i x)
      ; founded =
          pullback-is-well-founded (forward i)
            (λ y x → interpret (Coded-Order.relation O y x))
            (Coded-Order.founded O)
      } ,
    whole-along (λ y x → interpret (Coded-Order.relation O y x))
      (λ y x →
        interpret (Coded-Order.relation O (forward i y) (forward i x)))
      (backward i)
      (λ y x r →
        transport
          (λ u →
            interpret
              (Coded-Order.relation O u (forward i (backward i x))))
          (forward-backward i y ⁻¹)
          (transport (λ v → interpret (Coded-Order.relation O y v))
            (forward-backward i x ⁻¹) r))
      (Coded-Order.founded O)
      (pullback-is-well-founded (forward i)
        (λ y x → interpret (Coded-Order.relation O y x))
        (Coded-Order.founded O))

------------------------------------------------------------------------
-- The order within the fibers of a total

-- The empty relation: no steps between first components.
no-steps : {ℓ : Level} (X : Set ℓ) → X → X → Set ℓ
no-steps {ℓ} X y′ y = Lift ℓ 𝟘

-- Over a code a and a family c of codes with coded orders, the total
-- Σ y. interpret (c y) and the relation within its fibers.

module _ {ℓ : Level} {Φ : Ambient.Operator ℓ} {K : Set ℓ}
  (L : Specification.Closure (Ambient.formers ℓ) Φ K) (a : K)
  (c : Specification.Closure.interpret L a → K)
  (O : (y : Specification.Closure.interpret L a) →
    Coded-Order L (Specification.Closure.interpret L (c y)))
  where

  open Specification.Closure L using (interpret)

  -- The steps within the fiber over y.
  fiber-steps : (y : interpret a) →
    interpret (c y) → interpret (c y) → Set ℓ
  fiber-steps y z′ z = interpret (Coded-Order.relation (O y) z′ z)

  -- The sum, over the identity code of the first components, of the
  -- fiber's relation at the second ones moved into one fiber.
  fiber-family : (s′ s : Σ (interpret a) (λ y → interpret (c y))) →
    Specification.Family
      (Specification.Decode (λ (A : Set ℓ) → A) interpret)
  fiber-family (y′ , z′) (y , z) =
    pr₁ (Specification.Closure.identity L a y′ y) ,
    (λ q →
      Coded-Order.relation (O y)
        (transport (λ v → interpret (c v))
          (cast (pr₂ (Specification.Closure.identity L a y′ y)) q) z′)
        z)

  fiber-relation : (s′ s : Σ (interpret a) (λ y → interpret (c y))) → K
  fiber-relation s′ s = pr₁ (Specification.Closure.sum L (fiber-family s′ s))

  -- A step whose first components are identified is a step within one
  -- fiber.
  within-step : (y′ y : interpret a) (z′ : interpret (c y′))
    (z : interpret (c y)) (p : y′ ＝ y) →
    fiber-steps y (transport (λ v → interpret (c v)) p z′) z →
    dependent-lexicographic (λ y → interpret (c y)) (no-steps (interpret a))
      fiber-steps (y′ , z′) (y , z)
  within-step y′ y z′ z refl r = within y r

  within-fiber : (s′ s : Σ (interpret a) (λ y → interpret (c y))) →
    interpret (fiber-relation s′ s) →
    dependent-lexicographic (λ y → interpret (c y)) (no-steps (interpret a))
      fiber-steps s′ s
  within-fiber (y′ , z′) (y , z) t =
    within-step y′ y z′ z
      (cast (pr₂ (Specification.Closure.identity L a y′ y))
        (pr₁
          (cast
            (pr₂
              (Specification.Closure.sum L (fiber-family (y′ , z′) (y , z))))
            t)))
      (pr₂
        (cast
          (pr₂ (Specification.Closure.sum L (fiber-family (y′ , z′) (y , z))))
          t))

  fiber-order : Coded-Order L (Σ (interpret a) (λ y → interpret (c y)))
  fiber-order = record
    { relation = fiber-relation
    ; founded =
        subrelations-are-well-founded
          (λ {s′} {s} t → within-fiber s′ s t)
          (dependent-lexicographic-is-well-founded
            (λ y → interpret (c y)) (no-steps (interpret a)) fiber-steps
            (λ y → acc (λ y′ n → 𝟘-elim (lower n)))
            (λ y → Coded-Order.founded (O y)))
    }

  -- A step of a fiber's order is a step of the total's, over refl.
  fiber-step : (y : interpret a) (z′ z : interpret (c y)) →
    interpret (Coded-Order.relation (O y) z′ z) →
    interpret (fiber-relation (y , z′) (y , z))
  fiber-step y z′ z r =
    cast
      (pr₂ (Specification.Closure.sum L (fiber-family (y , z′) (y , z))) ⁻¹)
      ( cast (pr₂ (Specification.Closure.identity L a y y) ⁻¹) refl
      , transport
          (λ p →
            interpret
              (Coded-Order.relation (O y)
                (transport (λ v → interpret (c v)) p z′) z))
          (recast (pr₂ (Specification.Closure.identity L a y y)) refl ⁻¹)
          r )

  -- Each fiber's order lies below the order of the total.
  fiber-below : (y : interpret a) →
    order-height L (interpret (c y)) (O y)
      ⊑ order-height L (Σ (interpret a) (λ y → interpret (c y)))
          fiber-order
  fiber-below y =
    whole-along (λ z′ z → interpret (Coded-Order.relation (O y) z′ z))
      (λ s′ s → interpret (fiber-relation s′ s))
      (λ z → y , z)
      (fiber-step y)
      (Coded-Order.founded (O y))
      (Coded-Order.founded fiber-order)

------------------------------------------------------------------------
-- Regularity from unique names

unique-names-give-regularity : {ℓ : Level} (H : Type-Hypotheses ℓ)
  {Φ : Ambient.Operator ℓ} {K : Set ℓ}
  (L : Specification.Closure (Ambient.formers ℓ) Φ K) →
  Has-Unique-Names (type-parent H) L → Regular-For-Named-Families L
unique-names-give-regularity H L unique a X named O =
  let names = λ y →
        unique-names-name-covered-codes (type-parent H) L unique (X y)
          (named y)
      codes = λ y → pr₁ (names y)
      pulled = λ y → pulled-order L (pr₂ (names y)) (O y)
      total = Specification.Closure.sum L (a , codes)
      moved =
        moved-order L (pr₂ total)
          (fiber-order L a codes (λ y → pr₁ (pulled y)))
  in
  ⊑-⊏-trans
    (join-least (Specification.Closure.interpret L a)
      (λ y → order-height L (X y) (O y))
      (order-height L
        (Σ (Specification.Closure.interpret L a)
          (λ y → Specification.Closure.interpret L (codes y)))
        (fiber-order L a codes (λ y → pr₁ (pulled y))))
      (λ y →
        ⊑-trans (pr₂ (pulled y))
          (fiber-below L a codes (λ y → pr₁ (pulled y)) y)))
    (⊑-⊏-trans (pr₂ moved)
      (under (pr₁ total , pr₁ moved)
        (⊑-refl
          (order-height L (Specification.Closure.interpret L (pr₁ total))
            (pr₁ moved)))))

------------------------------------------------------------------------
-- The countable ordinals lie below

-- The natural code's decoding carries every coded order on ℕ into the fan.
countable-below : {ℓ : Level} {Φ : Ambient.Operator ℓ} {K : Set ℓ}
  (L : Specification.Closure (Ambient.formers ℓ) Φ K)
  (O : Coded-Order L (Lift ℓ ℕ)) →
  order-height L (Lift ℓ ℕ) O ⊏ hartogs-height L
countable-below L O =
  let moved = moved-order L (pr₂ (Specification.Closure.natural L)) O
  in
  ⊑-⊏-trans (pr₂ moved)
    (under (pr₁ (Specification.Closure.natural L) , pr₁ moved)
      (⊑-refl
        (order-height L
          (Specification.Closure.interpret L
            (pr₁ (Specification.Closure.natural L)))
          (pr₁ moved))))

------------------------------------------------------------------------
-- The rule with unique names gives regular heights

reflector-gives-regular-heights : {ℓ : Level} → Type-Hypotheses ℓ →
  Reflector ℓ → (Φ : Ambient.Operator ℓ) →
  Σ (Set ℓ) (λ K →
    Σ (Specification.Closure (Ambient.formers ℓ) Φ K)
      (λ L → Regular-For-Named-Families L))
reflector-gives-regular-heights H R Φ =
  Specification.Reflection.carrier
    (Specification.Mahlo.reflect (Reflector.mahlo R) Φ) ,
  Specification.Reflection.closure
    (Specification.Mahlo.reflect (Reflector.mahlo R) Φ) ,
  unique-names-give-regularity H
    (Specification.Reflection.closure
      (Specification.Mahlo.reflect (Reflector.mahlo R) Φ))
    (Reflector.unique R Φ)

------------------------------------------------------------------------
-- The question in this form

-- Merely declared: the plain Mahlo rule gives, for every operator, a
-- closure whose Hartogs height is regular for named families. The rule
-- with unique names does (`reflector-gives-regular-heights`).
Regular-Hartogs-Heights : (ℓ : Level) → Set (lsuc ℓ)
Regular-Hartogs-Heights ℓ =
  Type-Hypotheses ℓ → Specification.Mahlo (Ambient.formers ℓ) →
  (Φ : Ambient.Operator ℓ) →
  Σ (Set ℓ) (λ K →
    Σ (Specification.Closure (Ambient.formers ℓ) Φ K)
      (λ L → Regular-For-Named-Families L))
