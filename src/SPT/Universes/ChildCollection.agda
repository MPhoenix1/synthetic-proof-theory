{-# OPTIONS --safe --without-K #-}

module SPT.Universes.ChildCollection where

-- Strong Collection and Smallification in the children of a reflector. LCTT
-- states them between a stratum and the one above (LCTT.Meta.Model.Rules);
-- here the child takes the place of the lower stratum and the parent's
-- codes the place of the types one stratum up. The owners are the points of
-- a child type; witnesses and evidence are parent codes; coverage is
-- observed through propositions of the decoding level
-- (SPT.Foundation.Covers). A refinement is a child code of actual
-- occurrences, still covering every owner (`Refinement`); a support is a
-- child code of actual points of a covered parent type (`Small-Support`):
--
--   Strong-Collection L = Π j Y H. Total j Y H → Refinement j Y H,
--   Smallification L = Π (a : C). Covered ℓ (D a) → Small-Support a.
--
-- As in LCTT (Meta.Model.Rules), Strong Collection gives Smallification,
-- given a point of the decoding of the parent's unit code (`smallify`), and
-- with the parent's decoding up to retraction Smallification gives Strong
-- Collection (`strength`): smallify the parent's Σ of the witnesses and
-- evidence over each owner, and collect with the child's Σ of the owners
-- and their supports. Weak resizing into the child, the child's decoding
-- classifying the parent's (`Classifies`), gives Smallification
-- (`weak-to-smallification`), and with the parent's decoding up to
-- retraction Strong Collection (`weak-to-collection`). With the refinement
-- covered rather than given (`Covered-Collection`), Strong Collection is
-- the form a classical reading in cubical Agda can keep; covered
-- Smallification holds given a point of the decoding of the parent's unit
-- code (`covered-smallification`). The rules of a reflector ask these of
-- every child it returns (`Collection-Rule`, `Smallification-Rule`,
-- `Resizing-Rule`, `Covered-Collection-Rule`), as its degrees ask a
-- reflector of each (Degree).

open import SPT.Base
open import SPT.Foundation.Covers using
  (Covered; Cover; covered-by-point; map-covered)
open import SPT.Foundation.Impredicative.Classification using (Classifies)
open import SPT.Mahlo.Specification using
  (Operator; Formers; Decode; Closure; Reflection; Mahlo)
open import SPT.Mahlo.Retraction using
  (Retract; Retracts; out; into; out-into; inherited-retracts)

------------------------------------------------------------------------
-- The rules in one child

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D}
  {Ψ : Operator D} {A : Set ℓ} (L : Closure Q Ψ A) where

  ----------------------------------------------------------------------
  -- Strong Collection

  -- Mathematical shape: Σ (x : Decode j). Σ (y : D (Y x)). D (H x y); every
  -- occurrence keeps its owner.
  Evidence : (j : A) (Y : Decode D (Closure.interpret L) j → C) →
    ((x : Decode D (Closure.interpret L) j) → D (Y x) → C) → Set ℓ
  Evidence j Y H =
    Σ (Decode D (Closure.interpret L) j) (λ x → Σ (D (Y x)) (λ y → D (H x y)))

  -- The evidence covers every owner.
  Total : (j : A) (Y : Decode D (Closure.interpret L) j → C) →
    ((x : Decode D (Closure.interpret L) j) → D (Y x) → C) → Set (lsuc ℓ)
  Total j Y H = Cover ℓ (λ (e : Evidence j Y H) → pr₁ e)

  -- Mathematical shape: a child code of actual occurrences, still covering
  -- every owner.
  record Refinement (j : A) (Y : Decode D (Closure.interpret L) j → C)
    (H : (x : Decode D (Closure.interpret L) j) → D (Y x) → C) :
    Set (lsuc ℓ) where
    constructor refinement
    field
      collected : A
      occurrence : Decode D (Closure.interpret L) collected → Evidence j Y H
      covered : Cover ℓ (λ c → pr₁ (occurrence c))

  Strong-Collection : Set (κ ⊔ lsuc ℓ)
  Strong-Collection = (j : A) (Y : Decode D (Closure.interpret L) j → C)
    (H : (x : Decode D (Closure.interpret L) j) → D (Y x) → C) →
    Total j Y H → Refinement j Y H

  -- Strong Collection with the refinement covered rather than given: it is
  -- observed through propositions of the decoding level, as the owners are.
  Covered-Collection : Set (κ ⊔ lsuc ℓ)
  Covered-Collection = (j : A) (Y : Decode D (Closure.interpret L) j → C)
    (H : (x : Decode D (Closure.interpret L) j) → D (Y x) → C) →
    Total j Y H → Covered ℓ (Refinement j Y H)

  -- A given refinement is covered.
  covering : Strong-Collection → Covered-Collection
  covering φ j Y H total = covered-by-point (φ j Y H total)

  ----------------------------------------------------------------------
  -- Smallification

  -- Mathematical shape: a child code of actual points of D a, inhabited
  -- through propositions of the decoding level.
  record Small-Support (a : C) : Set (lsuc ℓ) where
    constructor support
    field
      index : A
      include : Decode D (Closure.interpret L) index → D a
      reached : Covered ℓ (Decode D (Closure.interpret L) index)

  Smallification : Set (κ ⊔ lsuc ℓ)
  Smallification = (a : C) → Covered ℓ (D a) → Small-Support a

  -- Smallification with the support covered rather than given.
  Covered-Smallification : Set (κ ⊔ lsuc ℓ)
  Covered-Smallification = (a : C) → Covered ℓ (D a) →
    Covered ℓ (Small-Support a)

  -- It holds outright: a point of D a is supported by the child's unit code
  -- and the constant map.
  covered-smallification : D (Formers.unit Q) → Covered-Smallification
  covered-smallification point a covered = map-covered
    (λ y → support (pr₁ (Closure.unit L)) (λ c → y)
      (covered-by-point (transport D (pr₂ (Closure.unit L) ⁻¹) point)))
    covered

  ----------------------------------------------------------------------
  -- Weak resizing into the child

  -- The presenting child code supports D a.
  weak-to-smallification : Classifies D (Decode D (Closure.interpret L)) →
    Smallification
  weak-to-smallification φ a covered = support
    (pr₁ (φ a))
    (pr₂ (pr₂ (φ a)))
    (map-covered (pr₁ (pr₂ (φ a))) covered)

  ----------------------------------------------------------------------
  -- Between the rules

  -- Both are needed only through the refinements and supports they return.

  opaque

    -- One owner, the point of the child's unit code; the witnesses the
    -- points of D a; the point of the parent's unit code as evidence.
    smallify : D (Formers.unit Q) → Strong-Collection → Smallification
    smallify point φ a covered = support
      (Refinement.collected r)
      (λ c → pr₁ (pr₂ (Refinement.occurrence r c)))
      (map-covered pr₁
        (Refinement.covered r (transport D (pr₂ (Closure.unit L) ⁻¹) point)))
      where
      total : Total (pr₁ (Closure.unit L)) (λ x → a) (λ x y → Formers.unit Q)
      total x = map-covered (λ y → (x , y , point) , refl) covered

      r : Refinement (pr₁ (Closure.unit L)) (λ x → a)
        (λ x y → Formers.unit Q)
      r = φ (pr₁ (Closure.unit L)) (λ x → a) (λ x y → Formers.unit Q) total

    -- Smallify the parent's Σ over each owner, its witnesses with their
    -- evidence. The collector is the child's Σ of the owners and their
    -- supports, read as pairs through the inherited retraction.
    strength : Retracts Q → Smallification → Strong-Collection
    strength R σ j Y H total = refinement collector occurrence covered
      where
      local : (x : Decode D (Closure.interpret L) j) →
        Small-Support (Formers.sum Q (Y x , H x))
      local x = σ (Formers.sum Q (Y x , H x)) (map-covered
        (λ q → into (Retracts.sum R (Y x) (H x))
          (transport (λ z → Σ (D (Y z)) (λ y → D (H z y)))
            (pr₂ q) (pr₂ (pr₁ q))))
        (total x))

      index : Decode D (Closure.interpret L) j → A
      index x = Small-Support.index (local x)

      collector : A
      collector = pr₁ (Closure.sum L (j , index))

      pairs : Retract (Decode D (Closure.interpret L) collector)
        (Σ (Decode D (Closure.interpret L) j)
          (λ x → Decode D (Closure.interpret L) (index x)))
      pairs = Retracts.sum (inherited-retracts R L) j index

      occurrence : Decode D (Closure.interpret L) collector → Evidence j Y H
      occurrence c =
        let p = out pairs c in
        pr₁ p ,
        out (Retracts.sum R (Y (pr₁ p)) (H (pr₁ p)))
          (Small-Support.include (local (pr₁ p)) (pr₂ p))

      covered : Cover ℓ (λ c → pr₁ (occurrence c))
      covered x = map-covered
        (λ i → into pairs (x , i) , ap pr₁ (out-into pairs (x , i)))
        (Small-Support.reached (local x))

  weak-to-collection : Retracts Q →
    Classifies D (Decode D (Closure.interpret L)) → Strong-Collection
  weak-to-collection R φ = strength R (weak-to-smallification φ)

------------------------------------------------------------------------
-- The rules of a reflector

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D}
  (M : Mahlo Q) where

  -- Every child M returns satisfies Strong Collection.
  Collection-Rule : Set (κ ⊔ lsuc ℓ)
  Collection-Rule = (Φ : Operator D) →
    Strong-Collection (Reflection.closure (Mahlo.reflect M Φ))

  -- Every child M returns satisfies Smallification.
  Smallification-Rule : Set (κ ⊔ lsuc ℓ)
  Smallification-Rule = (Φ : Operator D) →
    Smallification (Reflection.closure (Mahlo.reflect M Φ))

  -- Every parent code has a weak presentation in every child M returns.
  Resizing-Rule : Set (κ ⊔ ℓ)
  Resizing-Rule = (Φ : Operator D) →
    Classifies D
      (Decode D (Closure.interpret (Reflection.closure (Mahlo.reflect M Φ))))

  smallify-rule : D (Formers.unit Q) → Collection-Rule → Smallification-Rule
  smallify-rule point φ Φ =
    smallify (Reflection.closure (Mahlo.reflect M Φ)) point (φ Φ)

  strength-rule : Retracts Q → Smallification-Rule → Collection-Rule
  strength-rule R σ Φ =
    strength (Reflection.closure (Mahlo.reflect M Φ)) R (σ Φ)

  resizing-to-collection : Retracts Q → Resizing-Rule → Collection-Rule
  resizing-to-collection R φ Φ =
    weak-to-collection (Reflection.closure (Mahlo.reflect M Φ)) R (φ Φ)

  -- Every child M returns satisfies Strong Collection with the refinement
  -- covered.
  Covered-Collection-Rule : Set (κ ⊔ lsuc ℓ)
  Covered-Collection-Rule = (Φ : Operator D) →
    Covered-Collection (Reflection.closure (Mahlo.reflect M Φ))

  covering-rule : Collection-Rule → Covered-Collection-Rule
  covering-rule φ Φ =
    covering (Reflection.closure (Mahlo.reflect M Φ)) (φ Φ)
