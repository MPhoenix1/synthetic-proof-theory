{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Base.Induction where

-- Induction on the arguments of an introduction. A type C has an
-- introduction make out of a type A of arguments; each argument z has a
-- type of positions, and at each position an input in C:
--
--   input : (z : A) → Position z → C,     make : A → C.
--
-- A step gives P at make z from P at every input of z (`Argument-Step`);
-- induction gives P everywhere from a step (`Argument-Induction`); its
-- computation identity sends make z to the step at z with the hypotheses of
-- induction at its inputs (`Argument-Computation`). Induction into the
-- level of the arguments presents every element as make of an argument
-- (`Argument-Presented`, `argument-presented`, `argument-presentation`,
-- `argument-root`, `make-argument-root`), so elements with equal roots are
-- equal (`argument-root-injective`); with the computation identity, root
-- inverts make (`argument-root-make`) and make is injective
-- (`make-injective`). No output equation and no reflection enters. The
-- source arguments of a Dybjer–Setzer description are an instance, with
-- induction as Dybjer and Setzer state it (IR.Universal.Source).

open import SPT.Cubical.Base.Universes
open import SPT.Cubical.Base.Identity using (_⁻¹; _∙_; _＝_; ap; refl)
open import SPT.Cubical.Base.Sigma using (_,_; pr₁; pr₂; Σ)

module _
  {α π κ : Level} {A : Set α} {Position : A → Set π} {C : Set κ}
  (input : (z : A) → Position z → C) (make : A → C)
  where

  ----------------------------------------------------------------------
  -- The specification

  Argument-Step : {ν : Level} → (C → Set ν) → Set (α ⊔ π ⊔ ν)
  Argument-Step P = (z : A) → ((p : Position z) → P (input z p)) → P (make z)

  Argument-Induction : (ν : Level) → Set (α ⊔ π ⊔ κ ⊔ lsuc ν)
  Argument-Induction ν = (P : C → Set ν) → Argument-Step P → (g : C) → P g

  Argument-Computation : {ν : Level} → Argument-Induction ν →
    Set (α ⊔ π ⊔ κ ⊔ lsuc ν)
  Argument-Computation {ν} ind =
    (P : C → Set ν) (m : Argument-Step P) (z : A)
    → ind P m (make z) ＝ m z (λ p → ind P m (input z p))

  ----------------------------------------------------------------------
  -- Every element from an argument

  -- The arguments that make sends to an element.
  Argument-Presented : C → Set (α ⊔ κ)
  Argument-Presented g = Σ A (λ z → make z ＝ g)

  argument-presented : Argument-Step Argument-Presented
  argument-presented z _ = z , refl

  argument-presentation : Argument-Induction (α ⊔ κ) → (g : C) →
    Argument-Presented g
  argument-presentation ind = ind Argument-Presented argument-presented

  argument-root : Argument-Induction (α ⊔ κ) → C → A
  argument-root ind g = pr₁ (argument-presentation ind g)

  make-argument-root : (ind : Argument-Induction (α ⊔ κ)) (g : C) →
    make (argument-root ind g) ＝ g
  make-argument-root ind g = pr₂ (argument-presentation ind g)

  argument-root-injective :
    (ind : Argument-Induction (α ⊔ κ)) {g h : C} →
      argument-root ind g ＝ argument-root ind h → g ＝ h
  argument-root-injective ind {g} {h} e =
    make-argument-root ind g ⁻¹ ∙ ap make e ∙ make-argument-root ind h

  ----------------------------------------------------------------------
  -- With the computation identity

  argument-root-make :
    (ind : Argument-Induction (α ⊔ κ)) → Argument-Computation ind
    → (z : A) → argument-root ind (make z) ＝ z
  argument-root-make ind computation z =
    ap pr₁ (computation Argument-Presented argument-presented z)

  make-injective :
    (ind : Argument-Induction (α ⊔ κ)) → Argument-Computation ind
    → {z w : A} → make z ＝ make w → z ＝ w
  make-injective ind computation {z} {w} e =
    argument-root-make ind computation z ⁻¹
    ∙ ap (argument-root ind) e
    ∙ argument-root-make ind computation w
