{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Induction.Initiality where

-- Initiality of induction on the arguments of an introduction
-- (`Argument-Induction`), as a contractible type. A motive with a step is an
-- algebra displayed over the introduction; its sections are the valuations
-- satisfying the step's computation equations (`Section`), and induction is
-- one (`center`). Every section is induction at every element, by induction at
-- the motive of identifications (`joined`, `homotopy`, `coherent`). Under
-- extensionality at three named families (`Extensionality`, `uniform`)
-- the sections form a contractible type (`contractible`).

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Contractible using (is-contractible)
open import SPT.Cubical.Foundation.Extensionality using (FunExt)
open import SPT.Cubical.Foundation.Happly using
  (funext; funext-refl; homotopy-induction)

------------------------------------------------------------------------
-- Sections and the extensionality they use

-- A section of P with the step m gives a point of P at every element,
-- and at each introduction the step at the points of its inputs. When P
-- is the fibers of another algebra's decoding, a section is a morphism of
-- algebras (IR.Morphism). The contraction uses extensionality for
-- functions on the positions of each argument, for homotopies out of
-- induction, and for induction's computation equations.

record Section
  {α π κ ν : Level} {A : Set α} {Position : A → Set π} {C : Set κ}
  (input : (z : A) → Position z → C) (make : A → C) (P : C → Set ν)
  (m : Argument-Step input make P) : Set (α ⊔ κ ⊔ ν) where
  field
    valuation : (g : C) → P g
    equations :
      (z : A) → valuation (make z) ＝ m z (λ p → valuation (input z p))

record Extensionality
  {α π κ ν : Level} {A : Set α} {Position : A → Set π} {C : Set κ}
  (input : (z : A) → Position z → C) (make : A → C)
  (ind : Argument-Induction input make ν) (P : C → Set ν)
  (m : Argument-Step input make P) :
  Set (α ⊔ π ⊔ κ ⊔ ν) where
  field
    positions : (z : A) → FunExt (Position z) (λ p → P (input z p))
    homotopies : FunExt C (λ g → Σ (P g) (λ y → ind P m g ＝ y))
    equations :
      FunExt A (λ z → ind P m (make z) ＝ m z (λ p → ind P m (input z p)))

-- Extensionality for every family over the types of the levels of the
-- positions, the elements and the arguments gives the three.

module _
  {α π κ ν : Level} {A : Set α} {Position : A → Set π} {C : Set κ}
  (input : (z : A) → Position z → C) (make : A → C)
  (ind : Argument-Induction input make ν) (P : C → Set ν)
  (m : Argument-Step input make P)
  where

  uniform :
    ((A : Set π) (B : A → Set ν) → FunExt A B)
    → ((A : Set κ) (B : A → Set ν) → FunExt A B)
    → ((A : Set α) (B : A → Set ν) → FunExt A B)
    → Extensionality input make ind P m
  uniform positions elements arguments = record
    { positions = λ z → positions (Position z) (λ p → P (input z p))
    ; homotopies =
        elements C (λ g → Σ (P g) (λ y → ind P m g ＝ y))
    ; equations =
        arguments A
          (λ z → ind P m (make z) ＝ m z (λ p → ind P m (input z p)))
    }

------------------------------------------------------------------------
-- Induction is a section

module _
  {α π κ ν : Level} {A : Set α} {Position : A → Set π} {C : Set κ}
  (input : (z : A) → Position z → C) (make : A → C)
  (ind : Argument-Induction input make ν)
  (computation : Argument-Computation input make ind)
  (P : C → Set ν) (m : Argument-Step input make P)
  where

  center : Section input make P m
  center = record
    { valuation = ind P m
    ; equations = computation P m
    }

------------------------------------------------------------------------
-- Every section is induction, pointwise

-- At an introduction, the computation identity, the step at the
-- identifications of the inputs, and the section's own equation join
-- induction to the section (`joined`). Induction at the motive of these
-- identifications gives them at every element (`homotopy`); its
-- computation identity says that they are joined at every introduction
-- (`coherent`).

module _
  {α π κ ν : Level} {A : Set α} {Position : A → Set π} {C : Set κ}
  (input : (z : A) → Position z → C) (make : A → C)
  (ind : Argument-Induction input make ν)
  (computation : Argument-Computation input make ind)
  (P : C → Set ν) (m : Argument-Step input make P)
  (positions : (z : A) → FunExt (Position z) (λ p → P (input z p)))
  where

  joined :
    (v : (g : C) → P g)
    → ((z : A) → v (make z) ＝ m z (λ p → v (input z p)))
    → (z : A)
    → ((p : Position z) → ind P m (input z p) ＝ v (input z p))
    → ind P m (make z) ＝ v (make z)
  joined v c z q =
    computation P m z
    ∙ ( ap (m z)
          ( funext (positions z)
              (λ p → ind P m (input z p))
              (λ p → v (input z p))
              q)
      ∙ c z ⁻¹)

  homotopy :
    (h : Section input make P m) (g : C) → ind P m g ＝ Section.valuation h g
  homotopy h =
    ind (λ g → ind P m g ＝ Section.valuation h g)
      (joined (Section.valuation h) (Section.equations h))

  coherent :
    (h : Section input make P m) (z : A)
    → homotopy h (make z)
      ＝ joined (Section.valuation h) (Section.equations h) z
          (λ p → homotopy h (input z p))
  coherent h =
    computation (λ g → ind P m g ＝ Section.valuation h g)
      (joined (Section.valuation h) (Section.equations h))

------------------------------------------------------------------------
-- The sections form a contractible type

-- Over a homotopy from induction, a section whose equations are joined
-- along it is induction (`Agrees`). By homotopy induction it suffices to
-- take the constant homotopy. There extensionality sends the step's
-- identification to refl, so the joined identification is the
-- computation identity followed by the inverse equation, and the
-- equations are the computation identity (`agrees-refl`).

module _
  {α π κ ν : Level} {A : Set α} {Position : A → Set π} {C : Set κ}
  (input : (z : A) → Position z → C) (make : A → C)
  (ind : Argument-Induction input make ν)
  (computation : Argument-Computation input make ind)
  (P : C → Set ν) (m : Argument-Step input make P)
  (extensionality : Extensionality input make ind P m)
  where

  Agrees : (v : (g : C) → P g) → ((g : C) → ind P m g ＝ v g) → Set (α ⊔ κ ⊔ ν)
  Agrees v H =
    (c : (z : A) → v (make z) ＝ m z (λ p → v (input z p)))
    → ( (z : A)
        → H (make z)
          ＝ joined input make ind computation P m
              (Extensionality.positions extensionality) v c z
              (λ p → H (input z p)))
    → center input make ind computation P m
      ＝ record { valuation = v ; equations = c }

  agrees-refl : Agrees (ind P m) (λ g → refl)
  agrees-refl c coherence =
    ap (λ e → record { valuation = ind P m ; equations = e })
      ( Extensionality.equations extensionality (computation P m) c
          ( λ z →
              ap (λ d → d ⁻¹ ∙ computation P m z)
                ( coherence z
                ∙ ap
                    ( λ e → computation P m z ∙ (ap (m z) e ∙ c z ⁻¹))
                    ( funext-refl
                        (Extensionality.positions extensionality z)
                        (λ p → ind P m (input z p))))
              ∙ inverse-difference-cancels (computation P m z) (c z)))

  contractible : is-contractible (Section input make P m)
  contractible =
    center input make ind computation P m ,
    ( λ h →
        homotopy-induction (ind P m)
          (Extensionality.homotopies extensionality)
          Agrees
          agrees-refl
          (Section.valuation h)
          ( homotopy input make ind computation P m
              (Extensionality.positions extensionality) h)
          (Section.equations h)
          ( coherent input make ind computation P m
              (Extensionality.positions extensionality) h))
