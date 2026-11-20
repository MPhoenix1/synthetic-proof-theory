{-# OPTIONS --safe --without-K #-}

module SPT.IR.General where

-- Dybjer–Setzer's rules for general indexed induction–recursion (Indexed
-- induction–recursion, JLAP 2006, §4.7, §4.8), once for every inductive
-- family of a general code γ (`Inductive-Family`, a record): carriers with
-- readouts, the arguments of γ's polynomial code over them with their
-- information, compared with the shapes of γ clause by clause, an
-- introduction at every argument located at an index with its readout law,
-- and an induction on located arguments with the hypotheses it supplies.
-- IR.Indexed.General gives the universal family, with no extensionality;
-- IR.Polynomial.General the generated part of any algebra, under
-- extensionality for families of information over the arities.
--
-- Over all indices, located arguments are the shapes: an index with an
-- identification is a singleton (`Located`, `arguments`). Introduction
-- lands at the index its argument computes, with its decoding equation
-- (`intro`, `decoding`). A method on shapes is carried to the located
-- arguments along that isomorphism, giving the elimination rule (`Method`,
-- `ind`), whose computation equation holds wherever the family's induction
-- has its own (`Computation`, `ind-β`):
--
--   ind m (pr₁ (Mark γ Z x)) (intro x) ＝ m x (map-IH γ Z P (ind m) x).

open import SPT.Base
open import SPT.Foundation.HalfAdjoint.Extension using
  (extension; extension-β)
open import SPT.Foundation.Isomorphisms using (_≅_)

open import SPT.IR.Description.Indexed using
  (General; Shape; Mark; IH; map-IH; Information; result)
open import SPT.IR.Polynomial using (Family; carrier; readout)

------------------------------------------------------------------------
-- Located arguments

-- An argument with an identification of the index it computes with i.

module _
  {ℓ κ : Level} {I : Set ℓ} {D : I → Set (ℓ ⊔ κ)} (γ : General ℓ κ I D)
  where

  Located-Argument : (A : Set ℓ) → (A → Information γ) → I → Set ℓ
  Located-Argument A information i =
    Σ A (λ y → pr₁ (result γ (information y)) ＝ i)

------------------------------------------------------------------------
-- Inductive families of a general code

record Inductive-Family
  {ℓ κ : Level} {I : Set ℓ} {D : I → Set (ℓ ⊔ κ)} (γ : General ℓ κ I D)
  : Setω where
  field
    family : Family ℓ κ D
    Arguments : Set ℓ
    information : Arguments → Information γ
    to : Shape γ family → Arguments
    from : Arguments → Shape γ family
    from-to : (x : Shape γ family) → from (to x) ＝ x
    to-from : (y : Arguments) → to (from y) ＝ y
    output-to :
      (x : Shape γ family) → result γ (information (to x)) ＝ Mark γ family x
    make :
      (i : I) → Located-Argument γ Arguments information i
      → carrier family i
    make-β :
      (i : I) (y : Arguments) (e : pr₁ (result γ (information y)) ＝ i)
      → readout family i (make i (y , e))
        ＝ transport D e (pr₂ (result γ (information y)))
    Hypotheses :
      {ν : Level} (P : (i : I) → carrier family i → Set ν) (i : I)
      → Located-Argument γ Arguments information i → Set (ℓ ⊔ ν)
    induction :
      {ν : Level} (P : (i : I) → carrier family i → Set ν)
      → ((i : I) (b : Located-Argument γ Arguments information i)
        → Hypotheses P i b → P i (make i b))
      → (i : I) (t : carrier family i) → P i t
    calls :
      {ν : Level} (P : (i : I) → carrier family i → Set ν)
      → ((i : I) (b : Located-Argument γ Arguments information i)
        → Hypotheses P i b → P i (make i b))
      → (i : I) (b : Located-Argument γ Arguments information i)
      → Hypotheses P i b
    hyp-forward :
      {ν : Level} (P : (i : I) → carrier family i → Set ν)
      (x : Shape γ family)
      → Hypotheses P (pr₁ (Mark γ family x)) (to x , ap pr₁ (output-to x))
      → IH γ family P x
    calls-forward :
      {ν : Level} (P : (i : I) → carrier family i → Set ν)
      (m : (i : I) (b : Located-Argument γ Arguments information i)
        → Hypotheses P i b → P i (make i b))
      (x : Shape γ family)
      → hyp-forward P x
          (calls P m (pr₁ (Mark γ family x)) (to x , ap pr₁ (output-to x)))
        ＝ map-IH γ family P (induction P m) x

------------------------------------------------------------------------
-- Shapes and located arguments

module _
  {ℓ κ : Level} {I : Set ℓ} {D : I → Set (ℓ ⊔ κ)} {γ : General ℓ κ I D}
  (F : Inductive-Family γ)
  where

  open Inductive-Family F

  Located : Set ℓ
  Located = Σ I (Located-Argument γ Arguments information)

  settle :
    (y′ y : Arguments) → y′ ＝ y
    → (j : I) (c′ : pr₁ (result γ (information y′)) ＝ j)
    → (i : I) (c : pr₁ (result γ (information y)) ＝ i)
    → _＝_ {A = Located} (j , y′ , c′) (i , y , c)
  settle y′ _ refl _ refl _ refl = refl

  forth : Shape γ family → Located
  forth x = pr₁ (Mark γ family x) , to x , ap pr₁ (output-to x)

  back : Located → Shape γ family
  back (i , y , c) = from y

  back-forth : (x : Shape γ family) → back (forth x) ＝ x
  back-forth x = from-to x

  forth-back : (b : Located) → forth (back b) ＝ b
  forth-back (i , y , c) =
    settle (to (from y)) y (to-from y) (pr₁ (Mark γ family (from y)))
      (ap pr₁ (output-to (from y))) i c

  arguments : Shape γ family ≅ Located
  arguments = record
    { forward = forth
    ; backward = back
    ; backward-forward = back-forth
    ; forward-backward = forth-back
    }

------------------------------------------------------------------------
-- Introduction and the decoding equation

  intro : (x : Shape γ family) → carrier family (pr₁ (Mark γ family x))
  intro x = make (pr₁ (Mark γ family x)) (to x , ap pr₁ (output-to x))

  decoding :
    (x : Shape γ family)
    → readout family (pr₁ (Mark γ family x)) (intro x)
      ＝ pr₂ (Mark γ family x)
  decoding x =
    make-β (pr₁ (Mark γ family x)) (to x) (ap pr₁ (output-to x))
    ∙ from-Σ-＝-pr₂ (output-to x)

------------------------------------------------------------------------
-- Dybjer–Setzer's elimination rule

-- A method is prepared at the image of a shape by reading the family's
-- hypotheses forward, then carried to every located argument along the
-- adjusted inverse law (Foundation.HalfAdjoint.Extension); at the image
-- the half-adjoint triangle returns the prepared method.

  module _ {ν : Level} (P : (i : I) → carrier family i → Set ν) where

    Method : Set (ℓ ⊔ ν)
    Method =
      (x : Shape γ family) → IH γ family P x
      → P (pr₁ (Mark γ family x)) (intro x)

    Fiber : Located → Set (ℓ ⊔ ν)
    Fiber (i , b) = Hypotheses P i b → P i (make i b)

    prepared : Method → (x : Shape γ family) → Fiber (forth x)
    prepared m x h = m x (hyp-forward P x h)

    method :
      Method → (i : I) (b : Located-Argument γ Arguments information i)
      → Hypotheses P i b → P i (make i b)
    method m i b = extension arguments Fiber (prepared m) (i , b)

    method-β :
      (m : Method) (x : Shape γ family)
      → method m (pr₁ (Mark γ family x)) (to x , ap pr₁ (output-to x))
        ＝ prepared m x
    method-β m x = extension-β arguments Fiber (prepared m) x

    ind : Method → (i : I) (t : carrier family i) → P i t
    ind m = induction P (method m)

    -- The computation identity of the family's induction.
    Computation : Set (ℓ ⊔ ν)
    Computation =
      (m : (i : I) (b : Located-Argument γ Arguments information i)
        → Hypotheses P i b → P i (make i b))
      (i : I) (b : Located-Argument γ Arguments information i)
      → induction P m i (make i b) ＝ m i b (calls P m i b)

    ind-β :
      Computation → (m : Method) (x : Shape γ family)
      → ind m (pr₁ (Mark γ family x)) (intro x)
        ＝ m x (map-IH γ family P (ind m) x)
    ind-β computation m x =
      computation (method m) (pr₁ (Mark γ family x))
        (to x , ap pr₁ (output-to x))
      ∙ ( ap
            (λ k →
              k
                (calls P (method m) (pr₁ (Mark γ family x))
                  (to x , ap pr₁ (output-to x))))
            (method-β m x)
        ∙ ap (m x) (calls-forward P (method m) x))
