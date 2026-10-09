{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Univalence where

-- TypeTopology's univalence (UF.Univalence.Univalence) from Cubical
-- univalence.  idtoeq X Y gets a quasi-inverse: an equivalence e goes to
-- the Cubical ua of e, moved to TypeTopology's identity type.  At refl the
-- round trip is uaIdEquiv; at e it is uaβ, read on underlying functions,
-- since being an equivalence is a proposition (being-equiv-is-prop, with
-- the function extensionality of TypeTopology.FunExt).  TypeTopology's
-- qinvs-are-equivs turns the quasi-inverse into an equivalence.

open import Agda.Primitive using (Level)

import Cubical.Data.Equality.Conversion as EqualityConversion
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.Isomorphism as Isomorphism
import Cubical.Foundations.Prelude as Cubical
import Cubical.Foundations.Univalence as CubicalUnivalence

import SPT.Cubical.TypeTopology.MLTT.Identity-Type as Identity
import SPT.Cubical.TypeTopology.MLTT.Sigma-Type as Sigma
open Sigma.Σ using (pr₁; pr₂)
open import SPT.Cubical.TypeTopology.UF.Equiv using
  (_≃_; idtoeq; equivs-are-qinvs; qinvs-are-equivs)
open import SPT.Cubical.TypeTopology.UF.Equiv-FunExt using
  (being-equiv-is-prop)
open import SPT.Cubical.TypeTopology.UF.Univalence using (Univalence)

open import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.Bridge using
  (≡→＝; path→＝; ＝→path)
open import SPT.Cubical.OrdinalGeometry.Cubical.TypeTopology.FunExt using
  (funext)

private
  variable
    ℓ : Level

  -- The refl path goes to refl.
  path→＝-refl : {A : Set ℓ} {x : A}
    → path→＝ (Cubical.refl {x = x}) Cubical.≡ Identity.refl
  path→＝-refl =
    Cubical.cong ≡→＝
      (EqualityConversion.eqToPath EqualityConversion.pathToEq-reflPath)

  -- Equivalences with the same underlying function are equal.
  equivalence-path : {X Y : Set ℓ} {e e′ : X ≃ Y}
    → pr₁ e Cubical.≡ pr₁ e′ → e Cubical.≡ e′
  equivalence-path {e = e} {e′} p i =
    Sigma._,_ (p i)
      (Cubical.isProp→PathP
        (λ j left right → ＝→path
          (being-equiv-is-prop funext (p j) left right))
        (pr₂ e) (pr₂ e′) i)

  -- A TypeTopology equivalence as a Cubical one, with the same function.
  cubical : {X Y : Set ℓ} → X ≃ Y → X Equiv.≃ Y
  cubical (Sigma._,_ f e) =
    Isomorphism.isoToEquiv
      (Isomorphism.iso f g (λ y → ＝→path (fg y)) (λ x → ＝→path (gf x)))
    where
      quasi = equivs-are-qinvs f e
      g = pr₁ quasi
      gf = pr₁ (pr₂ quasi)
      fg = pr₂ (pr₂ quasi)

  -- Mathematical shape: e ↦ ua e, as an element of X ＝ Y.
  identification : (X Y : Set ℓ) → X ≃ Y → Identity._＝_ X Y
  identification X Y e = path→＝ (CubicalUnivalence.ua (cubical e))

  -- The function of idtoeq at a path is transport along it.
  function : {X Y : Set ℓ} (p : X Cubical.≡ Y)
    → pr₁ (idtoeq X Y (path→＝ p)) Cubical.≡ Cubical.transport p
  function {X = X} =
    Cubical.J
      (λ Y p → pr₁ (idtoeq X Y (path→＝ p)) Cubical.≡ Cubical.transport p)
      (Cubical.cong (λ q → pr₁ (idtoeq X X q)) path→＝-refl
        Cubical.∙ Cubical.funExt λ x → Cubical.sym (Cubical.transportRefl x))

  -- Mathematical shape: ua (idtoeq refl) = refl.
  retraction : (X Y : Set ℓ) (p : Identity._＝_ X Y)
    → Identity._＝_ (identification X Y (idtoeq X Y p)) p
  retraction X .X Identity.refl =
    path→＝
      (Cubical.cong path→＝
        (Cubical.cong CubicalUnivalence.ua (Equiv.equivEq Cubical.refl)
          Cubical.∙ CubicalUnivalence.uaIdEquiv)
        Cubical.∙ path→＝-refl)

  -- Mathematical shape: idtoeq (ua e) = e, on functions by uaβ.
  section : (X Y : Set ℓ) (e : X ≃ Y)
    → Identity._＝_ (idtoeq X Y (identification X Y e)) e
  section X Y e =
    path→＝
      (equivalence-path
        (function (CubicalUnivalence.ua (cubical e))
          Cubical.∙ Cubical.funExt (CubicalUnivalence.uaβ (cubical e))))

univalence : Univalence
univalence ℓ X Y =
  qinvs-are-equivs (idtoeq X Y)
    (Sigma._,_ (identification X Y)
      (Sigma._,_ (retraction X Y) (section X Y)))
