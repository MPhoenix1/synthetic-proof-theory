{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.WellFounded.Rank where

-- Well-founded relations packaged as records, ranks of a rewrite system
-- into them, termination from a rank, and maps of well-founded relations.

open import Agda.Primitive using (Level; lsuc; _⊔_)

open import SPT.Cubical.Core.WellFounded
open import SPT.Cubical.Core.WellFounded.Rewrite
open import SPT.Cubical.Core.WellFounded.Termination

------------------------------------------------------------------------
-- Well-founded ranking objects

record WFRel (ℓ ℓr : Level) : Set (lsuc (ℓ ⊔ ℓr)) where
  infix 40 _<_
  field
    Carrier : Set ℓ
    _<_     : Carrier → Carrier → Set ℓr
    wf      : WellFounded _<_

record Rank
  {ℓA ℓR ℓO ℓ< : Level}
  (R : Rewrite ℓA ℓR)
  (O : WFRel ℓO ℓ<)
  : Set (ℓA ⊔ ℓR ⊔ ℓO ⊔ ℓ<)
  where

  open Rewrite R
  open WFRel O

  field
    ρ : State → Carrier

    decreases :
      ∀ x y →
      x ↝ y →
      ρ y < ρ x

rank→term :
  {ℓA ℓR ℓO ℓ< : Level}
  {R : Rewrite ℓA ℓR}
  {O : WFRel ℓO ℓ<} →
    Rank R O → Termination.Term R
rank→term {R = R} {O = O} rank x = go x (WFRel.wf O (ρ x))
  where
    open Rewrite R using (State; _↝_)
    open WFRel O using (_<_)
    open Rank rank using (ρ; decreases)

    go : (x : State) → Acc _<_ (ρ x) → Termination.SN R x
    go x (acc smaller) =
      acc λ y x↝y →
        go y (smaller (ρ y) (decreases x y x↝y))

------------------------------------------------------------------------
-- Morphisms of well-founded relations

record WFRelHom
  {ℓA ℓa ℓB ℓb : Level}
  (Source : WFRel ℓA ℓa)
  (Target : WFRel ℓB ℓb)
  : Set (ℓA ⊔ ℓa ⊔ ℓB ⊔ ℓb)
  where

  module Src = WFRel Source
  module Tgt = WFRel Target

  field
    carrier-map : Src.Carrier → Tgt.Carrier

    preserves-< :
      ∀ {x y : Src.Carrier} →
      Src._<_ x y →
      Tgt._<_ (carrier-map x) (carrier-map y)

id-WFRelHom :
  {ℓ ℓr : Level}
  {O : WFRel ℓ ℓr} →
  WFRelHom O O
id-WFRelHom = record
  { carrier-map = λ x → x
  ; preserves-< = λ x<y → x<y
  }


compose-WFRelHom :
  {ℓA ℓa ℓB ℓb ℓC ℓc : Level}
  {A : WFRel ℓA ℓa}
  {B : WFRel ℓB ℓb}
  {C : WFRel ℓC ℓc} →
  WFRelHom B C →
  WFRelHom A B →
  WFRelHom A C
compose-WFRelHom g f = record
  { carrier-map =
      λ x →
        WFRelHom.carrier-map g
          (WFRelHom.carrier-map f x)

  ; preserves-< =
      λ x<y →
        WFRelHom.preserves-< g
          (WFRelHom.preserves-< f x<y)
  }
