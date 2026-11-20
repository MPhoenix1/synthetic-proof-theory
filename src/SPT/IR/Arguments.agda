{-# OPTIONS --safe --without-K #-}

module SPT.IR.Arguments where

-- Source arguments over the generated part of an algebra M of a description
-- γ, as layers: Restriction's layers, splitting and joining, at the
-- derivations. An element of the generated part is a layer (`layer`,
-- `expose`, inverse by refl: `expose-layer`, `layer-expose`), and
-- introduction is `layer` after `split`. Every element has a source
-- argument (`unroll`), which introduction gives back with no hypothesis
-- (`unroll-make`, Restriction's `join-split`); under extensionality for
-- families over positions (Restriction's `split-join`), introducing it
-- gives the element back (`make-unroll`), so elements with equal source
-- arguments are equal (`unroll-injective`).

open import SPT.Base
open import SPT.Foundation.Tree using (hole; node)

open import SPT.IR.Description using (Desc; indexed; Shape)
open import SPT.IR.Algebra using (Algebra)
import SPT.IR.Generated as Generated
open import SPT.IR.Polynomial using (Extensionality)
open import SPT.IR.Restriction using
  (Layer; join; join-split; split-join)

module _
  {s κ j : Level} {E : Set j} {γ : Desc {s = s} E} (M : Algebra κ γ)
  where

  open Algebra M using (K; value; operation)

  ----------------------------------------------------------------------
  -- Elements as layers, and their source arguments

  layer : Layer value (Generated.Der M) γ → Generated.G M
  layer (a , xs) = operation a , node (Generated.apply a) xs

  expose : Generated.G M → Layer value (Generated.Der M) γ
  expose (c , hole ())
  expose (c , node (Generated.apply a) xs) = a , xs

  expose-layer :
    (l : Layer value (Generated.Der M) γ) → expose (layer l) ＝ l
  expose-layer l = refl

  layer-expose : (g : Generated.G M) → layer (expose g) ＝ g
  layer-expose (c , hole ())
  layer-expose (c , node (Generated.apply a) xs) = refl

  -- The source argument of an element.
  unroll :
    Generated.G M → Shape γ (indexed (Generated.G M) (Generated.t M))
  unroll g = join value (Generated.Der M) γ (expose g)

  unroll-make :
    (z : Shape γ (indexed (Generated.G M) (Generated.t M)))
    → unroll (Generated.make M z) ＝ z
  unroll-make z = join-split value (Generated.Der M) γ z

  make-unroll :
    Extensionality s κ → (g : Generated.G M)
    → Generated.make M (unroll g) ＝ g
  make-unroll extensionality g =
    ap layer (split-join value (Generated.Der M) extensionality γ (expose g))
    ∙ layer-expose g

  unroll-injective :
    Extensionality s κ → {g h : Generated.G M}
    → unroll g ＝ unroll h → g ＝ h
  unroll-injective extensionality {g} {h} e =
    make-unroll extensionality g ⁻¹
    ∙ ap (Generated.make M) e
    ∙ make-unroll extensionality h
