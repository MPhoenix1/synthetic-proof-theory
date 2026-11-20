{-# OPTIONS --safe --without-K #-}

module SPT.IR.Action where

-- Maps into the fibers of one decoding over another act on shapes,
-- keeping their outputs. A δ continuation read at two identified
-- assignments has the same shapes, with the same outputs (`shift`). A
-- shape over Z, with a point of W over the decoding of each of its
-- inputs, gives a shape over W with the same output (`assemble`), under
-- extensionality for functions from an arity into the decodings.
-- Comparison's `assemble`, Smallness.Lowering's `carry` and Morphism's
-- `step` are this action. Polynomial.Action is its form for PN codes.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Fibers using (fiber)

open import SPT.IR.Description using
  (DS; ι; σ; δ; Indexed; index; Shape; Mark)
open import SPT.IR.Restriction using (Position; input)

------------------------------------------------------------------------
-- Moving a shape along an identity of assignments

-- A δ continuation read at two identified assignments has the same
-- shapes, with the same outputs.

shift :
  {s κ d e : Level} {D : Set d} {E : Set e} {A : Set s}
  (Z : Indexed κ D) (H : (A → D) → DS {s = s} D E) {Q R : A → D}
  → R ＝ Q → (z : Shape (H Q) Z)
  → Σ (Shape (H R) Z) (λ y → Mark (H R) Z y ＝ Mark (H Q) Z z)
shift Z H refl z = z , refl

------------------------------------------------------------------------
-- The action of a map into fibers

-- At δ the shape over W continues at the decodings of the chosen points,
-- the shape over Z at those of its inputs; extensionality identifies the
-- two assignments before the continuation is read (`shift`).

module _
  {s κ κ′ d : Level} {D : Set d}
  (extensionality : (A : Set s) → FunExt A (λ _ → D))
  (Z : Indexed κ D) (W : Indexed κ′ D)
  where

  assemble :
    {e : Level} {X : Set e} (S : DS {s = s} D X) (c : Shape S Z)
    → ((p : Position S Z c) → fiber (index W) (index Z (input S Z c p)))
    → Σ (Shape S W) (λ w → Mark S W w ＝ Mark S Z c)
  assemble (ι x) _ h = lift ⋆ , refl
  assemble (σ A H) (a , c) h =
    let rest = assemble (H a) c h
    in (a , pr₁ rest) , pr₂ rest
  assemble (δ A H) (f , c) h =
    let rest = assemble (H (λ x → index Z (f x))) c (λ p → h (inr p))
        moved =
          shift W H
            ( extensionality A
                (λ x → index W (pr₁ (h (inl x))))
                (λ x → index Z (f x))
                (λ x → pr₂ (h (inl x))))
            (pr₁ rest)
    in ((λ x → pr₁ (h (inl x))) , pr₁ moved) , (pr₂ moved ∙ pr₂ rest)
