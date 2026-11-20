{-# OPTIONS --safe --without-K #-}

module SPT.IR.Comparison where

-- The raised fixed point μγ of a description γ is the generated part of its
-- identity algebra (Algebra.identity): an ordinary inductive family at the
-- outputs' level, decoded by its index, with introduction, decoding and
-- induction from Generated. Here it is compared with the generated part of
-- an algebra M with its law, in both directions. Each derivation of M maps
-- into μγ at its own decoding, with no extensionality (`layer`, `output`,
-- `roll`, `to`, `decode`). Under extensionality for index families, each
-- raised code folds back into M's generated part with its decoding kept
-- (`assemble`, Action's at the identity family; `fold`, `folded`, `from`,
-- `decode-from`). No inverse law is asserted.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)

import SPT.IR.Action as Action
open import SPT.IR.Algebra using
  (Algebra; Law; identity; identity-β)
open import SPT.IR.Description using
  (Desc; ι; σ; δ; indexed; Shape; Mark)
import SPT.IR.Generated as Generated
open import SPT.IR.Restriction using (Position; input)

------------------------------------------------------------------------
-- Derivations map into the raised fixed point

module _
  {s κ j : Level} {E : Set j} {γ : Desc {s = s} E} (M : Algebra κ γ)
  where

  open Algebra M using (K; value)

  -- A shape over the carrier, with a raised code at the decoding of each
  -- of its recursive inputs, is a shape over μγ with the same output.

  layer :
    (S : Desc {s = s} E) (a : Shape S (indexed K value))
    → ((p : Position S (indexed K value) a)
      → Generated.Der (identity γ)
          (value (input S (indexed K value) a p)))
    → Shape S
        (indexed (Generated.G (identity γ)) (Generated.t (identity γ)))
  layer (ι e) _ h = lift ⋆
  layer (σ A H) (x , a) h = x , layer (H x) a h
  layer (δ A H) (f , a) h =
    (λ x → value (f x) , h (inl x)) ,
    layer (H (λ x → value (f x))) a (λ p → h (inr p))

  output :
    (S : Desc {s = s} E) (a : Shape S (indexed K value))
    (h : (p : Position S (indexed K value) a)
      → Generated.Der (identity γ)
          (value (input S (indexed K value) a p)))
    → Mark S
        (indexed (Generated.G (identity γ)) (Generated.t (identity γ)))
        (layer S a h)
      ＝ Mark S (indexed K value) a
  output (ι e) _ h = refl
  output (σ A H) (x , a) h = output (H x) a h
  output (δ A H) (f , a) h =
    output (H (λ x → value (f x))) a (λ p → h (inr p))

  -- Each node of M rolls in μγ from its layer, and the law moves the code
  -- to the node's decoding.

  roll :
    Law M
    → Generated.Method M
        (λ g → Generated.Der (identity γ) (Generated.t M g))
  roll law a xs h =
    transport (Generated.Der (identity γ))
      ( Generated.make-β (identity γ) (identity-β γ) (layer γ a h)
      ∙ (output γ a h ∙ law a ⁻¹))
      (pr₂ (Generated.make (identity γ) (layer γ a h)))

  to : Law M → Generated.G M → Generated.G (identity γ)
  to law g =
    Generated.t M g ,
    Generated.ind M
      (λ x → Generated.Der (identity γ) (Generated.t M x)) (roll law) g

  decode :
    (law : Law M) (g : Generated.G M)
    → Generated.t (identity γ) (to law g) ＝ Generated.t M g
  decode law g = refl

------------------------------------------------------------------------
-- Raised codes fold into the generated part

  -- A raised command keeps the decodings q of its recursive inputs, while
  -- the folded children have decodings t ∘ g. Extensionality identifies
  -- the two assignments (Action's `shift`) before the continuation is
  -- read, so the folded shape has the command's output: Action's
  -- `assemble` from the identity family to M's generated part.

  assemble :
    ((A : Set s) → FunExt A (λ _ → E))
    → (S : Desc {s = s} E) (c : Shape S (indexed E (λ e → e)))
    → ((p : Position S (indexed E (λ e → e)) c)
      → Σ (Generated.G M)
          (λ g →
            Generated.t M g ＝ input S (indexed E (λ e → e)) c p))
    → Σ (Shape S (indexed (Generated.G M) (Generated.t M)))
        (λ z →
          Mark S (indexed (Generated.G M) (Generated.t M)) z
            ＝ Mark S (indexed E (λ e → e)) c)
  assemble extensionality S c h =
    Action.assemble extensionality (indexed E (λ e → e))
      (indexed (Generated.G M) (Generated.t M)) S c h

  -- Mathematical shape: every raised code u folds to a derivation g of M
  -- with t g ＝ decode u.

  fold :
    ((A : Set s) → FunExt A (λ _ → E)) → Law M
    → Generated.Method (identity γ)
        (λ u →
          Σ (Generated.G M)
            (λ g → Generated.t M g ＝ Generated.t (identity γ) u))
  fold extensionality law c xs h =
    let arguments = assemble extensionality γ c h
    in Generated.make M (pr₁ arguments) ,
       (Generated.make-β M law (pr₁ arguments) ∙ pr₂ arguments)

  folded :
    ((A : Set s) → FunExt A (λ _ → E)) → Law M
    → (u : Generated.G (identity γ))
    → Σ (Generated.G M) (λ g → Generated.t M g ＝ Generated.t (identity γ) u)
  folded extensionality law =
    Generated.ind (identity γ)
      (λ u →
        Σ (Generated.G M)
          (λ g → Generated.t M g ＝ Generated.t (identity γ) u))
      (fold extensionality law)

  from :
    ((A : Set s) → FunExt A (λ _ → E)) → Law M
    → Generated.G (identity γ) → Generated.G M
  from extensionality law u = pr₁ (folded extensionality law u)

  decode-from :
    (extensionality : (A : Set s) → FunExt A (λ _ → E)) (law : Law M)
    (u : Generated.G (identity γ))
    → Generated.t M (from extensionality law u) ＝ Generated.t (identity γ) u
  decode-from extensionality law u = pr₂ (folded extensionality law u)
