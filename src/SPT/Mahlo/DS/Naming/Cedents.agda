{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Naming.Cedents where

-- The closure over the ambient reflection names exactly the derivable
-- names. Every selection of a tree of Naming.Trees, over any family of
-- small types, is derivable from nothing, by induction on the stage
-- (`applying`, `derived`), so each name of the closure is derivable
-- (`named-derivable`) and lies in every closed cedent (`contained`), with
-- no extensionality. With Cedents.derivable-named the two cedents agree
-- (`derivable-sorted`), so the trees are a small type of derivations of the
-- derivable names.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
import SPT.Mahlo.Ambient as Ambient
open import SPT.Foundation.Tree.W using (sup)
import SPT.Mahlo.Specification as Specification

open import SPT.Mahlo.DS.Cedents using
  ( Ced; _⊆_; ∅ᶜ; Closed; Derivable
  ; empty; unit; two; natural; product; sum; tree; identity; result
  ; branch; least; derivable-named)
open import SPT.IR.Description using (index)
import SPT.Mahlo.DS.Realization.Family as Families
import SPT.Mahlo.DS.Naming as Naming
import SPT.Mahlo.DS.Naming.Trees as Trees

------------------------------------------------------------------------
-- Every tree derives its selections

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Specification.Formers C D) (Φ : Specification.Operator D)
  where

  -- A tag applied to a family of derivable names derives each selection.
  applying :
    (t : Trees.Unary) (F : Specification.Family D)
    → Derivable Q Φ ∅ᶜ (pr₁ F)
    → ((x : D (pr₁ F)) → Derivable Q Φ ∅ᶜ (pr₂ F x))
    → (i : Trees.Selection (Trees.apply Q Φ t F))
    → Derivable Q Φ ∅ᶜ (pr₂ (Trees.apply Q Φ t F) i)
  applying Trees.product F d e i = product (pr₁ F) (pr₂ F) d e
  applying Trees.sum F d e i = sum (pr₁ F) (pr₂ F) d e
  applying Trees.wellfounded F d e i = tree (pr₁ F) (pr₂ F) d e
  applying Trees.operator F d e (inl _) = result (pr₁ F) (pr₂ F) d e
  applying Trees.operator F d e (inr y) = branch (pr₁ F) (pr₂ F) d e y

  derived :
    {A : Set ℓ} (B : A → Set ℓ) (s : Trees.Stage A B)
    (τ : pr₁ (Trees.layer Q Φ B s))
    (i : Trees.Selection (pr₂ (Trees.layer Q Φ B s) τ))
    → Derivable Q Φ ∅ᶜ (pr₂ (pr₂ (Trees.layer Q Φ B s) τ) i)
  derived B (sup (Trees.constant Trees.empty) f) τ i = empty
  derived B (sup (Trees.constant Trees.unit) f) τ i = unit
  derived B (sup (Trees.constant Trees.two) f) τ i = two
  derived B (sup (Trees.constant Trees.natural) f) τ i = natural
  derived B (sup (Trees.applied t x) f) τ i =
    applying t
      (Trees.input D (B x) (Trees.layer Q Φ B (f (inl (lift ⋆))))
        (λ y → Trees.layer Q Φ B (f (inr y))) τ)
      (derived B (f (inl (lift ⋆))) (pr₁ (pr₁ τ)) (pr₂ (pr₁ τ)))
      (λ z →
        derived B (f (inr (pr₁ (pr₂ τ) z)))
          (pr₁ (pr₂ (pr₂ τ) (pr₁ (pr₂ τ) z)))
          (pr₂ (pr₂ (pr₂ τ) (pr₁ (pr₂ τ) z))))
      i
  derived B (sup Trees.identity f) τ i =
    identity (Trees.chosen (Trees.layer Q Φ B (f (lift ⋆))) (pr₁ τ))
      (pr₁ (pr₂ τ)) (pr₂ (pr₂ τ))
      (derived B (f (lift ⋆)) (pr₁ (pr₁ τ)) (pr₂ (pr₁ τ)))

------------------------------------------------------------------------
-- The closure's names are the derivable names

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Specification.Formers C D) (Φ : Specification.Operator D)
  {K : Set ℓ}
  (L : Specification.Closure (Ambient.formers ℓ) (Trees.requests Q Φ) K)
  where

  named-derivable :
    Specification.Name (Naming.sort Q Φ L) ⊆ Derivable Q Φ ∅ᶜ
  named-derivable n =
    transport (Derivable Q Φ ∅ᶜ) (pr₂ n)
      (derived Q Φ (index (Families.view L (Naming.Value.family (pr₁ n))))
        (Trees.Request.stage (Naming.Value.origin (pr₁ n)))
        (Trees.Request.tree (Naming.Value.origin (pr₁ n)))
        (Trees.Request.selection (Naming.Value.origin (pr₁ n))))

  -- The closure lies in every closed cedent.
  contained :
    {ν : Level} {Δ : Ced ν C} → Closed Q Φ Δ
    → Specification.Name (Naming.sort Q Φ L) ⊆ Δ
  contained rules n = least (λ p → 𝟘-elim p) rules (named-derivable n)

  derivable-sorted :
    (extensionality : (X : Set ℓ) → FunExt X (λ _ → C))
    → Derivable Q Φ ∅ᶜ ⊆ Specification.Name (Naming.sort Q Φ L)
  derivable-sorted extensionality =
    derivable-named extensionality (Naming.closure Q Φ L extensionality)
