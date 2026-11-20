{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Embeddings where

-- A map is an embedding when each of its fibers is a proposition
-- (`is-embedding`); being one is a proposition under function
-- extensionality (`being-an-embedding-is-a-proposition`). Maps with
-- contractible fibers, lowering out of a lift and the first projection of
-- a family of propositions are embeddings, and so is a composite of
-- embeddings, its fibers being pairs of fibers. An embedding is
-- left-cancellable (`embeddings-are-left-cancellable`), and a
-- left-cancellable map into a set is an embedding
-- (`left-cancellable-maps-into-sets-are-embeddings`).

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Extensionality
  using (FunExt; Π-is-proposition)
open import SPT.Cubical.Foundation.Fibers using (fiber; has-contractible-fibers)
open import SPT.Cubical.Foundation.Fibers.Projection using
  (projection-fiber-isomorphism)
open import SPT.Cubical.Foundation.Fibers.Structure using
  (composite-fiber-isomorphism)
open import SPT.Cubical.Foundation.Propositions using
  (is-proposition; is-set; Σ-is-proposition)
open import SPT.Cubical.Foundation.Propositions.Closure using
  (isomorphic-to-a-proposition)
open import SPT.Cubical.Foundation.Sets
  using (being-a-proposition-is-a-proposition)

------------------------------------------------------------------------
-- Embeddings

-- An embedding identifies two points exactly when it identifies their
-- images; into a set, left cancellation is enough.

module _ {ℓ κ : Level} {A : Set ℓ} {B : Set κ} where

  -- Mathematical shape: Π (b : B). is-proposition (fiber f b).
  is-embedding : (A → B) → Set (ℓ ⊔ κ)
  is-embedding f = (b : B) → is-proposition (fiber f b)

  embeddings-are-left-cancellable : (f : A → B) → is-embedding f →
    (x y : A) → f x ＝ f y → x ＝ y
  embeddings-are-left-cancellable f e x y p =
    ap pr₁ (e (f y) (x , p) (y , refl))

  equivalences-are-embeddings : (f : A → B) → has-contractible-fibers f →
    is-embedding f
  equivalences-are-embeddings f c b u v = pr₂ (c b) u ⁻¹ ∙ pr₂ (c b) v

  left-cancellable-maps-into-sets-are-embeddings : is-set B → (f : A → B) →
    ((x y : A) → f x ＝ f y → x ＝ y) → is-embedding f
  left-cancellable-maps-into-sets-are-embeddings set f cancel b (x , p)
    (y , q) =
    to-Σ-＝ (cancel x y (p ∙ q ⁻¹))
      (set (f y) b
        (transport (λ a → f a ＝ b) (cancel x y (p ∙ q ⁻¹)) p) q)

module _ {ℓ : Level} {A B : Set ℓ}
  (extensionality : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y) where

  being-an-embedding-is-a-proposition : (f : A → B) →
    is-proposition (is-embedding f)
  being-an-embedding-is-a-proposition f =
    Π-is-proposition (extensionality B (λ b → is-proposition (fiber f b)))
      (λ b → being-a-proposition-is-a-proposition extensionality
        (fiber f b))

------------------------------------------------------------------------
-- Lifts, projections and composites

-- The fiber of lowering is a based path space; the fiber of the first
-- projection is the family (Fibers.Projection); the fiber of a composite
-- is a fiber of the outer map with a fiber of the inner one over its
-- middle point (Fibers.Structure).

module _ {ℓ κ : Level} {A : Set ℓ} where

  lowering-is-an-embedding : is-embedding (lower {κ = κ} {A = A})
  lowering-is-an-embedding a (lift .a , refl) (lift .a , refl) = refl

module _ {ℓ κ : Level} {A : Set ℓ} (F : A → Set κ) where

  first-projections-of-propositions-are-embeddings :
    ((a : A) → is-proposition (F a)) → is-embedding (pr₁ {A = A} {B = F})
  first-projections-of-propositions-are-embeddings propositions a =
    isomorphic-to-a-proposition (projection-fiber-isomorphism F a)
      (propositions a)

module _ {ℓ κ μ : Level} {A : Set ℓ} {B : Set κ} {C : Set μ} where

  composites-of-embeddings-are-embeddings : (f : A → B) (g : B → C) →
    is-embedding f → is-embedding g → is-embedding (λ a → g (f a))
  composites-of-embeddings-are-embeddings f g e d c =
    isomorphic-to-a-proposition (composite-fiber-isomorphism f g c)
      (Σ-is-proposition (d c) (λ middle → e (pr₁ middle)))
