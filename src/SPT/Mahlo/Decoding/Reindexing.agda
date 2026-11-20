{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Decoding.Reindexing where

-- Reindexing a W-type's branches by a map homotopic to the identity
-- preserves its trees up to similarity. outward and inward transport
-- branches along the chosen homotopy; similarity gives their round trip,
-- and reindexed packages these maps as an Unfolding.

open import SPT.Base
open import SPT.Foundation.Tree.W using (W; sup)
open import SPT.Mahlo.Retraction using (Similar; Unfolding)

module _ {α β : Level} (X : Set α) (B : X → Set β) (f : X → X)
  (h : (x : X) → f x ＝ x) where

  outward : W X (λ x → B (f x)) → W X B
  outward (sup x g) = sup x (λ t → outward
    (g (transport B (h x ⁻¹) t)))

  inward : W X B → W X (λ x → B (f x))
  inward (sup x g) = sup x (λ t → inward (g (transport B (h x) t)))

  similarity : (w : W X B) → Similar (outward (inward w)) w
  similarity (sup x g) = refl , λ i →
    transport
      (λ k → Similar
        (outward (inward (g (transport B (h x)
          (transport B (h x ⁻¹) i))))) (g k))
      (back-and-forth-transport B (h x) i)
      (similarity (g (transport B (h x) (transport B (h x ⁻¹) i))))

  reindexed : Unfolding (W X (λ x → B (f x))) X B
  reindexed = record
    { out = outward
    ; into = inward
    ; out-into = similarity
    }
