{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Lifting where

-- Well-founded trees under lifting. A tree over A and B raises to a tree over
-- their lifts, and lowers back, by recursion (`raised-tree`, `lowered-tree`).
-- The two are inverse under extensionality for the branches
-- (`lowered-raised`, `raised-lowered`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Tree.W using (W; sup)

module _ {ℓ : Level} (ℓ′ : Level) (A : Set ℓ) (B : A → Set ℓ) where

  raised-tree : W A B → W (Lift ℓ′ A) (λ a → Lift ℓ′ (B (lower a)))
  raised-tree (sup x f) = sup (lift x) (λ b → raised-tree (f (lower b)))

  lowered-tree : W (Lift ℓ′ A) (λ a → Lift ℓ′ (B (lower a))) → W A B
  lowered-tree (sup x f) = sup (lower x) (λ b → lowered-tree (f (lift b)))

  lowered-raised : ((a : A) → FunExt (B a) (λ _ → W A B)) →
    (t : W A B) → lowered-tree (raised-tree t) ＝ t
  lowered-raised e (sup x f) =
    ap (sup x)
      ( e x
          (λ b → lowered-tree (raised-tree (f b)))
          f
          (λ b → lowered-raised e (f b)))

  raised-lowered :
    ( (a : Lift ℓ′ A) →
      FunExt (Lift ℓ′ (B (lower a)))
        (λ _ → W (Lift ℓ′ A) (λ a′ → Lift ℓ′ (B (lower a′))))) →
    (t : W (Lift ℓ′ A) (λ a → Lift ℓ′ (B (lower a)))) →
    raised-tree (lowered-tree t) ＝ t
  raised-lowered e (sup x f) =
    ap (sup x)
      ( e x
          (λ b → raised-tree (lowered-tree (f b)))
          f
          (λ b → raised-lowered e (f b)))
