{-# OPTIONS --safe --without-K #-}

module SPT.IR.Indexed.General.Initiality where

-- Pointwise initiality of Dybjer–Setzer's elimination rule for general
-- indexed induction–recursion on the universal family (IR.Indexed.General),
-- with no extensionality. The universal family's own induction has
-- pointwise initiality, IR.Indexed.Initiality's, itself
-- Foundation.Tree.Fold.Initiality's at the derivations. Its relation
-- lifting at a located argument, past the identification, is the lifting
-- at the code's argument, which the native comparison reads forward to the
-- lifting at a shape (`lifted-forward`). So the universal family has the
-- record of IR.General.Initiality (`universal-initiality`), and that
-- module's laws hold of the rule: relational uniqueness, the fundamental
-- theorem, uniqueness for congruent methods and fusion, with the
-- computation identity by refl (IR.Indexed.General's
-- `universal-computation`).

open import SPT.Base

open import SPT.IR.Indexed using (U; value; family)
import SPT.IR.Indexed as Indexed
open import SPT.IR.Indexed.General using (to; hyp-forward; universal)
import SPT.IR.Indexed.Initiality as Initiality
open import SPT.IR.General.Initiality using (Lifted; Pointwise-Initiality)
open import SPT.IR.Description.Indexed using
  (ι; σ; δ; General; Shape; map-IH; general; polynomial)
open import SPT.IR.Polynomial using (Scheme; shape)

------------------------------------------------------------------------
-- Native relatedness read forward

-- At an argument of a subcode, the native lifting at the valuation's
-- values is the lifting at the shape, past the unit of a constant at σ and
-- out of the lift at each input at δ.

module _
  {ℓ κ μ ν ρ : Level} {I : Set ℓ} {D : I → Set (ℓ ⊔ κ)}
  (γ : General ℓ κ I D)
  (Q : (i : I) → U (general γ) i → Set μ)
  (P : (i : I) → U (general γ) i → Set ν)
  (C : (i : I) (u : U (general γ) i) → Q i u → P i u → Set ρ)
  (v : (i : I) (u : U (general γ) i) → Q i u)
  where

  lifted-forward :
    (ε : General ℓ κ I D) (x : Shape ε (family (general γ)))
    (k : Indexed.Hyp (general γ) P (polynomial ε) (to (general γ) ε x))
    → Initiality.Lifted (general γ) Q P C (polynomial ε)
        (to (general γ) ε x)
        (Initiality.values (general γ) Q v (polynomial ε)
          (to (general γ) ε x))
        k
    → Lifted (family (general γ)) Q P C ε x
        (map-IH ε (family (general γ)) Q v x)
        (hyp-forward (general γ) P ε x k)
  lifted-forward (ι e) x k r = lift ⋆
  lifted-forward (σ A f) (a , x) (h , k) (r , r′) =
    lifted-forward (f a) x k r′
  lifted-forward (δ A i F) (g , x) (h , k) (r , r′) =
    ( (λ a → lower (r a))
    , lifted-forward (F (λ a → value (general γ) (i a) (g a))) x k r′)

------------------------------------------------------------------------
-- The universal family's pointwise initiality

module _
  {ℓ κ : Level} {I : Set ℓ} {D : I → Set (ℓ ⊔ κ)} (γ : General ℓ κ I D)
  where

  universal-initiality : Pointwise-Initiality (universal γ)
  universal-initiality = record
    { Related = λ Q P C i b →
        Initiality.Lifted (general γ) Q P C
          (shape (Scheme.rule (general γ) i)) b
    ; values = λ Q v i b →
        Initiality.values (general γ) Q v
          (shape (Scheme.rule (general γ) i)) b
    ; unique-rel = λ Q P C v m law →
        Initiality.ind-unique-rel (general γ) Q P C v m law
    ; lifted-forward = λ Q P C v x k r →
        lifted-forward γ Q P C v γ x (pr₁ k) (pr₁ r)
    }
