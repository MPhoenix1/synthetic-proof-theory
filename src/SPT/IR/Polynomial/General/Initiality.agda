{-# OPTIONS --safe --without-K #-}

module SPT.IR.Polynomial.General.Initiality where

-- Pointwise initiality of Dybjer–Setzer's elimination rule for general
-- indexed induction–recursion on the generated part of any algebra
-- (IR.Polynomial.General), under extensionality for families of
-- information over the arities. Induction on literal arguments has
-- pointwise initiality (Polynomial.Induction.Initiality, from
-- Polynomial.Generated.Initiality, itself Foundation.Tree.Fold.
-- Initiality's at the derivations). Relatedness at a located argument is
-- relatedness at the positions of its argument, which reads forward to the
-- lifting at a shape (`lifted-forward`). So the generated part has the
-- record of IR.General.Initiality (`generated-part-initiality`), and that
-- module's laws hold of the rule there: relational uniqueness, the
-- fundamental theorem, uniqueness for congruent methods and fusion, with
-- the computation identity under extensionality for the motive
-- (IR.Polynomial.General's `generated-part-computation`).

open import SPT.Base

open import SPT.IR.General.Initiality using (Lifted; Pointwise-Initiality)
open import SPT.IR.Description.Indexed using
  (ι; σ; δ; General; Shape; map-IH; general; polynomial)
open import SPT.IR.Polynomial using (Scheme; readout; shape; Extensionality)
open import SPT.IR.Polynomial.Algebra using (Algebra)
import SPT.IR.Polynomial.Generated as Generated
open import SPT.IR.Polynomial.General using
  (to; hyp-forward; generated-part)
import SPT.IR.Polynomial.Induction as Induction
import SPT.IR.Polynomial.Induction.Initiality as Literal

------------------------------------------------------------------------
-- Relatedness at positions read forward

-- At an argument of a subcode, relatedness at its positions to the
-- valuation's values is the lifting at the shape: a recursive input of a
-- δ is its position in the product.

module _
  {ℓ κ μ ν ρ : Level} {I : Set ℓ} {D : I → Set (ℓ ⊔ κ)}
  (γ : General ℓ κ I D) (M : Algebra (general γ))
  (let G = Generated.generated M)
  (Q : (i : I) → Generated.Carrier M i → Set μ)
  (P : (i : I) → Generated.Carrier M i → Set ν)
  (C : (i : I) (t : Generated.Carrier M i) → Q i t → P i t → Set ρ)
  (v : (i : I) (t : Generated.Carrier M i) → Q i t)
  where

  lifted-forward :
    (ε : General ℓ κ I D) (x : Shape ε G)
    (k : Induction.Literal M P (polynomial ε) (to G ε x))
    → Literal.Literal-Related M Q P C (polynomial ε) (to G ε x)
        (Literal.literal-values M Q v (polynomial ε) (to G ε x)) k
    → Lifted G Q P C ε x (map-IH ε G Q v x) (hyp-forward G P ε x k)
  lifted-forward (ι e) x k r = lift ⋆
  lifted-forward (σ A f) (a , x) k r =
    lifted-forward (f a) x (λ z → k (inr z)) (λ z → r (inr z))
  lifted-forward (δ A i F) (g , x) k r =
    ( (λ a → r (inl (a , lift ⋆)))
    , lifted-forward (F (λ a → readout G (i a) (g a))) x
        (λ z → k (inr z)) (λ z → r (inr z)))

------------------------------------------------------------------------
-- The generated part's pointwise initiality

module _
  {ℓ κ : Level} {I : Set ℓ} {D : I → Set (ℓ ⊔ κ)} (γ : General ℓ κ I D)
  (M : Algebra (general γ)) (extensionality : Extensionality ℓ κ)
  where

  generated-part-initiality :
    Pointwise-Initiality (generated-part γ M extensionality)
  generated-part-initiality = record
    { Related = λ Q P C i b →
        Literal.Literal-Related M Q P C (shape (Scheme.rule (general γ) i)) b
    ; values = λ Q v i b →
        Literal.literal-values M Q v (shape (Scheme.rule (general γ) i)) b
    ; unique-rel = λ Q P C v m law →
        Literal.source-unique-rel M extensionality Q P C v m law
    ; lifted-forward = λ Q P C v x k r →
        lifted-forward γ M Q P C v γ x (λ z → k (inl z)) (λ z → r (inl z))
    }
