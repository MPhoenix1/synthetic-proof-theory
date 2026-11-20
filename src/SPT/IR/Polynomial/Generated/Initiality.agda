{-# OPTIONS --safe --without-K #-}

module SPT.IR.Polynomial.Generated.Initiality where

-- Pointwise initiality of induction on the derivations of the generated
-- part of an algebra of a scheme (Polynomial.Generated), with no
-- extensionality: a valuation with the lax law is related to induction at
-- every element (`Lax`, `ind-unique-rel`). The lax law asks, at every
-- layer, that the method at any hypotheses related to the valuation at
-- the positions be related to it at the layer's introduction; no
-- reflexivity, transitivity or congruence is asked. The derivations are
-- the closed trees of the generated part's signature and `ind` is
-- induction on them, so this is Foundation.Tree.Fold.Initiality's
-- `induction-unique-rel` at that signature.

open import SPT.Base
import SPT.Foundation.Tree.Fold.Initiality as Trees

open import SPT.IR.Polynomial using (Scheme; carrier; shape)
open import SPT.IR.Polynomial.Algebra using (Algebra)
open import SPT.IR.Polynomial.Generated using
  (Position; input; Der; Carrier; Layer; introduce; Method; ind; no-hole;
   step; apply)

module _ {ℓ κ : Level} {s : Scheme ℓ κ} (M : Algebra s) where

  open Algebra M using (family)

  ----------------------------------------------------------------------
  -- The lax law

  module _
    {μ ν ρ : Level}
    (Q : (i : Scheme.Index s) → Carrier M i → Set μ)
    (P : (i : Scheme.Index s) → Carrier M i → Set ν)
    (C : (i : Scheme.Index s) (t : Carrier M i) → Q i t → P i t → Set ρ)
    where

    Lax :
      ((i : Scheme.Index s) (t : Carrier M i) → Q i t) → Method M P
      → Set (ℓ ⊔ ν ⊔ ρ)
    Lax v m =
      (i : Scheme.Index s) (l : Layer M (shape (Scheme.rule s i)))
      (k :
        (z : Position (shape (Scheme.rule s i)) family (pr₁ l))
        → P (pr₁ (input (shape (Scheme.rule s i)) family (pr₁ l) z))
            (pr₂ (input (shape (Scheme.rule s i)) family (pr₁ l) z) , pr₂ l z))
      → ( (z : Position (shape (Scheme.rule s i)) family (pr₁ l))
          → C (pr₁ (input (shape (Scheme.rule s i)) family (pr₁ l) z))
              (pr₂ (input (shape (Scheme.rule s i)) family (pr₁ l) z) , pr₂ l z)
              (v (pr₁ (input (shape (Scheme.rule s i)) family (pr₁ l) z))
                ( pr₂ (input (shape (Scheme.rule s i)) family (pr₁ l) z)
                , pr₂ l z))
              (k z))
      → C i (introduce M i l) (v i (introduce M i l)) (m i l k)

  ----------------------------------------------------------------------
  -- Relational uniqueness

  module _
    {μ ν ρ : Level}
    (Q : (i : Scheme.Index s) → Carrier M i → Set μ)
    (P : (i : Scheme.Index s) → Carrier M i → Set ν)
    (C : (i : Scheme.Index s) (t : Carrier M i) → Q i t → P i t → Set ρ)
    (v : (i : Scheme.Index s) (t : Carrier M i) → Q i t) (m : Method M P)
    (law : Lax Q P C v m)
    where

    ind-unique-rel :
      (i : Scheme.Index s) (t : Carrier M i) → C i t (v i t) (ind M P m i t)
    ind-unique-rel i t =
      Trees.induction-unique-rel
        (λ (j : Σ (Scheme.Index s) (carrier family)) (d : Der M j) →
          Q (pr₁ j) (pr₂ j , d))
        (λ (j : Σ (Scheme.Index s) (carrier family)) (d : Der M j) →
          P (pr₁ j) (pr₂ j , d))
        (λ (j : Σ (Scheme.Index s) (carrier family)) (d : Der M j) →
          C (pr₁ j) (pr₂ j , d))
        (λ {j} d → v (pr₁ j) (pr₂ j , d))
        (no-hole M P) (step M P m)
        (record
          { at-hole = λ ()
          ; at-node = λ { (apply i′ u) xs k r → law i′ (u , xs) k r }
          })
        (pr₂ t)
