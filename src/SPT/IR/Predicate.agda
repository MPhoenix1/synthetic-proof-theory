{-# OPTIONS --safe --without-K #-}

module SPT.IR.Predicate where

-- Predicates that a description preserves. Q on the decodings of the
-- recursive inputs and R on the outputs follow the description's
-- constructors and the actual returns of its δ nodes (`Good`: terminal,
-- parameter, recursive). A shape whose inputs decode into Q has an output
-- in R (`preserve`). For a lawful algebra M and a predicate Q that γ
-- preserves, every element of the generated part decodes into Q, by
-- induction (`Preservation`: `method`, `all`, `all-β` by refl), and so does
-- every introduction from inputs decoding into Q (`step`). Hypotheses are
-- functions on positions.

open import SPT.Base

open import SPT.IR.Description using
  (DS; Desc; ι; σ; δ; indexed; Shape; Mark)
open import SPT.IR.Algebra using (Algebra; Law)
import SPT.IR.Generated as Generated
open import SPT.IR.Restriction using
  (Position; input; heads; children)

------------------------------------------------------------------------
-- Preserved predicates

data Good {s d e q r : Level} {D : Set d} {E : Set e}
  (Q : D → Set q) (R : E → Set r) :
  DS {s = s} D E → Set (lsuc s ⊔ d ⊔ e ⊔ q ⊔ r) where
  terminal : {v : E} → R v → Good Q R (ι v)
  parameter :
    {A : Set s} {H : A → DS {s = s} D E}
    → ((a : A) → Good Q R (H a)) → Good Q R (σ A H)
  recursive :
    {A : Set s} {H : (A → D) → DS {s = s} D E}
    → ((v : A → D) → ((a : A) → Q (v a)) → Good Q R (H v))
    → Good Q R (δ A H)

preserve :
  {s κ d q r : Level} {D : Set d} {X : Set κ}
  {Q : D → Set q} {R : D → Set r} (v : X → D) (γ : Desc {s = s} D)
  → Good Q R γ → (a : Shape γ (indexed X v))
  → ((p : Position γ (indexed X v) a) → Q (v (input γ (indexed X v) a p)))
  → R (Mark γ (indexed X v) a)
preserve v (ι e) (terminal good) a h = good
preserve v (σ A H) (parameter good) (x , a) h = preserve v (H x) (good x) a h
preserve v (δ A H) (recursive good) (f , a) h =
  preserve v (H (λ x → v (f x)))
    (good (λ x → v (f x)) (λ x → h (inl x))) a (λ p → h (inr p))

------------------------------------------------------------------------
-- Preservation along the generated part

module Preservation
  {s κ d q : Level} {D : Set d} {γ : Desc {s = s} D} (M : Algebra κ γ)
  (law : Law M) (Q : D → Set q) (good : Good Q Q γ)
  where

  method : Generated.Method M (λ g → Q (Generated.t M g))
  method a xs h =
    transport Q (law a ⁻¹) (preserve (Algebra.value M) γ good a h)

  all : (g : Generated.G M) → Q (Generated.t M g)
  all = Generated.ind M (λ g → Q (Generated.t M g)) method

  all-β :
    (z : Shape γ (indexed (Generated.G M) (Generated.t M)))
    → all (Generated.make M z)
      ＝ method
          (heads (Algebra.value M) (Generated.Der M) γ z)
          (children (Algebra.value M) (Generated.Der M) γ z)
          (λ p → all
            ( input γ (indexed (Algebra.K M) (Algebra.value M))
                (heads (Algebra.value M) (Generated.Der M) γ z) p
            , children (Algebra.value M) (Generated.Der M) γ z p))
  all-β z = refl

  step :
    (z : Shape γ (indexed (Generated.G M) (Generated.t M)))
    → ((p : Position γ (indexed (Generated.G M) (Generated.t M)) z)
      → Q (Generated.t M
          (input γ (indexed (Generated.G M) (Generated.t M)) z p)))
    → Q (Generated.t M (Generated.make M z))
  step z h =
    transport Q (Generated.make-β M law z ⁻¹)
      (preserve (Generated.t M) γ good z h)
