{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Degree.Tree where

-- Degrees of Mahlo reflection along trees. At a node, each position asks every
-- child of the reflector to be Mahlo again, with the degree of the subtree at
-- that position; a hole asks for nothing further (`Along`):
--
--   Along (node o k) M = Π (p : Pos o). Π (Ψ : Operator D).
--     Σ (c : Mahlo (child M Ψ)). Along (k p) (child M Ψ c).
--
-- Substitution composes degrees (`Graft`, `graft`, `ungraft`). Brouwer
-- trees are the trees of one judgment with zero, successors and limits of
-- sequences (`Brouwer`); the finite chains present the finite degrees
-- (`finite`, `to-finite`, `from-finite`), and the tree ω asks for every
-- finite degree at once (`from-omega`, `to-omega`).

open import SPT.Base
open import SPT.Foundation.Tree using
  (Signature; Judgment; Op; Pos; boundary; Tree; hole; node; History)
open import SPT.Foundation.Tree.Substitution using (bind)
open import SPT.Mahlo.Specification using
  (Operator; Formers; Reflection; Mahlo)
open import SPT.Mahlo.Decoding using (MahloReflection; reflect; child-formers)
open import SPT.Mahlo.Degree using
  (child-reflection; Degree; mahlo; child; next)

------------------------------------------------------------------------
-- Degree along a tree

-- The child returned for Ψ is M's own, the same at every position; its
-- reflector and everything below may depend on the position.
Along : {ℓj ℓo ℓp ℓx : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} {j : Judgment S} → Tree S X j →
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D} →
  MahloReflection Q → Set (ℓp ⊔ κ ⊔ lsuc ℓ)
Along {ℓj} {ℓo} {ℓp} (hole x) {κ} {ℓ} M = Lift (ℓp ⊔ κ ⊔ lsuc ℓ) 𝟙
Along {ℓj} {ℓo} {ℓp} {ℓx} {S} (node o k) {κ} {ℓ} {C} {D} M =
  (p : Pos S o) (Ψ : Operator D) →
  Σ (Mahlo (child-formers (Reflection.closure (reflect M Ψ))))
    (λ c → Along (k p) (child-reflection M Ψ c))

------------------------------------------------------------------------
-- Substitution composes degrees

-- Degree along an open tree whose holes are continued by the trees σ.
Graft : {ℓj ℓo ℓp ℓx ℓy : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} {Y : Judgment S → Set ℓy} {j : Judgment S} →
  Tree S X j → ((i : Judgment S) → X i → Tree S Y i) →
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D} →
  MahloReflection Q → Set (ℓp ⊔ κ ⊔ lsuc ℓ)
Graft (hole {j} x) σ M = Along (σ j x) M
Graft {ℓj} {ℓo} {ℓp} {ℓx} {ℓy} {S} (node o k) σ {κ} {ℓ} {C} {D} M =
  (p : Pos S o) (Ψ : Operator D) →
  Σ (Mahlo (child-formers (Reflection.closure (reflect M Ψ))))
    (λ c → Graft (k p) σ (child-reflection M Ψ c))

module _ {ℓj ℓo ℓp ℓx ℓy : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} {Y : Judgment S → Set ℓy} where

  -- Along the substituted tree is exactly Along the outer tree with every hole
  -- asking for the degree along its continuation.
  graft : {j : Judgment S} (t : Tree S X j)
    (σ : (i : Judgment S) → X i → Tree S Y i) {κ ℓ : Level} {C : Set κ}
    {D : C → Set ℓ} {Q : Formers C D} (M : MahloReflection Q) →
    Graft t σ M → Along (bind σ t) M
  graft (hole x) σ M G = G
  graft (node o k) σ M G p Ψ =
    pr₁ (G p Ψ) ,
    graft (k p) σ (child-reflection M Ψ (pr₁ (G p Ψ))) (pr₂ (G p Ψ))

  ungraft : {j : Judgment S} (t : Tree S X j)
    (σ : (i : Judgment S) → X i → Tree S Y i) {κ ℓ : Level} {C : Set κ}
    {D : C → Set ℓ} {Q : Formers C D} (M : MahloReflection Q) →
    Along (bind σ t) M → Graft t σ M
  ungraft (hole x) σ M A = A
  ungraft (node o k) σ M A p Ψ =
    pr₁ (A p Ψ) ,
    ungraft (k p) σ (child-reflection M Ψ (pr₁ (A p Ψ))) (pr₂ (A p Ψ))

------------------------------------------------------------------------
-- Brouwer trees

data Shape : Set where
  stop more limit : Shape

Arity : Shape → Set
Arity stop = 𝟘
Arity more = 𝟙
Arity limit = ℕ

-- One judgment; zero, successors, and limits of sequences.
brouwer : Signature lzero lzero lzero
brouwer = record
  { Judgment = 𝟙
  ; Op = λ _ → Shape
  ; Pos = λ o → Arity o
  ; boundary = λ _ _ → ⋆
  }

Brouwer : Set
Brouwer = History brouwer ⋆

finite : ℕ → Brouwer
finite zero = node stop 𝟘-elim
finite (suc n) = node more (λ _ → finite n)

ω : Brouwer
ω = node limit finite

------------------------------------------------------------------------
-- Finite chains present the finite degrees

-- Both recurse at the children, whose families differ from the parent's.

to-finite : {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D}
  (n : ℕ) (M : MahloReflection Q) → Degree n M → Along (finite n) M
to-finite zero M R = λ p → 𝟘-elim p
to-finite (suc n) M R p Ψ =
  mahlo M n R Ψ , to-finite n (child M n R Ψ) (next M n R Ψ)

from-finite : {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D}
  (n : ℕ) (M : MahloReflection Q) → Along (finite n) M → Degree n M
from-finite zero M R = lift ⋆
from-finite (suc n) M R Ψ =
  pr₁ (R ⋆ Ψ) ,
  from-finite n (child-reflection M Ψ (pr₁ (R ⋆ Ψ))) (pr₂ (R ⋆ Ψ))

------------------------------------------------------------------------
-- Degree ω: every finite degree at once

-- The child returned for Ψ is M's; its reflector is chosen separately for each
-- finite degree. This is the consistent form of "all finite depths".

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D} where

  from-omega : (M : MahloReflection Q) → Along ω M → (n : ℕ) →
    Degree (suc n) M
  from-omega M R n Ψ =
    pr₁ (R n Ψ) ,
    from-finite n (child-reflection M Ψ (pr₁ (R n Ψ))) (pr₂ (R n Ψ))

  to-omega : (M : MahloReflection Q) → ((n : ℕ) → Degree (suc n) M) →
    Along ω M
  to-omega M R n Ψ =
    mahlo M n (R n) Ψ ,
    to-finite n (child M n (R n) Ψ) (next M n (R n) Ψ)
