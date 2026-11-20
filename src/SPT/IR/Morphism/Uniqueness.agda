{-# OPTIONS --safe --without-K #-}

module SPT.IR.Morphism.Uniqueness where

-- Uniqueness of the generated part. The generated parts of two lawful algebras
-- of one description are isomorphic: the folds each way compose to a morphism
-- from a generated part to itself, which the fold's uniqueness identifies with
-- the identity (`generated-parts-are-isomorphic`). So every lawful algebra has
-- the raised fixed point as its generated part, up to isomorphism, whatever
-- its carrier.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Fibers.Transport using (first-of-transport)
open import SPT.Foundation.Induction.Initiality using (Section)
open import SPT.Foundation.Isomorphisms using (_≅_)

open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.IR.Description using (Desc)
import SPT.IR.Generated as Generated
open import SPT.IR.Layers using (normal)
open import SPT.IR.Morphism using (Morphism)
open import SPT.IR.Morphism.Composition using (compose; identity)
open import SPT.IR.Morphism.Initiality using
  (generated; generated-fold; generated-unique)
import SPT.IR.Polynomial as Polynomial

module _
  {s κ κ′ j : Level} {E : Set j} {γ : Desc {s = s} E}
  (arities : (A : Set s) (B : A → Set j) → FunExt A B)
  (positions : Polynomial.Extensionality s κ)
  (positions′ : Polynomial.Extensionality s κ′)
  (motive : (A : Set s) (B : A → Set (s ⊔ κ ⊔ j)) → FunExt A B)
  (motive′ : (A : Set s) (B : A → Set (s ⊔ κ′ ⊔ j)) → FunExt A B)
  (M : Algebra κ γ) (law : Law M) (N : Algebra κ′ γ) (law′ : Law N)
  where

  forth : Morphism (normal E arities) (generated M) (generated N)
    (Generated.make-β M law) (Generated.make-β N law′)
  forth =
    generated-fold (normal E arities) positions motive′ M law (generated N)
      (Generated.make-β N law′)

  back : Morphism (normal E arities) (generated N) (generated M)
    (Generated.make-β N law′) (Generated.make-β M law)
  back =
    generated-fold (normal E arities) positions′ motive N law′ (generated M)
      (Generated.make-β M law)

  to : Generated.G M → Generated.G N
  to x = pr₁ (Section.valuation forth x)

  from : Generated.G N → Generated.G M
  from y = pr₁ (Section.valuation back y)

  -- The composite and the identity are both the fold into the generated part.
  from-to : (x : Generated.G M) → from (to x) ＝ x
  from-to x =
    let twice = compose arities motive′ motive
                  (generated M) (generated N) (generated M)
                  (Generated.make-β M law)
                  (Generated.make-β N law′)
                  (Generated.make-β M law)
                  back
                  forth
        unit = identity arities (generated M) (Generated.make-β M law)
        unique = generated-unique (normal E arities) positions motive
                   M law (generated M) (Generated.make-β M law)
    in first-of-transport (Algebra.value (generated M))
         (pr₂ (Section.valuation forth x))
         (Section.valuation back (pr₁ (Section.valuation forth x))) ⁻¹
       ∙ ap pr₁ (unique twice x ⁻¹ ∙ unique unit x)

-- Mathematical shape: G M ≅ G N for lawful M and N. The second round trip is
-- the first at the two algebras exchanged.
generated-parts-are-isomorphic :
  {s κ κ′ j : Level} {E : Set j} {γ : Desc {s = s} E}
  (arities : (A : Set s) (B : A → Set j) → FunExt A B)
  (positions : Polynomial.Extensionality s κ)
  (positions′ : Polynomial.Extensionality s κ′)
  (motive : (A : Set s) (B : A → Set (s ⊔ κ ⊔ j)) → FunExt A B)
  (motive′ : (A : Set s) (B : A → Set (s ⊔ κ′ ⊔ j)) → FunExt A B)
  (M : Algebra κ γ) (law : Law M) (N : Algebra κ′ γ) (law′ : Law N) →
  Generated.G M ≅ Generated.G N
generated-parts-are-isomorphic
  arities positions positions′ motive motive′ M law N law′ = record
  { forward = to arities positions positions′ motive motive′ M law N law′
  ; backward = from arities positions positions′ motive motive′ M law N law′
  ; backward-forward =
      from-to arities positions positions′ motive motive′ M law N law′
  ; forward-backward =
      from-to arities positions′ positions motive′ motive N law′ M law
  }
