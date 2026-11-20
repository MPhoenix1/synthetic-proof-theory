{-# OPTIONS --safe --without-K #-}

module SPT.IR.Morphism.Initiality where

-- Initiality among algebras with their laws. For an algebra with
-- induction on source arguments and its computation identity, the fold
-- into every algebra is a morphism, every morphism is the fold pointwise
-- (`fold`, `unique`), and the morphisms are contractible (`initial`). The
-- generated part of every algebra is such an algebra (`generated`, by
-- Induction.Generated; `generated-unique`, `generated-initial`), and so
-- is the induction–recursion of smallness (`small-unique`,
-- `small-initial`).

open import SPT.Base
open import SPT.Foundation.Contractible using (is-contractible)
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Induction.Initiality using
  (Section; Extensionality; uniform; center; homotopy; contractible)

open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.IR.Description using (Desc; indexed; Shape)
import SPT.IR.Generated as Generated
open import SPT.IR.Induction.Generated using (source; source-β)
open import SPT.IR.Morphism using (Fibers; step; Morphism)
import SPT.IR.Polynomial as Polynomial
open import SPT.IR.Restriction using (Position; input)
open import SPT.IR.Smallness using (Smallness)

------------------------------------------------------------------------
-- Algebras with induction are initial

-- The morphisms from M into N are the sections of N's step over M, so
-- Foundation.Induction.Initiality applies at the fibers: induction at the
-- step, the fold of N, is a morphism; with extensionality over positions
-- every morphism is the fold pointwise, and with the rest of its
-- extensionality the morphisms form a contractible type.

module _
  {s κ κ′ j : Level} {E : Set j} {γ : Desc {s = s} E}
  (extensionality : (A : Set s) → FunExt A (λ _ → E))
  (M : Algebra κ γ) (N : Algebra κ′ γ) (law : Law M) (law′ : Law N)
  (ind :
    Argument-Induction (input γ (indexed (Algebra.K M) (Algebra.value M)))
      (Algebra.operation M) (κ′ ⊔ j))
  (computation :
    Argument-Computation (input γ (indexed (Algebra.K M) (Algebra.value M)))
      (Algebra.operation M) ind)
  where

  open Algebra M using (K; value; operation)

  fold : Morphism extensionality M N law law′
  fold =
    center (input γ (indexed K value)) operation ind computation
      (Fibers M N) (step extensionality M N law law′)

  unique :
    ( (z : Shape γ (indexed K value))
      → FunExt (Position γ (indexed K value) z)
          (λ p → Fibers M N (input γ (indexed K value) z p)))
    → (h : Morphism extensionality M N law law′) (k : K)
    → Section.valuation fold k ＝ Section.valuation h k
  unique =
    homotopy (input γ (indexed K value)) operation ind computation
      (Fibers M N) (step extensionality M N law law′)

  initial :
    Extensionality (input γ (indexed K value)) operation ind (Fibers M N)
      (step extensionality M N law law′)
    → is-contractible (Morphism extensionality M N law law′)
  initial =
    contractible (input γ (indexed K value)) operation ind computation
      (Fibers M N) (step extensionality M N law law′)

------------------------------------------------------------------------
-- The generated part is initial

-- The generated part of M, with introduction as its operation and the
-- decoding law make-β from M's law (`generated`), has induction on source
-- arguments with its computation identity (Induction.Generated). Its fold
-- is unique pointwise under extensionality for functions from the
-- arities' level only, into the outputs, the derivations and the fibers;
-- the morphism type is contractible under extensionality for functions
-- on the generated part and its source arguments as well.

generated :
  {s κ j : Level} {E : Set j} {γ : Desc {s = s} E}
  → Algebra κ γ → Algebra (s ⊔ κ) γ
generated M = record
  { K = Generated.G M
  ; value = Generated.t M
  ; operation = Generated.make M
  }

module _
  {s κ κ′ j : Level} {E : Set j} {γ : Desc {s = s} E}
  (extensionality : (A : Set s) → FunExt A (λ _ → E))
  (positions : Polynomial.Extensionality s κ)
  (motive : (A : Set s) (B : A → Set (κ′ ⊔ j)) → FunExt A B)
  (M : Algebra κ γ) (law : Law M) (N : Algebra κ′ γ) (law′ : Law N)
  where

  generated-fold :
    Morphism extensionality (generated M) N (Generated.make-β M law) law′
  generated-fold =
    fold extensionality (generated M) N (Generated.make-β M law) law′
      (source M positions (κ′ ⊔ j))
      (source-β M positions (κ′ ⊔ j) motive)

  generated-unique :
    ( h :
        Morphism extensionality (generated M) N (Generated.make-β M law)
          law′)
    (g : Generated.G M)
    → Section.valuation generated-fold g ＝ Section.valuation h g
  generated-unique =
    unique extensionality (generated M) N (Generated.make-β M law) law′
      (source M positions (κ′ ⊔ j))
      (source-β M positions (κ′ ⊔ j) motive)
      ( λ z →
          motive (Position γ (indexed (Generated.G M) (Generated.t M)) z)
            ( λ p →
                Fibers (generated M) N
                  (input γ (indexed (Generated.G M) (Generated.t M)) z p)))

  generated-initial :
    ((A : Set (s ⊔ κ)) (B : A → Set (κ′ ⊔ j)) → FunExt A B)
    → is-contractible
        (Morphism extensionality (generated M) N (Generated.make-β M law)
          law′)
  generated-initial total =
    initial extensionality (generated M) N (Generated.make-β M law) law′
      (source M positions (κ′ ⊔ j))
      (source-β M positions (κ′ ⊔ j) motive)
      ( uniform (input γ (indexed (Generated.G M) (Generated.t M)))
          (Generated.make M) (source M positions (κ′ ⊔ j))
          (Fibers (generated M) N)
          (step extensionality (generated M) N (Generated.make-β M law) law′)
          motive total total)

------------------------------------------------------------------------
-- Initiality from smallness

-- The induction–recursion smallness derives is the generated part of a
-- description's small algebra, so it is initial among the algebras with
-- their laws. Its arities, carrier and source arguments share the level
-- ℓ, so the contraction needs no further level.

module _
  {ℓ κ′ : Level} (small : Smallness ℓ) (γ : Desc {s = ℓ} (Set ℓ))
  (extensionality : (A : Set ℓ) → FunExt A (λ _ → Set ℓ))
  (positions : Polynomial.Extensionality ℓ ℓ)
  (motive : (A : Set ℓ) (B : A → Set (κ′ ⊔ lsuc ℓ)) → FunExt A B)
  (N : Algebra κ′ γ) (law′ : Law N)
  where

  small-unique :
    ( h :
        Morphism extensionality (generated (Smallness.algebra small γ)) N
          ( Generated.make-β (Smallness.algebra small γ)
              (Smallness.law small γ))
          law′)
    (g : Generated.G (Smallness.algebra small γ))
    → Section.valuation
        ( generated-fold extensionality positions motive
            (Smallness.algebra small γ) (Smallness.law small γ) N law′)
        g
      ＝ Section.valuation h g
  small-unique =
    generated-unique extensionality positions motive
      (Smallness.algebra small γ) (Smallness.law small γ) N law′

  small-initial :
    is-contractible
      (Morphism extensionality (generated (Smallness.algebra small γ)) N
        ( Generated.make-β (Smallness.algebra small γ)
            (Smallness.law small γ))
        law′)
  small-initial =
    generated-initial extensionality positions motive
      (Smallness.algebra small γ) (Smallness.law small γ) N law′ motive
