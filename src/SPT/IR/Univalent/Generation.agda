{-# OPTIONS --safe --without-K #-}

module SPT.IR.Univalent.Generation where

-- The generated part of an algebra M as a family of propositions on its
-- carrier. A family over the carrier is closed when it holds at every
-- operation whose inputs it holds at (`Closed`); closed families of
-- propositions of level ν are records (`Closed-Family`). A generation of M
-- is one at the carrier's level κ; it is least at level ν when it lies
-- below every closed family of propositions of level ν (`Least`). A least
-- generation is Sattler and Vezzosi's propositional indexed W-type (LICS
-- 2020, Def. B.3, with every index propositional), a higher inductive
-- family. Book type theory has none, so here it is a hypothesis;
-- Univalent.Resizing derives it from propositional resizing.

open import SPT.Base
open import SPT.Foundation.Propositions using (is-proposition)

open import SPT.IR.Algebra using (Algebra)
open import SPT.IR.Description using (Desc; indexed; Shape)
open import SPT.IR.Restriction using (Position; input)

------------------------------------------------------------------------
-- Closed families

module _
  {s κ j : Level} {E : Set j} {γ : Desc {s = s} E} (M : Algebra κ γ)
  where

  open Algebra M using (K; value; operation)

  Closed : {ν : Level} → (K → Set ν) → Set (s ⊔ κ ⊔ ν)
  Closed Q =
    (a : Shape γ (indexed K value))
    → ((p : Position γ (indexed K value) a)
      → Q (input γ (indexed K value) a p))
    → Q (operation a)

record Closed-Family
  {s κ j : Level} {E : Set j} {γ : Desc {s = s} E} (M : Algebra κ γ)
  (ν : Level) : Set (s ⊔ κ ⊔ lsuc ν) where
  field
    family : Algebra.K M → Set ν
    proposition : (k : Algebra.K M) → is-proposition (family k)
    closed : Closed M family

------------------------------------------------------------------------
-- Leastness

Least :
  {s κ j : Level} {E : Set j} {γ : Desc {s = s} E} (M : Algebra κ γ)
  → Closed-Family M κ → (ν : Level) → Set (s ⊔ κ ⊔ lsuc ν)
Least M G ν =
  (C : Closed-Family M ν) (k : Algebra.K M)
  → Closed-Family.family G k → Closed-Family.family C k
