{-# OPTIONS --safe --without-K #-}

module SPT.IR.Univalent.Resizing where

-- Propositional resizing gives least generations. Resizing between two
-- levels is Foundation.Impredicative.PropositionalResizing's
-- `Propositional-Resizing-Between` (a proposition of level ν with a
-- proposition of level κ and maps both ways, `Resized`;
-- `propositions-resize-to-their-level` at one level). The points of an
-- algebra's carrier in every closed family of propositions of level ν
-- (`intersection`) form a proposition under extensionality; resized to
-- the carrier's level they are a generation (`generation`), least at every
-- level that resizes to ν (`shrink`, `least`). In the simplicial model
-- excluded middle holds (Kapulkin–Lumsdaine, TAC 2020), so every
-- proposition is equivalent to 𝟙 or 𝟘, and resizing holds.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt; Π-is-proposition)
open import SPT.Foundation.Impredicative.PropositionalResizing using
  (Resized; Propositional-Resizing-Between)
open import SPT.Foundation.Propositions using (is-proposition)

open import SPT.IR.Algebra using (Algebra)
open import SPT.IR.Description using (Desc; indexed)
open import SPT.IR.Restriction using (input)
open import SPT.IR.Univalent.Generation using
  (Closed-Family; Least)

------------------------------------------------------------------------
-- The intersection of the closed families

-- A point lies in the intersection when it lies in every closed family of
-- propositions of level ν; under extensionality for those families at the
-- point, this is a proposition.

module _
  {s κ j : Level} {E : Set j} {γ : Desc {s = s} E} (M : Algebra κ γ)
  (ν : Level)
  where

  open Algebra M using (K)

  intersection : K → Set (s ⊔ κ ⊔ lsuc ν)
  intersection k = (C : Closed-Family M ν) → Closed-Family.family C k

  intersection-proposition :
    ((k : K) → FunExt (Closed-Family M ν) (λ C → Closed-Family.family C k))
    → (k : K) → is-proposition (intersection k)
  intersection-proposition extensionality k =
    Π-is-proposition (extensionality k)
      (λ C → Closed-Family.proposition C k)

------------------------------------------------------------------------
-- The generation

-- The intersection resized to the carrier's level is closed: at an
-- operation every closed family holds, its inputs being in all of them.
-- A closed family of a level μ that resizes to ν shrinks to one of level
-- ν, which contains the intersection; so the generation is least at μ.

module _
  {s κ j : Level} {E : Set j} {γ : Desc {s = s} E} (M : Algebra κ γ)
  (ν : Level)
  (resize : Propositional-Resizing-Between (s ⊔ κ ⊔ lsuc ν) κ)
  (extensionality :
    (k : Algebra.K M)
    → FunExt (Closed-Family M ν) (λ C → Closed-Family.family C k))
  where

  open Algebra M using (K; value; operation)

  resized : (k : K) → Resized κ (intersection M ν k)
  resized k =
    resize (intersection M ν k)
      (intersection-proposition M ν extensionality k)

  generation : Closed-Family M κ
  generation = record
    { family = λ k → Resized.small (resized k)
    ; proposition = λ k → Resized.small-proposition (resized k)
    ; closed = λ a hs →
        Resized.down (resized (operation a))
          (λ C →
            Closed-Family.closed C a
              (λ p →
                Resized.up (resized (input γ (indexed K value) a p))
                  (hs p) C))
    }

  shrunk :
    (μ : Level) → Propositional-Resizing-Between μ ν →
    (C : Closed-Family M μ) (k : K) → Resized ν (Closed-Family.family C k)
  shrunk μ resize-μ C k =
    resize-μ (Closed-Family.family C k) (Closed-Family.proposition C k)

  shrink : (μ : Level) → Propositional-Resizing-Between μ ν →
    Closed-Family M μ → Closed-Family M ν
  shrink μ resize-μ C = record
    { family = λ k → Resized.small (shrunk μ resize-μ C k)
    ; proposition = λ k → Resized.small-proposition (shrunk μ resize-μ C k)
    ; closed = λ a hs →
        Resized.down (shrunk μ resize-μ C (operation a))
          (Closed-Family.closed C a
            (λ p →
              Resized.up
                (shrunk μ resize-μ C (input γ (indexed K value) a p))
                (hs p)))
    }

  least : (μ : Level) → Propositional-Resizing-Between μ ν →
    Least M generation μ
  least μ resize-μ C k g =
    Resized.up (shrunk μ resize-μ C k)
      (Resized.up (resized k) g (shrink μ resize-μ C))
