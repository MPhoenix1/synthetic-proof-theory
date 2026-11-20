{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Model where

-- The models of the core theory (`Model`). A model consists of:
-- - a Russell model (Model.Russell): contexts, substitutions, terms with
--   their types, a tower of Russell universes, comprehension;
-- - a structure for every former: Lift, Π, Σ, identity types, W (over
--   the Π-structure), 0, 1, + and ℕ, and Kubánek's subuniverses: their
--   operations, and their laws over the Π-structure and the operations
--   (Model/);
-- - a closed term for each constant.
--
-- Whether a constant has its statement as type depends on how the
-- statement is interpreted, so it is a hypothesis of soundness, not
-- a field. The simplicial model of Kapulkin–Lumsdaine, with the
-- constants of univalence and the ambient Mahlo rule
-- (Cubical/Mahlo/Simplicial.md), is to be one.

open import SPT.Base hiding (Lift)
open import SPT.MartinLof.Model.Empty using (Empty)
open import SPT.MartinLof.Model.Identity using (Identity)
open import SPT.MartinLof.Model.Lift using (Lift)
open import SPT.MartinLof.Model.Natural using (Natural)
open import SPT.MartinLof.Model.Pi using (Pi)
open import SPT.MartinLof.Model.Russell using (Russell)
open import SPT.MartinLof.Model.Sigma using (Sigma)
open import SPT.MartinLof.Model.Subuniverse using
  (Operations; Subuniverse)
open import SPT.MartinLof.Model.Sum using (Sum)
open import SPT.MartinLof.Model.Unit using (Unit)
open import SPT.MartinLof.Model.WellFounded using (WellFounded)

record Model (ℓ : Level) (C : Set) : Set (lsuc ℓ) where
  field
    base : Russell ℓ
    lift-structure : Lift base
    pi-structure : Pi base
    sigma-structure : Sigma base
    identity-structure : Identity base
    tree-structure : WellFounded base pi-structure
    empty-structure : Empty base
    unit-structure : Unit base
    sum-structure : Sum base
    natural-structure : Natural base
    subuniverse-operations : Operations base
    subuniverse-structure :
      Subuniverse base pi-structure subuniverse-operations
    constant : C → Russell.Tm base (Russell.◇ base)
