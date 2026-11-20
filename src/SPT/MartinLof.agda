{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof where

-- Martin-Löf type theory with Russell universes at closed levels, Lift,
-- Π, Σ, identity types, W, 0, 1, + and ℕ, Kubánek's Mahlo subuniverses,
-- and univalence and the ambient Mahlo rule at every level as its only
-- constants, with its models. Its expressions are the trees of a binding
-- signature (Foundation.Tree.Binding), its typing a signature generation,
-- and every derivation is valid in every model of it, by fold over the
-- derivation (`soundness`); in a model where 0 has no closed term the
-- theory derives none (`consistency`). This module is an index; each
-- module is imported by name where it is used.
--
--   MartinLof.Raw          raw expressions as a binding signature
--   MartinLof.Formers      the formers as operations on expressions
--   MartinLof.Formers.Substitution
--                          one substitution law per former
--   MartinLof.Skeleton     expressions compared by first-order skeletons
--   MartinLof.Judgment     contexts, judgments, rules, derivations
--   MartinLof.Structural   the structural rules
--   MartinLof.Rules.*      one rule block per former and the constants
--   MartinLof.Subuniverse  the types of the subuniverses' parts
--   MartinLof.Univalence, MartinLof.Mahlo
--                          the statements of the two constants
--   MartinLof.Univalence.Substitution, .Formation, MartinLof.Mahlo.Formation
--                          the statements under substitution, as types at
--                          level l + 1, and the constants as terms of them
--   MartinLof.Theory       the theory: its constants and rule blocks
--   MartinLof.Derived      the rules as functions on derivations
--   MartinLof.Discriminator
--                          a derivation that needs the extensional rule
--   MartinLof.Model        the models; Model.Russell their base, Model.*
--                          one structure per former, Model.Terminal the
--                          terminal model
--   MartinLof.Soundness    soundness and consistency; Soundness.* the
--                          interpretation, transport of values, and the
--                          validity of every rule block

import SPT.MartinLof.Derived
import SPT.MartinLof.Discriminator
import SPT.MartinLof.Formers
import SPT.MartinLof.Formers.Substitution
import SPT.MartinLof.Judgment
import SPT.MartinLof.Mahlo
import SPT.MartinLof.Mahlo.Formation
import SPT.MartinLof.Model
import SPT.MartinLof.Model.Empty
import SPT.MartinLof.Model.Identity
import SPT.MartinLof.Model.Lift
import SPT.MartinLof.Model.Natural
import SPT.MartinLof.Model.Pi
import SPT.MartinLof.Model.Russell
import SPT.MartinLof.Model.Sigma
import SPT.MartinLof.Model.Subuniverse
import SPT.MartinLof.Model.Sum
import SPT.MartinLof.Model.Terminal
import SPT.MartinLof.Model.Unit
import SPT.MartinLof.Model.WellFounded
import SPT.MartinLof.Raw
import SPT.MartinLof.Rules.Constant
import SPT.MartinLof.Rules.Empty
import SPT.MartinLof.Rules.Identity
import SPT.MartinLof.Rules.Lift
import SPT.MartinLof.Rules.Natural
import SPT.MartinLof.Rules.Pi
import SPT.MartinLof.Rules.Sigma
import SPT.MartinLof.Rules.Subuniverse
import SPT.MartinLof.Rules.Sum
import SPT.MartinLof.Rules.Unit
import SPT.MartinLof.Rules.Universe
import SPT.MartinLof.Rules.WellFounded
import SPT.MartinLof.Skeleton
import SPT.MartinLof.Soundness
import SPT.MartinLof.Soundness.Constant
import SPT.MartinLof.Soundness.Empty
import SPT.MartinLof.Soundness.Environment
import SPT.MartinLof.Soundness.Identity
import SPT.MartinLof.Soundness.Instances
import SPT.MartinLof.Soundness.Interpretation
import SPT.MartinLof.Soundness.Lift
import SPT.MartinLof.Soundness.Natural
import SPT.MartinLof.Soundness.Pi
import SPT.MartinLof.Soundness.Sigma
import SPT.MartinLof.Soundness.Structural
import SPT.MartinLof.Soundness.Subuniverse
import SPT.MartinLof.Soundness.Sum
import SPT.MartinLof.Soundness.Transport
import SPT.MartinLof.Soundness.Typing
import SPT.MartinLof.Soundness.Unit
import SPT.MartinLof.Soundness.WellFounded
import SPT.MartinLof.Soundness.WellFounded.Computation
import SPT.MartinLof.Soundness.WellFounded.Generic
import SPT.MartinLof.Soundness.WellFounded.Induction
import SPT.MartinLof.Soundness.WellFounded.Method
import SPT.MartinLof.Soundness.WellFounded.Trees
import SPT.MartinLof.Structural
import SPT.MartinLof.Subuniverse
import SPT.MartinLof.Theory
import SPT.MartinLof.Univalence
import SPT.MartinLof.Univalence.Formation
import SPT.MartinLof.Univalence.Substitution
