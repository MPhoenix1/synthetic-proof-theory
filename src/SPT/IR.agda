{-# OPTIONS --safe --without-K #-}

module SPT.IR where

-- Induction–recursion on SPT's base. Dybjer–Setzer descriptions, general
-- indexed codes and polynomial codes; algebras of them, and the generated part
-- of an algebra as closed trees of a signature, with induction, initiality
-- among algebras, morphisms and translations; the smallness principle of
-- induction–recursion as a statement, with its lowerings; the rules of
-- Shulman's univalent universes and least generations. Native
-- induction–recursive types: the universal type of Dybjer–Setzer descriptions
-- and its decoding (Universal), with Dybjer–Setzer's induction and its
-- initiality, induction on source arguments, initiality among lawful algebras
-- and the action of translations; one induction–recursive family for all
-- schemes of indexed polynomial induction–recursion (Indexed), with its
-- initiality, the comparison with ordinary arguments, Dybjer–Setzer's rules for
-- general indexed codes (Indexed.General), and Kubánek's reducibility predicate
-- for the external Mahlo universe as a general code, also over Kripke stages
-- and with neutral codes (Indexed.General.Reducibility). Every realized law
-- holds by refl. This module is an index; each module is imported by name where
-- it is used.
--
--   Description(.Indexed(.Counter))   Dybjer–Setzer descriptions and
--                                general indexed codes (an example code)
--   Polynomial(.Action, .Algebra, .Frontier, .Factorization
--   (.Discriminator))            polynomial codes of indexed
--                                induction–recursion, their algebras
--   Algebra, Action, Restriction, Layers, Arguments, Predicate,
--   Identifications(.Discriminator)   algebras, shapes, recursive inputs
--                                and layers; identifications of shapes
--   Generated(.Initiality(.Discriminator)), Induction.Generated,
--   Comparison(.Discriminator)   the generated part of an algebra, its
--                                induction and initiality; the raised
--                                fixed point
--   Polynomial.Generated(.Initiality), .Induction(.Initiality),
--   .General(.Discriminator, .Initiality), .Outputs
--                                the same for schemes, Dybjer–Setzer's
--                                rules for general codes on generated
--                                parts, outputs polynomial in types
--   General(.Initiality)         Dybjer–Setzer's rules for general codes
--                                and their initiality, over any inductive
--                                family of the code
--   Morphism(.Composition, .Initiality, .Uniqueness, .Fusion,
--   .Discriminator)              morphisms of algebras; initiality,
--                                uniqueness and fusion
--   Translation(.Morphism, .Fold, .Initiality, .Fusion(.Discriminator),
--   .Discriminator)              translations of descriptions and their
--                                fold, functorial
--   Smallness(.Lowering, .Initiality, .Discriminator)   the smallness
--                                principle, its lowerings, unique induction
--   Univalent.Universe, .Generation, .Classifier, .Resizing
--                                Shulman's univalent universes; least
--                                generations from a classifier or resizing
--   Universal                    the universal type and its decoding
--   Universal.Induction          Dybjer–Setzer's induction rule
--   Universal.Derivation         the derivations of the elements, as
--                                closed trees of one signature
--   Universal.Initiality         pointwise initiality of the native
--                                induction, from the trees' at the
--                                derivations (and .Discriminator)
--   Universal.Discriminator      decoding by refl, distinct codes
--   Universal.Source             induction on source arguments, its
--                                sections contractible (and .Discriminator)
--   Universal.Morphism           initiality among lawful algebras
--                                (and .Discriminator)
--   Universal.Translation        the action of translations, its functor
--                                laws (and .Discriminator)
--   Indexed                      the universal family of a scheme
--   Indexed.Derivation           the derivations of its elements, as
--                                closed trees of one signature
--   Indexed.Initiality           its pointwise initiality, from the
--                                trees' at the derivations
--                                (and .Discriminator)
--   Indexed.Induction            induction on ordinary arguments
--                                (and .Initiality(.Discriminator))
--   Indexed.Comparison           native and ordinary arguments
--   Indexed.Discriminator        a universe of base types and sums
--   Indexed.General              general indexed codes, with no
--                                extensionality (and .Discriminator,
--                                .Initiality(.Discriminator))
--   Indexed.General.Reducibility Kubánek's reducibility predicate
--                                (and .Discriminator, .Kripke(...))

import SPT.IR.Description
import SPT.IR.Algebra
import SPT.IR.Restriction
import SPT.IR.Generated
import SPT.IR.Generated.Initiality
import SPT.IR.Generated.Initiality.Discriminator
import SPT.IR.Arguments
import SPT.IR.Identifications
import SPT.IR.Identifications.Discriminator
import SPT.IR.Induction.Generated
import SPT.IR.Predicate
import SPT.IR.Smallness
import SPT.IR.Smallness.Lowering
import SPT.IR.Smallness.Initiality
import SPT.IR.Smallness.Discriminator
import SPT.IR.Comparison
import SPT.IR.Comparison.Discriminator
import SPT.IR.Action
import SPT.IR.Layers
import SPT.IR.Morphism
import SPT.IR.Morphism.Initiality
import SPT.IR.Morphism.Uniqueness
import SPT.IR.Morphism.Discriminator
import SPT.IR.Morphism.Composition
import SPT.IR.Morphism.Fusion
import SPT.IR.Translation
import SPT.IR.Translation.Morphism
import SPT.IR.Translation.Fold
import SPT.IR.Translation.Initiality
import SPT.IR.Translation.Discriminator
import SPT.IR.Translation.Fusion
import SPT.IR.Translation.Fusion.Discriminator
import SPT.IR.Polynomial
import SPT.IR.Description.Indexed
import SPT.IR.Description.Indexed.Counter
import SPT.IR.Polynomial.Action
import SPT.IR.Polynomial.Frontier
import SPT.IR.Polynomial.Algebra
import SPT.IR.Polynomial.Generated
import SPT.IR.Polynomial.Generated.Initiality
import SPT.IR.Polynomial.Induction
import SPT.IR.Polynomial.Induction.Initiality
import SPT.IR.Polynomial.Factorization
import SPT.IR.Polynomial.Factorization.Discriminator
import SPT.IR.General
import SPT.IR.General.Initiality
import SPT.IR.Polynomial.General
import SPT.IR.Polynomial.General.Discriminator
import SPT.IR.Polynomial.General.Initiality
import SPT.IR.Polynomial.Outputs
import SPT.IR.Univalent.Universe
import SPT.IR.Univalent.Generation
import SPT.IR.Univalent.Resizing
import SPT.IR.Univalent.Classifier
import SPT.IR.Universal
import SPT.IR.Universal.Induction
import SPT.IR.Universal.Derivation
import SPT.IR.Universal.Initiality
import SPT.IR.Universal.Initiality.Discriminator
import SPT.IR.Universal.Discriminator
import SPT.IR.Universal.Source
import SPT.IR.Universal.Source.Discriminator
import SPT.IR.Universal.Morphism
import SPT.IR.Universal.Morphism.Discriminator
import SPT.IR.Universal.Translation
import SPT.IR.Universal.Translation.Discriminator
import SPT.IR.Indexed
import SPT.IR.Indexed.Derivation
import SPT.IR.Indexed.Initiality
import SPT.IR.Indexed.Initiality.Discriminator
import SPT.IR.Indexed.Induction
import SPT.IR.Indexed.Induction.Initiality
import SPT.IR.Indexed.Induction.Initiality.Discriminator
import SPT.IR.Indexed.Comparison
import SPT.IR.Indexed.Discriminator
import SPT.IR.Indexed.General
import SPT.IR.Indexed.General.Discriminator
import SPT.IR.Indexed.General.Initiality
import SPT.IR.Indexed.General.Initiality.Discriminator
import SPT.IR.Indexed.General.Reducibility
import SPT.IR.Indexed.General.Reducibility.Discriminator
import SPT.IR.Indexed.General.Reducibility.Kripke
import SPT.IR.Indexed.General.Reducibility.Kripke.Discriminator
import SPT.IR.Indexed.General.Reducibility.Kripke.Initiality
import SPT.IR.Indexed.General.Reducibility.Kripke.Neutral
import SPT.IR.Indexed.General.Reducibility.Kripke.Neutral.Discriminator
import SPT.IR.Indexed.General.Reducibility.Kripke.Neutral.Initiality
