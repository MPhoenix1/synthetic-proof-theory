{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo where

-- Resident reflection over a Tarski family: closures of an operator,
-- reflections, and reflectors, the Mahlo rule; the decoding laws of the
-- selected formers and their inheritance by every reflected child; and the
-- ambient parent of a universe level, whose codes are its types. Residence
-- separates the free closure from its being small and named; DS proves
-- IR's smallness principle equivalent to the ambient Mahlo rule and
-- realizes Dybjer–Setzer induction–recursion in its closures;
-- Heights measures derivations of the derivable names; Polynomial builds
-- parents whose reflections are closures of blocks of polynomial trees.
-- This module is an index; each module is imported by name where it is
-- used.
--
--   Specification   resident reflection
--   Decoding        decoding laws of resident reflection
--   Ambient         the ambient parent
--   Sets            the parent of small sets, its formers and laws
--   Paradox         no type of a universe has that universe as a retract
--   SelfNaming      a family closed under W names no copy of its own index,
--                   and no W-type is one of its own branchings
--   Lifting         well-founded trees under lifting
--   Retraction      decoding of the formers up to retraction
--   Relative        the induction–recursive closure of an operator
--   Degree          degrees of Mahlo reflection
--   Degree.Tree     degrees along trees; Brouwer trees
--   Child           small spaces of a reflected child
--   Space           Mahlo closure with displayed spaces as type-objects
--   Universe        a generated Mahlo universe over a displayed seed
--   Universe.Formation   its spaces, selections and boundary formation
--   Universe.Boundary    the boundary families it codes, with their fills
--   Described       a universe reflecting every operator it describes
--   Described.Discriminator   its reflections have content
--   Polynomial.Basis        a small parent holding the carrier of an
--                           ordinary universe; its ordinary closure
--   Polynomial.Closure      the closure of an operator whose blocks are
--                           literal polynomial trees
--   Polynomial.Generation   generated small types with polynomial tree
--                           carriers and repeated materialization
--   Polynomial.Generation.Formation   higher-order tree formation; a
--                           later product read off no constant family
--   Polynomial.Parent       a raised parent, Mahlo by the polynomial
--                           closures
--   Polynomial.Parent.Formation   higher-order returns as Mahlo trees,
--                           the next operator and its reflection
--
--   Residence.Families      resident families, pullbacks, maps
--   Residence.Constructors  one layer of constructors and its maps
--   Residence.Constructors.Comparison     maps along a triangle
--   Residence.Constructors.Discriminator  exact map boundaries
--   Residence.Absorption    least closures and absorbed reflections
--   Residence.Membership    generated membership, with no IR
--   Residence.Inductive     the induction–recursive closure is least
--   Residence.Names         names of codes formed from named codes
--   Residence.Presentation  presentations of generated totals
--   Residence.Discriminator closure without residence
--   Residence.Subclosure    resident composition; the least subclosure
--   Residence.Reflection    resident returns and their composition
--   Residence.Calibration   absorption against Mahlo
--   Residence.Comparison    residence up to isomorphism
--   Residence.Unreflected   a least closure is not Mahlo
--   Residence.Fibered       residence read off the pullback square
--
--   DS.Ambient(.Initiality), DS.Realization(.Frontier, .Family,
--   .Discriminator, .Schema), DS.Clauses, DS.Smallness.Modal:   the
--                 smallness principle (IR.Smallness) ⇔ the ambient Mahlo
--                 rule, and the initiality of the induction–recursion it
--                 derives; small algebras from closures; closures from
--                 clauses; the principle and the rule under a modality
--   DS.Polynomial(.Realization, .Smallness, .Discriminator, .General,
--   .Outputs(.Discriminator)):   small algebras of the rules of indexed
--                 polynomial induction–recursion, of general codes and of
--                 outputs polynomial in types, from smallness and the rule
--   DS.Sorted(.Frontier, .Family, .Realization(.Discriminator, .Cedents),
--   .Smallness, .Mahlo, .Discriminator):   outputs in any type
--   DS.Naming(.Trees, .Cedents), DS.Cedents:   families admitting the small
--                 types; cedents and derivations
--   DS.Univalent(.Construction, .Reflector(.Universes), .Discriminator,
--   .Names, .Gluing, .Collection, .Completion(.Map), .Sums, .Covering, .Sets,
--   .Types, .Smallness(.Modal)):
--                 univalent universes from algebras with unique names
--                 (their rules in IR.Univalent); names up to isomorphism, the
--                 members of a named cover named through join limits,
--                 collection names families; over a univalent parent,
--                 completed codes along maps of codes, unique names from
--                 collection, collection exactly when the completion
--                 names its sums, and collection from
--                 weakly initial covers, at the small sets and at the
--                 small types; smallness with unique names is Shulman's
--                 universes and the rule with unique names, follows from
--                 its truncation, and from the plain principle given
--                 completions and weakly initial covers, merely existing
--                 ones with least generations, or covered collection in
--                 the reflector's closures
--   DS.Sets(.Description, .Realization, .Ambient, .Smallness):   set-valued
--                 descriptions with set arities, read as type-valued ones;
--                 their smallness principle ⇔ the rule of the parent of
--                 small sets, with and without unique names, and the
--                 passage between them from weakly initial covers
--   DS.Stationary(.Ambient, .Discriminator, .Derivable):   stationary
--                 reflection, the degrees above smallness
--
--   Heights, Heights.Least, Heights.Presentation, Heights.Comparison,
--   Heights.Boundary:   heights of derivations of the derivable names
--   Heights.Stages(.Map), Heights.Regular:   stages of a layer of codes;
--                 the Mahlo rule is regular heights
--   Heights.Univalent:   univalent stages; heights regular for relations
--                 give the rule with unique names
--   Heights.Fiberwise(.Covers):   stages completed child by child; fans
--                 bounding merely named families give the rule with
--                 unique names, and weakly initial covers give such fans
--   Heights.Hartogs:   the Hartogs height of a closure; with unique names
--                 it is regular for named families and uncountable

import SPT.Mahlo.Specification
import SPT.Mahlo.Decoding
import SPT.Mahlo.Ambient
import SPT.Mahlo.Sets
import SPT.Mahlo.Paradox
import SPT.Mahlo.SelfNaming
import SPT.Mahlo.Lifting
import SPT.Mahlo.Retraction
import SPT.Mahlo.Relative
import SPT.Mahlo.Degree
import SPT.Mahlo.Degree.Tree
import SPT.Mahlo.Child
import SPT.Mahlo.Space
import SPT.Mahlo.Universe
import SPT.Mahlo.Universe.Boundary
import SPT.Mahlo.Universe.Formation
import SPT.Mahlo.Described
import SPT.Mahlo.Described.Discriminator
import SPT.Mahlo.Polynomial.Basis
import SPT.Mahlo.Polynomial.Closure
import SPT.Mahlo.Polynomial.Generation
import SPT.Mahlo.Polynomial.Generation.Formation
import SPT.Mahlo.Polynomial.Parent
import SPT.Mahlo.Polynomial.Parent.Formation

import SPT.Mahlo.Residence.Families
import SPT.Mahlo.Residence.Constructors
import SPT.Mahlo.Residence.Constructors.Comparison
import SPT.Mahlo.Residence.Constructors.Discriminator
import SPT.Mahlo.Residence.Absorption
import SPT.Mahlo.Residence.Membership
import SPT.Mahlo.Residence.Inductive
import SPT.Mahlo.Residence.Names
import SPT.Mahlo.Residence.Presentation
import SPT.Mahlo.Residence.Discriminator
import SPT.Mahlo.Residence.Subclosure
import SPT.Mahlo.Residence.Reflection
import SPT.Mahlo.Residence.Calibration
import SPT.Mahlo.Residence.Comparison
import SPT.Mahlo.Residence.Unreflected
import SPT.Mahlo.Residence.Fibered

import SPT.Mahlo.DS.Smallness.Modal
import SPT.Mahlo.DS.Realization.Frontier
import SPT.Mahlo.DS.Realization.Family
import SPT.Mahlo.DS.Realization
import SPT.Mahlo.DS.Realization.Discriminator
import SPT.Mahlo.DS.Realization.Schema
import SPT.Mahlo.DS.Ambient
import SPT.Mahlo.DS.Ambient.Initiality
import SPT.Mahlo.DS.Clauses
import SPT.Mahlo.DS.Polynomial.Realization
import SPT.Mahlo.DS.Polynomial.Smallness
import SPT.Mahlo.DS.Polynomial.Discriminator
import SPT.Mahlo.DS.Polynomial.General
import SPT.Mahlo.DS.Polynomial.Outputs
import SPT.Mahlo.DS.Polynomial.Outputs.Discriminator
import SPT.Mahlo.DS.Sorted
import SPT.Mahlo.DS.Sorted.Frontier
import SPT.Mahlo.DS.Sorted.Family
import SPT.Mahlo.DS.Sorted.Realization
import SPT.Mahlo.DS.Sorted.Smallness
import SPT.Mahlo.DS.Sorted.Mahlo
import SPT.Mahlo.DS.Sorted.Discriminator
import SPT.Mahlo.DS.Sorted.Realization.Discriminator
import SPT.Mahlo.DS.Sorted.Realization.Cedents
import SPT.Mahlo.DS.Naming.Trees
import SPT.Mahlo.DS.Naming
import SPT.Mahlo.DS.Cedents
import SPT.Mahlo.DS.Naming.Cedents
import SPT.Mahlo.DS.Univalent.Construction
import SPT.Mahlo.DS.Univalent.Reflector
import SPT.Mahlo.DS.Univalent.Reflector.Universes
import SPT.Mahlo.DS.Univalent.Discriminator
import SPT.Mahlo.DS.Univalent.Names
import SPT.Mahlo.DS.Univalent.Gluing
import SPT.Mahlo.DS.Univalent.Collection
import SPT.Mahlo.DS.Univalent.Completion
import SPT.Mahlo.DS.Univalent.Completion.Map
import SPT.Mahlo.DS.Univalent.Sums
import SPT.Mahlo.DS.Univalent.Covering
import SPT.Mahlo.DS.Univalent.Sets
import SPT.Mahlo.DS.Univalent.Types
import SPT.Mahlo.DS.Univalent.Smallness
import SPT.Mahlo.DS.Univalent.Smallness.Modal
import SPT.Mahlo.DS.Sets.Description
import SPT.Mahlo.DS.Sets.Realization
import SPT.Mahlo.DS.Sets.Ambient
import SPT.Mahlo.DS.Sets.Smallness
import SPT.Mahlo.DS.Stationary
import SPT.Mahlo.DS.Stationary.Ambient
import SPT.Mahlo.DS.Stationary.Discriminator
import SPT.Mahlo.DS.Stationary.Derivable

import SPT.Mahlo.Heights
import SPT.Mahlo.Heights.Stages
import SPT.Mahlo.Heights.Stages.Map
import SPT.Mahlo.Heights.Regular
import SPT.Mahlo.Heights.Least
import SPT.Mahlo.Heights.Presentation
import SPT.Mahlo.Heights.Comparison
import SPT.Mahlo.Heights.Boundary
import SPT.Mahlo.Heights.Univalent
import SPT.Mahlo.Heights.Fiberwise
import SPT.Mahlo.Heights.Fiberwise.Covers
import SPT.Mahlo.Heights.Hartogs

import SPT.Mahlo.Generation
import SPT.Mahlo.Residence.Adjoined
import SPT.Mahlo.Residence.Adjoined.Children
import SPT.Mahlo.Residence.Adjoined.Connectives
import SPT.Mahlo.Residence.Adjoined.Discrimination
import SPT.Mahlo.Residence.Adjoined.Generation
import SPT.Mahlo.Residence.Adjoined.Realizability
import SPT.Mahlo.Residence.Adjoined.Realizability.ExcludedMiddle
import SPT.Mahlo.Residence.Adjoined.Realizability.Reflection
import SPT.Mahlo.Residence.Adjoined.Sets
import SPT.Mahlo.Residence.Containment
import SPT.Mahlo.Residence.Containment.Discriminator

import SPT.Mahlo.Decoding.Reindexing

import SPT.Mahlo.Terminal

import SPT.Mahlo.Setzer
