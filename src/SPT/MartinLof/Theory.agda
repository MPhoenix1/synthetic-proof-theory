{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Theory where

-- The core theory: Martin-Löf type theory with Russell universes at closed
-- levels, Lift, Π, Σ, identity types, W, 0, 1, + and ℕ, and Kubánek's
-- Mahlo subuniverses, with univalence and the ambient Mahlo rule at every
-- level. These two rules are its only constants: `univalence l` and
-- `mahlo l` (`Constant`), each a closed type at level suc l (`level`,
-- `statement`, `axioms`). The statements are TypeTopology's is-univalent
-- (Univalence) and SPT's Mahlo (Ambient.formers ℓ) (Mahlo).
--
-- Its rule blocks are combined into one signature over its judgments
-- by the choice-retaining coproduct of signatures
-- (Foundation.Signature.Coproduct). A rule of the theory is a block
-- (`Block`) with a rule of that block (`blocks`, `rules`): the structural
-- rules, the universes, Lift, Π, Σ, identity types, W, 0, 1, +, ℕ, the
-- subuniverses, and the constants. A derivation of a judgment is a closed
-- history of the typing generation of these rules (`Derivation`,
-- Judgment's `Derivation`).

open import SPT.Base hiding (lift)
import SPT.Foundation.Signature.Coproduct as Coproduct
import SPT.Foundation.Signature.Sum as Sig
import SPT.MartinLof.Judgment as Judgment
open import SPT.MartinLof.Judgment using (Judgment)
import SPT.MartinLof.Mahlo as Mahlo
import SPT.MartinLof.Raw as Raw
import SPT.MartinLof.Rules.Constant as Constants
import SPT.MartinLof.Rules.Empty as Empty
import SPT.MartinLof.Rules.Identity as Identity
import SPT.MartinLof.Rules.Lift as Lift
import SPT.MartinLof.Rules.Natural as Natural
import SPT.MartinLof.Rules.Pi as Pi
import SPT.MartinLof.Rules.Sigma as Sigma
import SPT.MartinLof.Rules.Subuniverse as Subuniverses
import SPT.MartinLof.Rules.Sum as Sum
import SPT.MartinLof.Rules.Unit as Unit
import SPT.MartinLof.Rules.Universe as Universe
import SPT.MartinLof.Rules.WellFounded as WellFounded
import SPT.MartinLof.Structural as Structural
import SPT.MartinLof.Univalence as Univalence

------------------------------------------------------------------------
-- The constants

-- Univalence and the ambient Mahlo rule, of the universe at each level.
data Constant : Set where
  univalence mahlo : ℕ → Constant

level : Constant → ℕ
level (univalence l) = suc l
level (mahlo l) = suc l

statement : Constant → Raw.Expression Constant 0
statement (univalence l) = Univalence.univalence l
statement (mahlo l) = Mahlo.mahlo l

axioms : Constants.Axioms Constant
axioms = record { level = level ; statement = statement }

------------------------------------------------------------------------
-- The rules

data Block : Set where
  structural universe lift pi sigma identity well-founded : Block
  empty unit sum natural subuniverse constants : Block

blocks : Block → Sig.Signature-Over (Judgment Constant) lzero lzero
blocks structural = Structural.rules Constant
blocks universe = Universe.rules Constant
blocks lift = Lift.rules Constant
blocks pi = Pi.rules Constant
blocks sigma = Sigma.rules Constant
blocks identity = Identity.rules Constant
blocks well-founded = WellFounded.rules Constant
blocks empty = Empty.rules Constant
blocks unit = Unit.rules Constant
blocks sum = Sum.rules Constant
blocks natural = Natural.rules Constant
blocks subuniverse = Subuniverses.rules Constant
blocks constants = Constants.rules Constant axioms

rules : Sig.Signature-Over (Judgment Constant) lzero lzero
rules = Coproduct.coproduct-signature-over Block blocks

Derivation : Judgment Constant → Set
Derivation j = Judgment.Derivation Constant rules j
