{-# OPTIONS --safe --without-K --no-projection-like #-}

module SPT.MartinLof.Soundness where

-- Soundness of the core theory (Theory) in its models (`soundness`), and
-- its consistency (`consistency`). The theory's constants are univalence
-- and the ambient Mahlo rule at every level. A model of the theory is a
-- model (Model) whose constant univalence l has the value of univalence
-- at l as type (`univalent`), and whose constant mahlo l has the value of
-- Mahlo (Ambient.formers l) as type (`reflecting`), the values computed
-- by the interpretation (Soundness/Interpretation); so every constant
-- has the value of its statement as type (`statements`).
--
-- In such a model every derivable judgment is valid (`Valid`): its
-- context is valid, and its terms have stable values whose types are the
-- values of their types. A derivation is a closed tree over the
-- rules of the theory, so soundness is fold (Foundation.Tree.Fold)
-- along the validity of the rules (`validity`): a node is a block with a
-- rule of it, valid by the block's soundness (Soundness/) at the validity
-- of its premises (`valid`). If no closed term of the model has the empty
-- type, the theory derives no closed term of 0: the value of its term
-- would be one.

open import SPT.Base
import SPT.Foundation.Signature.Sum as Sig
open import SPT.Foundation.Tree using (Op; Pos; boundary)
open import SPT.Foundation.Tree.Fold using (Algebra; fold)
import SPT.MartinLof.Formers as Formers
import SPT.MartinLof.Mahlo as Mahlo
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Judgment using (Judgment; ∅; term)
open import SPT.MartinLof.Model using (Model)
open import SPT.MartinLof.Model.Empty using (Empty)
open import SPT.MartinLof.Model.Russell using (Russell)
import SPT.MartinLof.Soundness.Constant as Constants
import SPT.MartinLof.Soundness.Empty as Nothing
import SPT.MartinLof.Soundness.Identity as Paths
import SPT.MartinLof.Soundness.Interpretation as Interpretation
import SPT.MartinLof.Soundness.Lift as Lifting
import SPT.MartinLof.Soundness.Natural as Numbers
import SPT.MartinLof.Soundness.Pi as Products
import SPT.MartinLof.Soundness.Sigma as Pairs
import SPT.MartinLof.Soundness.Structural as Structural
import SPT.MartinLof.Soundness.Subuniverse as Subuniverses
import SPT.MartinLof.Soundness.Sum as Sums
import SPT.MartinLof.Soundness.Unit as One
import SPT.MartinLof.Soundness.WellFounded as Trees
import SPT.MartinLof.Theory as Theory
import SPT.MartinLof.Univalence as Univalence

module _ {ℓ : Level} (M : Model ℓ Theory.Constant) (let open Model M)
  (let ◇ = Russell.◇ base)
  (let type-of = Russell.type-of base)
  (let meaning = Interpretation.⟦_⟧ base lift-structure pi-structure
                   sigma-structure identity-structure tree-structure
                   empty-structure unit-structure sum-structure
                   natural-structure subuniverse-operations
                     subuniverse-structure constant)
  (let Valid = Interpretation.Valid base lift-structure pi-structure
                 sigma-structure identity-structure tree-structure
                 empty-structure unit-structure sum-structure
                 natural-structure subuniverse-operations subuniverse-structure
                   constant)
  (univalent :
     (l : ℕ)
     → type-of (constant (Theory.univalence l))
       ＝ meaning (Univalence.univalence l) ◇ [])
  (reflecting :
     (l : ℕ)
     → type-of (constant (Theory.mahlo l)) ＝ meaning (Mahlo.mahlo l) ◇ [])
  where

  ----------------------------------------------------------------------
  -- The constants

  -- Each constant has the value of its statement as type.
  statements :
    (c : Theory.Constant)
    → type-of (constant c) ＝ meaning (Theory.statement c) ◇ []
  statements (Theory.univalence l) = univalent l
  statements (Theory.mahlo l) = reflecting l

  ----------------------------------------------------------------------
  -- The rules

  -- A rule of the theory, a block with a rule of the block, is valid at
  -- the validity of its premises.
  valid :
    {j : Judgment Theory.Constant} (o : Op (Sig.to-signature Theory.rules) j)
    → ((p : Pos (Sig.to-signature Theory.rules) o)
       → Valid (boundary (Sig.to-signature Theory.rules) o p))
    → Valid j
  valid (Theory.structural , r) h =
    Structural.sound base lift-structure pi-structure sigma-structure
      identity-structure tree-structure empty-structure unit-structure
      sum-structure natural-structure subuniverse-operations
        subuniverse-structure constant r h
  valid (Theory.universe , r) h =
    Lifting.universe-sound base lift-structure pi-structure sigma-structure
      identity-structure tree-structure empty-structure unit-structure
      sum-structure natural-structure subuniverse-operations
        subuniverse-structure constant r h
  valid (Theory.lift , r) h =
    Lifting.sound base lift-structure pi-structure sigma-structure
      identity-structure tree-structure empty-structure unit-structure
      sum-structure natural-structure subuniverse-operations
        subuniverse-structure constant r h
  valid (Theory.pi , r) h =
    Products.sound base lift-structure pi-structure sigma-structure
      identity-structure tree-structure empty-structure unit-structure
      sum-structure natural-structure subuniverse-operations
        subuniverse-structure constant r h
  valid (Theory.sigma , r) h =
    Pairs.sound base lift-structure pi-structure sigma-structure
      identity-structure tree-structure empty-structure unit-structure
      sum-structure natural-structure subuniverse-operations
        subuniverse-structure constant r h
  valid (Theory.identity , r) h =
    Paths.sound base lift-structure pi-structure sigma-structure
      identity-structure tree-structure empty-structure unit-structure
      sum-structure natural-structure subuniverse-operations
        subuniverse-structure constant r h
  valid (Theory.well-founded , r) h =
    Trees.sound base lift-structure pi-structure sigma-structure
      identity-structure tree-structure empty-structure unit-structure
      sum-structure natural-structure subuniverse-operations
        subuniverse-structure constant r h
  valid (Theory.empty , r) h =
    Nothing.sound base lift-structure pi-structure sigma-structure
      identity-structure tree-structure empty-structure unit-structure
      sum-structure natural-structure subuniverse-operations
        subuniverse-structure constant r h
  valid (Theory.unit , r) h =
    One.sound base lift-structure pi-structure sigma-structure
      identity-structure tree-structure empty-structure unit-structure
      sum-structure natural-structure subuniverse-operations
        subuniverse-structure constant r h
  valid (Theory.sum , r) h =
    Sums.sound base lift-structure pi-structure sigma-structure
      identity-structure tree-structure empty-structure unit-structure
      sum-structure natural-structure subuniverse-operations
        subuniverse-structure constant r h
  valid (Theory.natural , r) h =
    Numbers.sound base lift-structure pi-structure sigma-structure
      identity-structure tree-structure empty-structure unit-structure
      sum-structure natural-structure subuniverse-operations
        subuniverse-structure constant r h
  valid (Theory.subuniverse , r) h =
    Subuniverses.sound base lift-structure pi-structure sigma-structure
      identity-structure tree-structure empty-structure unit-structure
      sum-structure natural-structure subuniverse-operations
        subuniverse-structure constant r h
  valid (Theory.constants , r) h =
    Constants.sound base lift-structure pi-structure sigma-structure
      identity-structure tree-structure empty-structure unit-structure
      sum-structure natural-structure
      subuniverse-operations subuniverse-structure constant Theory.axioms
        statements r h

  -- The validity of the rules, as an algebra for fold; a closed
  -- history has no holes.
  validity :
    Algebra (Sig.to-signature Theory.rules)
      (λ _ → 𝟘) Valid
  validity = record { on-hole = λ () ; on-node = valid }

  ----------------------------------------------------------------------
  -- Soundness and consistency

  -- Every derivable judgment is valid.
  soundness : {j : Judgment Theory.Constant} → Theory.Derivation j → Valid j
  soundness = fold validity

  -- If no closed term of the model has the empty type, the theory derives
  -- no closed term of 0.
  consistency :
    ((t : Russell.Tm base ◇)
     → type-of t ＝ Empty.empty empty-structure → 𝟘)
    → (t : Raw.Expression Theory.Constant 0)
    → Theory.Derivation (term ∅ 0 t Formers.empty) → 𝟘
  consistency none t d =
    let _[_] = Russell._[_] base
        empty = Empty.empty empty-structure
        (_ , Tt) = soundness d
        tt = Interpretation.Typed.term-type Tt
        e = ap (λ σ → empty [ σ ])
                (Russell.ε-unique base (Russell.id base) ⁻¹) ∙
              Russell.[id] base empty
    in none (meaning t ◇ []) (tt ∙ e)
