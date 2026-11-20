{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Tree.Descendant where

-- A descendant of a node in a closed tree lies below it along a nonempty route
-- of children. Writing `c <₁ p` for `HistoryChild c p` and `c < p` for
-- `Descendant c p`:
--
--    c <₁ p                    m <₁ p    c < m
--   -------- immediate        ---------------- nested
--    c < p                          c < p
--
-- A witness keeps every child along the route; distinct routes between the same
-- nodes are not identified. `Descendant` is transitive, the least transitive
-- relation containing `HistoryChild`, and well-founded: a route of length one
-- ends at a child, and a longer one lies below a child.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Accessibility using
  (is-accessible; acc; is-well-founded; predecessors-are-accessible)
open import SPT.Cubical.Foundation.WellFounded.Subrelation using (_⊆_)
open import SPT.Cubical.Foundation.Tree
open import SPT.Cubical.Foundation.Tree.Child using
  (HistoryNode; HistoryChild; node-child)

module _ {ℓj ℓo ℓp : Level} {S : Signature ℓj ℓo ℓp} where

  data Descendant : HistoryNode S → HistoryNode S → Set (ℓj ⊔ ℓo ⊔ ℓp)
    where
    immediate : {child parent : HistoryNode S} →
      HistoryChild child parent → Descendant child parent
    nested : {child middle parent : HistoryNode S} →
      HistoryChild middle parent → Descendant child middle →
      Descendant child parent

------------------------------------------------------------------------
-- Transitivity

  -- The two routes are concatenated.

  child→descendant : {child parent : HistoryNode S} →
    HistoryChild child parent → Descendant child parent
  child→descendant = immediate

  descendant-trans : {smaller middle larger : HistoryNode S} →
    Descendant smaller middle → Descendant middle larger →
    Descendant smaller larger
  descendant-trans smaller<middle (immediate middle<larger) =
    nested middle<larger smaller<middle
  descendant-trans smaller<middle (nested next<larger middle<next) =
    nested next<larger (descendant-trans smaller<middle middle<next)

------------------------------------------------------------------------
-- Well-foundedness

  mutual
    history-acc : {judgment : Judgment S} (history : History S judgment) →
      is-accessible Descendant (judgment , history)
    history-acc (hole ())
    history-acc (node operation children) =
      acc (smaller operation children)

    smaller : {judgment : Judgment S} (operation : Op S judgment)
      (children : (position : Pos S operation) →
        History S (boundary S operation position))
      (predecessor : HistoryNode S) →
      Descendant predecessor (judgment , node operation children) →
      is-accessible Descendant predecessor
    smaller operation children
      .(boundary S operation position , children position)
      (immediate (node-child position)) =
      history-acc (children position)
    smaller operation children predecessor
      (nested (node-child position) predecessor<child) =
      predecessors-are-accessible (history-acc (children position))
        predecessor predecessor<child

  node-acc : (point : HistoryNode S) → is-accessible Descendant point
  node-acc (judgment , history) = history-acc history

  descendant-wf : is-well-founded Descendant
  descendant-wf = node-acc

------------------------------------------------------------------------
-- The least transitive relation containing HistoryChild

--   HistoryChild ⊆ R    R transitive
--   --------------------------------
--           Descendant ⊆ R

module _ {ℓj ℓo ℓp ℓr : Level} {S : Signature ℓj ℓo ℓp}
  {relation : HistoryNode S → HistoryNode S → Set ℓr} where

  descendant-least : HistoryChild ⊆ relation →
    ({smaller middle larger : HistoryNode S} →
      relation smaller middle → relation middle larger →
      relation smaller larger) →
    Descendant ⊆ relation
  descendant-least contains transitive (immediate child<parent) =
    contains child<parent
  descendant-least contains transitive
    (nested middle<parent smaller<middle) =
    transitive (descendant-least contains transitive smaller<middle)
      (contains middle<parent)
