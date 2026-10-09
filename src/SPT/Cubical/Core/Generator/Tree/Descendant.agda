{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.Generator.Tree.Descendant where

-- Proper descendants in closed trees: Descendant is the transitive closure
-- of HistoryChild, keeping every child witness along the route.  It is
-- transitive (descendant-trans), the least transitive relation containing
-- HistoryChild (descendant-least), and well founded (descendant-wf).

open import Agda.Primitive using (Level; _⊔_)
open import Data.Product using (_,_)

open import SPT.Cubical.Core.WellFounded using
  (Acc; acc; WellFounded; predecessorAcc)
open import SPT.Cubical.Core.Generator.Signature using (Signature)
open import SPT.Cubical.Core.Generator.Tree using
  (Judgment; Op; Pos; boundary; History; hole; node)
open import SPT.Cubical.Core.Generator.Tree.Child using
  (HistoryNode; HistoryChild; node-child)

------------------------------------------------------------------------
-- Routes of children

-- Writing c <₁ p for HistoryChild c p and c < p for Descendant c p:
--
--      c <₁ p                   m <₁ p    c < m
--     -------- immediate       ----------------- nested
--      c < p                         c < p
--
-- A witness is a nonempty route of children from p down to c; distinct
-- routes between the same nodes are not identified.

data Descendant
    {ℓj ℓo ℓp : Level}
    {signature : Signature ℓj ℓo ℓp}
    : HistoryNode signature
    → HistoryNode signature
    → Set (ℓj ⊔ ℓo ⊔ ℓp)
  where
  immediate :
      ∀ {child parent}
    → HistoryChild {signature = signature} child parent
    → Descendant child parent

  nested :
      ∀ {child middle parent}
    → HistoryChild {signature = signature} middle parent
    → Descendant child middle
    → Descendant child parent

child→descendant :
    ∀ {ℓj ℓo ℓp : Level}
      {signature : Signature ℓj ℓo ℓp}
      {child parent : HistoryNode signature}
  → HistoryChild child parent
  → Descendant child parent
child→descendant =
  immediate

------------------------------------------------------------------------
-- Transitivity and leastness

-- a < b → b < c → a < c, by concatenating the two routes.

descendant-trans :
    ∀ {ℓj ℓo ℓp : Level}
      {signature : Signature ℓj ℓo ℓp}
      {smaller middle larger : HistoryNode signature}
  → Descendant smaller middle
  → Descendant middle larger
  → Descendant smaller larger
descendant-trans smaller<middle
    (immediate middle<larger) =
  nested middle<larger smaller<middle
descendant-trans smaller<middle
    (nested next<larger middle<next) =
  nested next<larger
    (descendant-trans smaller<middle middle<next)

-- Descendant is the least transitive relation containing HistoryChild:
--
--   HistoryChild ⊆ R    R transitive
--   --------------------------------
--          Descendant ⊆ R.

descendant-least :
    ∀ {ℓj ℓo ℓp ℓr : Level}
      {signature : Signature ℓj ℓo ℓp}
      {relation :
        HistoryNode signature → HistoryNode signature → Set ℓr}
  → (∀ {child parent}
      → HistoryChild child parent
      → relation child parent)
  → (∀ {smaller middle larger}
      → relation smaller middle
      → relation middle larger
      → relation smaller larger)
  → ∀ {smaller larger}
  → Descendant smaller larger
  → relation smaller larger
descendant-least
    contains-history-child
    transitive-relation
    (immediate child<parent) =
  contains-history-child child<parent
descendant-least
    contains-history-child
    transitive-relation
    (nested middle<parent smaller<middle) =
  transitive-relation
    (descendant-least
      contains-history-child
      transitive-relation
      smaller<middle)
    (contains-history-child middle<parent)

------------------------------------------------------------------------
-- Well-foundedness

-- history-acc h : Acc Descendant (j , h), by induction on h: a route of
-- length one ends at a child, and a longer one lies below a child.

mutual
  history-acc :
      ∀ {ℓj ℓo ℓp : Level}
        {signature : Signature ℓj ℓo ℓp}
        {judgment : Judgment signature}
    → (history : History signature judgment)
    → Acc Descendant (judgment , history)
  history-acc (hole ())
  history-acc (node operation children) =
    acc (smaller operation children)

  smaller :
      ∀ {ℓj ℓo ℓp : Level}
        {signature : Signature ℓj ℓo ℓp}
        {judgment : Judgment signature}
    → (operation : Op signature judgment)
    → (children :
        (position : Pos signature operation)
      → History signature (boundary signature operation position))
    → (predecessor : HistoryNode signature)
    → Descendant
        predecessor (judgment , node operation children)
    → Acc Descendant predecessor
  smaller operation children
      .(_ , children position)
      (immediate (node-child position)) =
    history-acc (children position)
  smaller operation children predecessor
      (nested
        (node-child position)
        predecessor<child) =
    predecessorAcc
      (history-acc (children position))
      predecessor
      predecessor<child

node-acc :
    ∀ {ℓj ℓo ℓp : Level}
      {signature : Signature ℓj ℓo ℓp}
    → (point : HistoryNode signature)
    → Acc Descendant point
node-acc (judgment , history) =
  history-acc history

-- Descendant is well founded.

descendant-wf :
    ∀ {ℓj ℓo ℓp : Level}
      {signature : Signature ℓj ℓo ℓp}
  → WellFounded (Descendant {signature = signature})
descendant-wf =
  node-acc
