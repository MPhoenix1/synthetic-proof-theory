{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.Generator.Linear.Exponential.Order where

-- The lexicographic order on exponential normal forms, read directly from
-- the final node of each history (`Snoc`) rather than through `prepend`.
-- Transitivity, and well-foundedness from well-foundedness of the exponent
-- order and accessibility of the admissible coefficients.

open import Agda.Primitive using (Level; _⊔_)
open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)

open import SPT.Cubical.Core.WellFounded using
  (Acc; acc; WellFounded; acc-ind)
open import SPT.Cubical.Core.Generator.Linear.Signature using
  ( unary-position
  ; sequentialSignature
  ; sequential-seed
  ; sequential-next
  )
open import SPT.Cubical.Core.Generator.Linear.History using
  (SequentialHistory)
open import SPT.Cubical.Core.Generator.Tree using
  (History; Pos; boundary; hole; node)
import SPT.Cubical.Core.Generator.Linear.Exponential as Exponential
import SPT.Cubical.Core.WellFounded.Subrelation as Subrelation

------------------------------------------------------------------------
-- The order on one layer

module Layer
    {ℓe ℓc ℓg ℓre ℓrc : Level}
    (Exponent : Set ℓe)
    (Coefficient : Set ℓc)
    (Good : Coefficient → Set ℓg)
    (_≺e_ : Exponent → Exponent → Set ℓre)
    (_≺c_ : Coefficient → Coefficient → Set ℓrc)
  where

  module Terms = Exponential.Layer
    Exponent Coefficient Good _≺e_ _≺c_

  private
    ℓs = ℓe ⊔ ℓc
    ℓstep = ℓe ⊔ ℓc ⊔ ℓg ⊔ ℓre
    ℓterm = ℓe ⊔ ℓc ⊔ ℓg ⊔ ℓre
    ℓorder = ℓe ⊔ ℓc ⊔ ℓg ⊔ ℓre ⊔ ℓrc

  -- The child function stored at a successor node.
  Children :
      ∀ {n : ℕ}
        {x : Terms.State n}
        {y : Terms.State (suc n)}
    → Terms.Step n x y
    → Set (ℓs ⊔ ℓstep)
  Children edge =
    (position :
      Pos
        (sequentialSignature Terms.Step Terms.empty-state)
        (sequential-next edge)) →
      History
        (sequentialSignature Terms.Step Terms.empty-state)
        (boundary
          (sequentialSignature Terms.Step Terms.empty-state)
          (sequential-next edge)
          position)

  SeedChildren : Set (ℓs ⊔ ℓstep)
  SeedChildren =
    (position :
      Pos
        (sequentialSignature Terms.Step Terms.empty-state)
        sequential-seed) →
      History
        (sequentialSignature Terms.Step Terms.empty-state)
        (boundary
          (sequentialSignature Terms.Step Terms.empty-state)
          sequential-seed
          position)

  ----------------------------------------------------------------------
  -- Views of the final node

  -- `Empty` views a history consisting of the seed node alone.
  data Empty : Terms.Exponential → Set ℓterm where
    empty-node :
        (children : SeedChildren)
      → Empty
          (Terms.exponential
            zero
            Terms.empty-state
            (node sequential-seed children))

  -- `Snoc head coefficient tail whole` views the final node of `whole`: it
  -- prepends (head, coefficient) to `tail`, and `tail` is the child stored at
  -- that node.
  data Snoc :
      Exponent → Coefficient →
      Terms.Exponential → Terms.Exponential →
      Set ℓterm
    where
    first-node :
        (head : Exponent)
        (coefficient : Coefficient)
        (good : Good coefficient)
        {children : Children (Terms.first-step head coefficient good)}
      → Snoc
          head coefficient
          (Terms.exponential
            zero
            Terms.empty-state
            (children unary-position))
          (Terms.exponential
            (suc zero)
            (Terms.head-state head coefficient)
            (node
              (sequential-next
                (Terms.first-step head coefficient good))
              children))

    later-node :
        {n : ℕ}
        (head tail-head : Exponent)
        (coefficient tail-coefficient : Coefficient)
        (good : Good coefficient)
        (decrease : tail-head ≺e head)
        {children : Children
          (Terms.prepend-step
            {n = n}
            head tail-head coefficient tail-coefficient
            good decrease)}
      → Snoc
          head coefficient
          (Terms.exponential
            (suc n)
            (Terms.head-state tail-head tail-coefficient)
            (children unary-position))
          (Terms.exponential
            (suc (suc n))
            (Terms.head-state head coefficient)
            (node
              (sequential-next
                (Terms.prepend-step
                  head tail-head coefficient tail-coefficient
                  good decrease))
              children))

  data Shape (term : Terms.Exponential) : Set ℓterm where
    empty-shape : Empty term → Shape term
    snoc-shape :
        {head : Exponent}
        {coefficient : Coefficient}
        {tail : Terms.Exponential}
      → Snoc head coefficient tail term
      → Shape term

  shape : (term : Terms.Exponential) → Shape term
  shape (Terms.exponential n endpoint (hole ()))
  shape
      (Terms.exponential
        zero
        Terms.empty-state
        (node sequential-seed children)) =
    empty-shape (empty-node children)
  shape
      (Terms.exponential
        (suc zero)
        (Terms.head-state head coefficient)
        (node
          (sequential-next
            (Terms.first-step .head .coefficient good))
          children)) =
    snoc-shape
      (first-node head coefficient good {children = children})
  shape
      (Terms.exponential
        (suc (suc n))
        (Terms.head-state head coefficient)
        (node
          (sequential-next
            (Terms.prepend-step
              .head tail-head .coefficient tail-coefficient
              good decrease))
          children)) =
    snoc-shape
      (later-node
        head tail-head coefficient tail-coefficient
        good decrease
        {children = children})

  empty-view :
      (history : SequentialHistory
        {State = Terms.State}
        {Step = Terms.Step}
        Terms.empty-state zero Terms.empty-state)
    → Empty (Terms.exponential zero Terms.empty-state history)
  empty-view (hole ())
  empty-view (node sequential-seed children) =
    empty-node children

  -- The final node of a normal form built by `prepend`.
  prepend-snoc :
      (head : Exponent)
      (coefficient : Coefficient)
      (good : Good coefficient)
      (tail : Terms.Exponential)
      (below : Terms.TailBelow head tail)
    → Snoc
        head coefficient tail
        (Terms.prepend head coefficient good tail below)
  prepend-snoc head coefficient good
      .(Terms.exponential zero Terms.empty-state history)
      below@(Terms.below-empty history)
      with shape
        (Terms.prepend
          head coefficient good
          (Terms.exponential zero Terms.empty-state history)
          below)
  ... | snoc-shape
      (first-node
        .head .coefficient .good
        {children = children}) =
    first-node
      head coefficient good
      {children = children}
  prepend-snoc head coefficient good
      .(Terms.exponential
        (suc n)
        (Terms.head-state tail-head tail-coefficient)
        history)
      below@(Terms.below-head {n = n}
        tail-head tail-coefficient history decrease)
      with shape
        (Terms.prepend
          head coefficient good
          (Terms.exponential
            (suc n)
            (Terms.head-state tail-head tail-coefficient)
            history)
          below)
  ... | snoc-shape
      (later-node
        .head .tail-head .coefficient .tail-coefficient
        .good .decrease
        {children = children}) =
    later-node
      head tail-head coefficient tail-coefficient
      good decrease
      {children = children}

  zero-empty : Empty Terms.zeroᴱ
  zero-empty = empty-view (Terms.support Terms.zeroᴱ)

  singleton-snoc :
      (head : Exponent)
      (coefficient : Coefficient)
      (good : Good coefficient)
    → Snoc
        head coefficient Terms.zeroᴱ
        (Terms.singleton head coefficient good)
  singleton-snoc head coefficient good =
    prepend-snoc
      head coefficient good
      Terms.zeroᴱ
      (Terms.below-empty (Terms.support Terms.zeroᴱ))

  ----------------------------------------------------------------------
  -- The order

  infix 4 _≺ᴱ_

  -- The order is defined on views of the final nodes, so two composable
  -- comparisons share the middle node itself.
  data _≺ᴱ_ : Terms.Exponential → Terms.Exponential → Set ℓorder where
    proper-prefix :
        {left right-tail right : Terms.Exponential}
        {right-head : Exponent}
        {right-coefficient : Coefficient}
      → Empty left
      → Snoc right-head right-coefficient right-tail right
      → left ≺ᴱ right

    first-difference :
        {left-tail left right-tail right : Terms.Exponential}
        {left-head right-head : Exponent}
        {left-coefficient right-coefficient : Coefficient}
      → Snoc left-head left-coefficient left-tail left
      → Snoc right-head right-coefficient right-tail right
      → Terms.PairLess
          left-head left-coefficient
          right-head right-coefficient
      → left ≺ᴱ right

    common-head :
        {left-tail left right-tail right : Terms.Exponential}
        {head : Exponent}
        {coefficient : Coefficient}
      → Snoc head coefficient left-tail left
      → Snoc head coefficient right-tail right
      → left-tail ≺ᴱ right-tail
      → left ≺ᴱ right

  zero-below-singleton :
      (head : Exponent)
      (coefficient : Coefficient)
      (good : Good coefficient)
    → Terms.zeroᴱ ≺ᴱ Terms.singleton head coefficient good
  zero-below-singleton head coefficient good =
    proper-prefix
      zero-empty
      (singleton-snoc head coefficient good)

  -- Removing the final node decreases the order.
  tail-below :
      {head : Exponent}
      {coefficient : Coefficient}
      {tail whole : Terms.Exponential} →
      Snoc head coefficient tail whole →
      tail ≺ᴱ whole
  tail-below
      final-node@(first-node
        head coefficient good {children = children}) =
    proper-prefix
      (empty-view (children unary-position))
      final-node
  tail-below {tail = tail}
      final-node@(later-node {n = n}
        head tail-head coefficient tail-coefficient
        good decrease {children = children})
      with children unary-position
  ... | hole ()
  ... | node
      (sequential-next
        (Terms.first-step
          .tail-head .tail-coefficient tail-good))
      tail-children =
    first-difference
      (first-node
        tail-head tail-coefficient tail-good
        {children = tail-children})
      final-node
      (Terms.Pair.earlier
        {x = tail-coefficient} {y = coefficient}
        decrease)
  ... | node
      (sequential-next
        (Terms.prepend-step
          .tail-head prior-head
          .tail-coefficient prior-coefficient
          tail-good prior-decrease))
      tail-children =
    first-difference
      (later-node
        tail-head prior-head
        tail-coefficient prior-coefficient
        tail-good prior-decrease
        {children = tail-children})
      final-node
      (Terms.Pair.earlier
        {x = tail-coefficient} {y = coefficient}
        decrease)

  -- The comparison of Exponential, on forms presented by `prepend`, is
  -- contained in this order.
  from-formation :
    Subrelation.SubRel Terms._≺ᴱ_ _≺ᴱ_
  from-formation
      (Terms.proper-prefix
        left-empty
        right-head right-coefficient right-good
        right-tail right-below) =
    proper-prefix
      (empty-view left-empty)
      (prepend-snoc
        right-head right-coefficient right-good
        right-tail right-below)
  from-formation
      (Terms.first-difference
        left-good right-good
        left-below right-below difference) =
    first-difference
      (prepend-snoc _ _ left-good _ left-below)
      (prepend-snoc _ _ right-good _ right-below)
      difference
  from-formation
      (Terms.common-head
        head coefficient
        left-good right-good
        left-below right-below suffix) =
    common-head
      (prepend-snoc
        head coefficient left-good _ left-below)
      (prepend-snoc
        head coefficient right-good _ right-below)
      (from-formation suffix)

  empty-snoc-absurd :
      {term tail : Terms.Exponential}
      {head : Exponent}
      {coefficient : Coefficient}
    → Empty term
    → Snoc head coefficient tail term
    → ⊥ {ℓterm}
  empty-snoc-absurd (empty-node children) ()

  empty-no-predecessor :
      {left right : Terms.Exponential}
    → Empty right
    → left ≺ᴱ right
    → ⊥ {ℓorder}
  empty-no-predecessor right-empty
      (proper-prefix left-empty right-node) =
    ⊥-elim (empty-snoc-absurd right-empty right-node)
  empty-no-predecessor right-empty
      (first-difference left-node right-node difference) =
    ⊥-elim (empty-snoc-absurd right-empty right-node)
  empty-no-predecessor right-empty
      (common-head left-node right-node suffix) =
    ⊥-elim (empty-snoc-absurd right-empty right-node)

  empty-accessible :
      {term : Terms.Exponential}
    → Empty term
    → Acc _≺ᴱ_ term
  empty-accessible empty =
    acc λ predecessor decrease →
      ⊥-elim (empty-no-predecessor empty decrease)

  -- Transitivity, by cases on the views of the shared middle term.
  trans :
      (∀ {left middle right} →
        left ≺e middle → middle ≺e right → left ≺e right)
    → (∀ {left middle right} →
        left ≺c middle → middle ≺c right → left ≺c right)
    → ∀ {left middle right}
    → left ≺ᴱ middle
    → middle ≺ᴱ right
    → left ≺ᴱ right
  trans trans-exponent trans-coefficient
      (proper-prefix left-empty middle-node)
      (proper-prefix middle-empty right-node) =
    ⊥-elim (empty-snoc-absurd middle-empty middle-node)
  trans trans-exponent trans-coefficient
      (proper-prefix left-empty middle-node)
      (first-difference middle-node′ right-node difference) =
    proper-prefix left-empty right-node
  trans trans-exponent trans-coefficient
      (proper-prefix left-empty middle-node)
      (common-head middle-node′ right-node suffix) =
    proper-prefix left-empty right-node
  trans trans-exponent trans-coefficient
      (first-difference left-node middle-node difference)
      (proper-prefix middle-empty right-node) =
    ⊥-elim (empty-snoc-absurd middle-empty middle-node)
  trans trans-exponent trans-coefficient
      (common-head left-node middle-node prefix)
      (proper-prefix middle-empty right-node) =
    ⊥-elim (empty-snoc-absurd middle-empty middle-node)

  trans trans-exponent trans-coefficient
      (first-difference
        left-node
        (first-node
          middle-head middle-coefficient middle-good
          {children = middle-children})
        left-difference)
      (first-difference
        (first-node
          .middle-head .middle-coefficient .middle-good
          {children = .middle-children})
        right-node
        right-difference) =
    first-difference
      left-node right-node
      (Terms.pair-trans
        trans-exponent trans-coefficient
        left-difference right-difference)
  trans trans-exponent trans-coefficient
      (first-difference
        left-node
        (later-node
          middle-head middle-tail-head
          middle-coefficient middle-tail-coefficient
          middle-good middle-decrease
          {children = middle-children})
        left-difference)
      (first-difference
        (later-node
          .middle-head .middle-tail-head
          .middle-coefficient .middle-tail-coefficient
          .middle-good .middle-decrease
          {children = .middle-children})
        right-node
        right-difference) =
    first-difference
      left-node right-node
      (Terms.pair-trans
        trans-exponent trans-coefficient
        left-difference right-difference)

  trans trans-exponent trans-coefficient
      (first-difference
        left-node
        (first-node
          middle-head middle-coefficient middle-good
          {children = middle-children})
        difference)
      (common-head
        (first-node
          .middle-head .middle-coefficient .middle-good
          {children = .middle-children})
        right-node
        suffix) =
    first-difference left-node right-node difference
  trans trans-exponent trans-coefficient
      (first-difference
        left-node
        (later-node
          middle-head middle-tail-head
          middle-coefficient middle-tail-coefficient
          middle-good middle-decrease
          {children = middle-children})
        difference)
      (common-head
        (later-node
          .middle-head .middle-tail-head
          .middle-coefficient .middle-tail-coefficient
          .middle-good .middle-decrease
          {children = .middle-children})
        right-node
        suffix) =
    first-difference left-node right-node difference

  trans trans-exponent trans-coefficient
      (common-head
        left-node
        (first-node
          middle-head middle-coefficient middle-good
          {children = middle-children})
        prefix)
      (first-difference
        (first-node
          .middle-head .middle-coefficient .middle-good
          {children = .middle-children})
        right-node
        difference) =
    first-difference left-node right-node difference
  trans trans-exponent trans-coefficient
      (common-head
        left-node
        (later-node
          middle-head middle-tail-head
          middle-coefficient middle-tail-coefficient
          middle-good middle-decrease
          {children = middle-children})
        prefix)
      (first-difference
        (later-node
          .middle-head .middle-tail-head
          .middle-coefficient .middle-tail-coefficient
          .middle-good .middle-decrease
          {children = .middle-children})
        right-node
        difference) =
    first-difference left-node right-node difference

  trans trans-exponent trans-coefficient
      (common-head
        left-node
        (first-node
          middle-head middle-coefficient middle-good
          {children = middle-children})
        prefix)
      (common-head
        (first-node
          .middle-head .middle-coefficient .middle-good
          {children = .middle-children})
        right-node
        suffix) =
    common-head
      left-node right-node
      (trans trans-exponent trans-coefficient prefix suffix)
  trans trans-exponent trans-coefficient
      (common-head
        left-node
        (later-node
          middle-head middle-tail-head
          middle-coefficient middle-tail-coefficient
          middle-good middle-decrease
          {children = middle-children})
        prefix)
      (common-head
        (later-node
          .middle-head .middle-tail-head
          .middle-coefficient .middle-tail-coefficient
          .middle-good .middle-decrease
          {children = .middle-children})
        right-node
        suffix) =
    common-head
      left-node right-node
      (trans trans-exponent trans-coefficient prefix suffix)

  ----------------------------------------------------------------------
  -- Accessibility

  HeadAcc : Exponent → Set ℓorder
  HeadAcc head =
    ∀ {coefficient : Coefficient}
      {tail whole : Terms.Exponential} →
      Snoc head coefficient tail whole →
      Acc _≺ᴱ_ whole

  CoefficientAcc : Exponent → Coefficient → Set ℓorder
  CoefficientAcc head coefficient =
    ∀ {tail whole : Terms.Exponential} →
      Snoc head coefficient tail whole →
      Acc _≺ᴱ_ whole

  TailAcc :
      Exponent → Coefficient → Terms.Exponential → Set ℓorder
  TailAcc head coefficient tail =
    ∀ {whole : Terms.Exponential} →
      Snoc head coefficient tail whole →
      Acc _≺ᴱ_ whole

  tail-accessible :
      {head : Exponent}
    → ((lower : Exponent) → lower ≺e head → HeadAcc lower)
    → {coefficient : Coefficient}
      {tail whole : Terms.Exponential}
    → Snoc head coefficient tail whole
    → Acc _≺ᴱ_ tail
  tail-accessible smaller-head
      (first-node head coefficient good {children = children}) =
    empty-accessible
      (empty-view (children unary-position))
  tail-accessible smaller-head
      (later-node {n = n}
        head tail-head coefficient tail-coefficient
        good decrease
        {children = children})
      with children unary-position
  ... | hole ()
  ... | node
      (sequential-next
        (Terms.first-step .tail-head .tail-coefficient tail-good))
      tail-children =
    smaller-head tail-head decrease
      (first-node
        tail-head tail-coefficient tail-good
        {children = tail-children})
  ... | node
      (sequential-next
        (Terms.prepend-step
          .tail-head prior-head
          .tail-coefficient prior-coefficient
          tail-good prior-decrease))
      tail-children =
    smaller-head tail-head decrease
      (later-node
        tail-head prior-head
        tail-coefficient prior-coefficient
        tail-good prior-decrease
        {children = tail-children})

  module AccessibilityProof
      (good-accessible :
        (coefficient : Coefficient) →
        Good coefficient →
        Acc _≺c_ coefficient)
    where

    predecessor :
        {head : Exponent}
        {coefficient : Coefficient}
        {tail whole : Terms.Exponential}
      → ((lower-head : Exponent) →
          lower-head ≺e head →
          HeadAcc lower-head)
      → ((lower-coefficient : Coefficient) →
          lower-coefficient ≺c coefficient →
          CoefficientAcc head lower-coefficient)
      → ((lower-tail : Terms.Exponential) →
          lower-tail ≺ᴱ tail →
          TailAcc head coefficient lower-tail)
      → Snoc head coefficient tail whole
      → (prior : Terms.Exponential)
      → prior ≺ᴱ whole
      → Acc _≺ᴱ_ prior
    predecessor
        smaller-head smaller-coefficient smaller-tail
        (first-node
          head coefficient good
          {children = children})
        prior
        (proper-prefix prior-empty
          (first-node
            .head .coefficient .good
            {children = .children})) =
      empty-accessible prior-empty
    predecessor
        smaller-head smaller-coefficient smaller-tail
        (first-node
          head coefficient good
          {children = children})
        prior
        (first-difference prior-node
          (first-node
            .head .coefficient .good
            {children = .children})
          (Terms.exponent-less decrease)) =
      smaller-head _ decrease prior-node
    predecessor
        smaller-head smaller-coefficient smaller-tail
        (first-node
          head coefficient good
          {children = children})
        prior
        (first-difference prior-node
          (first-node
            .head .coefficient .good
            {children = .children})
          (Terms.coefficient-less .head decrease)) =
      smaller-coefficient _ decrease prior-node
    predecessor
        smaller-head smaller-coefficient smaller-tail
        (first-node
          head coefficient good
          {children = children})
        prior
        (common-head prior-node
          (first-node
            .head .coefficient .good
            {children = .children})
          suffix) =
      smaller-tail _ suffix prior-node

    predecessor
        smaller-head smaller-coefficient smaller-tail
        (later-node
          head tail-head coefficient tail-coefficient
          good support-decrease
          {children = children})
        prior
        (proper-prefix prior-empty
          (later-node
            .head .tail-head .coefficient .tail-coefficient
            .good .support-decrease
            {children = .children})) =
      empty-accessible prior-empty
    predecessor
        smaller-head smaller-coefficient smaller-tail
        (later-node
          head tail-head coefficient tail-coefficient
          good support-decrease
          {children = children})
        prior
        (first-difference prior-node
          (later-node
            .head .tail-head .coefficient .tail-coefficient
            .good .support-decrease
            {children = .children})
          (Terms.exponent-less decrease)) =
      smaller-head _ decrease prior-node
    predecessor
        smaller-head smaller-coefficient smaller-tail
        (later-node
          head tail-head coefficient tail-coefficient
          good support-decrease
          {children = children})
        prior
        (first-difference prior-node
          (later-node
            .head .tail-head .coefficient .tail-coefficient
            .good .support-decrease
            {children = .children})
          (Terms.coefficient-less .head decrease)) =
      smaller-coefficient _ decrease prior-node
    predecessor
        smaller-head smaller-coefficient smaller-tail
        (later-node
          head tail-head coefficient tail-coefficient
          good support-decrease
          {children = children})
        prior
        (common-head prior-node
          (later-node
            .head .tail-head .coefficient .tail-coefficient
            .good .support-decrease
            {children = .children})
          suffix) =
      smaller-tail _ suffix prior-node

    tail-step :
        {head : Exponent}
      → ((lower-head : Exponent) →
          lower-head ≺e head →
          HeadAcc lower-head)
      → {coefficient : Coefficient}
      → ((lower-coefficient : Coefficient) →
          lower-coefficient ≺c coefficient →
          CoefficientAcc head lower-coefficient)
      → (tail : Terms.Exponential)
      → ((lower-tail : Terms.Exponential) →
          lower-tail ≺ᴱ tail →
          TailAcc head coefficient lower-tail)
      → TailAcc head coefficient tail
    tail-step
        smaller-head smaller-coefficient
        tail smaller-tail final-node =
      acc λ prior decrease →
        predecessor
          smaller-head smaller-coefficient smaller-tail
          final-node prior decrease

    tail-ind :
        {head : Exponent}
      → ((lower-head : Exponent) →
          lower-head ≺e head →
          HeadAcc lower-head)
      → {coefficient : Coefficient}
      → ((lower-coefficient : Coefficient) →
          lower-coefficient ≺c coefficient →
          CoefficientAcc head lower-coefficient)
      → (tail : Terms.Exponential)
      → Acc _≺ᴱ_ tail
      → TailAcc head coefficient tail
    tail-ind {head = head}
        smaller-head {coefficient = coefficient}
        smaller-coefficient tail =
      acc-ind
        (TailAcc head coefficient)
        (tail-step smaller-head smaller-coefficient)
        tail

    coefficient-step :
        {head : Exponent}
      → ((lower-head : Exponent) →
          lower-head ≺e head →
          HeadAcc lower-head)
      → (coefficient : Coefficient)
      → ((lower-coefficient : Coefficient) →
          lower-coefficient ≺c coefficient →
          CoefficientAcc head lower-coefficient)
      → CoefficientAcc head coefficient
    coefficient-step smaller-head coefficient smaller-coefficient
        {tail = tail} final-node =
      tail-ind
        smaller-head smaller-coefficient
        tail
        (tail-accessible smaller-head final-node)
        final-node

    coefficient-ind :
        {head : Exponent}
      → ((lower-head : Exponent) →
          lower-head ≺e head →
          HeadAcc lower-head)
      → (coefficient : Coefficient)
      → Acc _≺c_ coefficient
      → CoefficientAcc head coefficient
    coefficient-ind {head = head} smaller-head coefficient =
      acc-ind
        (CoefficientAcc head)
        (coefficient-step smaller-head)
        coefficient

    head-step :
        (head : Exponent)
      → ((lower-head : Exponent) →
          lower-head ≺e head →
          HeadAcc lower-head)
      → HeadAcc head
    head-step head smaller-head
        {coefficient = coefficient}
        final-node@(first-node .head .coefficient good) =
      coefficient-ind
        smaller-head coefficient
        (good-accessible coefficient good)
        final-node
    head-step head smaller-head
        {coefficient = coefficient}
        final-node@(later-node
          .head tail-head .coefficient tail-coefficient
          good support-decrease) =
      coefficient-ind
        smaller-head coefficient
        (good-accessible coefficient good)
        final-node

    head-ind :
        (head : Exponent)
      → Acc _≺e_ head
      → HeadAcc head
    head-ind =
      acc-ind HeadAcc head-step

  -- Well-foundedness: induction on the leading exponent handles a first
  -- difference, accessibility of the coefficient handles a smaller
  -- coefficient at the same exponent, and the tail handles a common head.
  well-founded :
      WellFounded _≺e_
    → ((coefficient : Coefficient) →
        Good coefficient →
        Acc _≺c_ coefficient)
    → WellFounded _≺ᴱ_
  well-founded exponent-wf good-accessible term
      with shape term
  ... | empty-shape empty =
    empty-accessible empty
  ... | snoc-shape final-node =
    AccessibilityProof.head-ind
      good-accessible _ (exponent-wf _) final-node

  formation-well-founded :
      WellFounded _≺e_ →
      ((coefficient : Coefficient) →
        Good coefficient →
        Acc _≺c_ coefficient) →
      WellFounded Terms._≺ᴱ_
  formation-well-founded exponent-wf good-accessible =
    Subrelation.subrel-wf
      from-formation
      (well-founded exponent-wf good-accessible)
