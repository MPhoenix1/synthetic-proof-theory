{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Linear.Exponential.Order where

-- The lexicographic order on exponential normal forms, read directly from the
-- final node of each history rather than through `prepend`. The final node is
-- viewed in two ways: a history that is the seed alone (`Empty`), and a node
-- that prepends a pair to a tail stored as its child (`Snoc`). Every normal
-- form has one of these views (`shape`), and every history at a successor has a
-- `Snoc` view with its tail (`snoc-of`). The children of a node are explicit in
-- its view, and a node built by `prepend` stores the child that `only-child`
-- names, so its view is read off without inspecting the history
-- (`prepend-snoc`).
--
-- The order compares the views: the empty form lies below every nonempty one, a
-- smaller leading pair decides, and equal leading pairs pass to the tails. Two
-- composable comparisons share the middle node itself. Removing the final node
-- decreases the order, and the formation order of `Exponential` is contained in
-- this one (`from-formation`). The order is transitive when the exponent and
-- coefficient orders are, and it is well-founded when the exponent order is and
-- every admissible coefficient is accessible: induction on the leading exponent
-- handles a first difference, accessibility of the coefficient a smaller
-- coefficient at the same exponent, and the tail a common head.

open import SPT.Cubical.Base hiding (length)
open import SPT.Cubical.Foundation.Accessibility using
  (is-accessible; acc; is-well-founded; accessible-induction)
open import SPT.Cubical.Foundation.WellFounded.Subrelation using
  (_⊆_; subrelations-are-well-founded)
open import SPT.Cubical.Foundation.Tree
  using (History; Pos; boundary; hole; node)
open import SPT.Cubical.Foundation.Linear.Signature using
  (unary-position; sequentialSignature; sequential-seed; sequential-next)
open import SPT.Cubical.Foundation.Linear.History using
  (SequentialHistory; only-child)
open import SPT.Cubical.Foundation.Linear.Exponential using
  ( Layer; State; empty-state; head-state; Step; first-step
  ; prepend-step; Exponential; exponential; support; zeroᴱ; TailBelow
  ; below-empty; below-head; prepend; singleton; PairLess; pair-trans
  ; exponent-less; coefficient-less )
import SPT.Cubical.Foundation.Linear.Exponential as Formation

------------------------------------------------------------------------
-- Views of the final node

module _ {ℓe ℓc ℓg ℓre ℓrc : Level} (L : Layer ℓe ℓc ℓg ℓre ℓrc) where

  open Layer L

  Children : {n : ℕ} {x : State L n} {y : State L (suc n)} →
    Step L n x y → Set (ℓe ⊔ ℓc ⊔ ℓg ⊔ ℓre)
  Children edge =
    (position :
      Pos (sequentialSignature (Step L) empty-state) (sequential-next edge)) →
    History (sequentialSignature (Step L) empty-state)
      (boundary (sequentialSignature (Step L) empty-state)
        (sequential-next edge) position)

  SeedChildren : Set (ℓe ⊔ ℓc ⊔ ℓg ⊔ ℓre)
  SeedChildren =
    (position :
      Pos (sequentialSignature (Step L) empty-state) sequential-seed) →
    History (sequentialSignature (Step L) empty-state)
      (boundary (sequentialSignature (Step L) empty-state) sequential-seed
        position)

  data Empty : Exponential L → Set (ℓe ⊔ ℓc ⊔ ℓg ⊔ ℓre) where
    empty-node : (children : SeedChildren) →
      Empty (exponential zero empty-state (node sequential-seed children))

  data Snoc : Exponent → Coefficient → Exponential L → Exponential L →
    Set (ℓe ⊔ ℓc ⊔ ℓg ⊔ ℓre) where
    first-node : (head : Exponent) (coefficient : Coefficient)
      (good : Good coefficient)
      (children : Children (first-step head coefficient good)) →
      Snoc head coefficient
        (exponential zero empty-state (children unary-position))
        (exponential (suc zero) (head-state head coefficient)
          (node (sequential-next (first-step head coefficient good))
            children))
    later-node : {n : ℕ} (head tail-head : Exponent)
      (coefficient tail-coefficient : Coefficient)
      (good : Good coefficient) (decrease : tail-head ≺e head)
      (children : Children (prepend-step head tail-head coefficient
        tail-coefficient good decrease)) →
      Snoc head coefficient
        (exponential (suc n) (head-state tail-head tail-coefficient)
          (children unary-position))
        (exponential (suc (suc n)) (head-state head coefficient)
          (node
            (sequential-next
              (prepend-step head tail-head coefficient tail-coefficient
                good decrease))
            children))

  data Shape (term : Exponential L) : Set (ℓe ⊔ ℓc ⊔ ℓg ⊔ ℓre) where
    empty-shape : Empty term → Shape term
    snoc-shape : {head : Exponent} {coefficient : Coefficient}
      {tail : Exponential L} → Snoc head coefficient tail term →
      Shape term

------------------------------------------------------------------------
-- Reading the views

  shape : (term : Exponential L) → Shape term
  shape (exponential n endpoint (hole ()))
  shape (exponential zero empty-state (node sequential-seed children)) =
    empty-shape (empty-node children)
  shape (exponential (suc zero) (head-state head coefficient)
    (node (sequential-next (first-step .head .coefficient good))
      children)) =
    snoc-shape (first-node head coefficient good children)
  shape (exponential (suc (suc n)) (head-state head coefficient)
    (node
      (sequential-next
        (prepend-step .head tail-head .coefficient tail-coefficient good
          decrease))
      children)) =
    snoc-shape
      (later-node head tail-head coefficient tail-coefficient good decrease
        children)

  empty-view :
    (history : SequentialHistory (Step L) empty-state zero empty-state) →
    Empty (exponential zero empty-state history)
  empty-view (hole ())
  empty-view (node sequential-seed children) = empty-node children

  snoc-of : {n : ℕ} {head : Exponent} {coefficient : Coefficient}
    (history : SequentialHistory (Step L) empty-state (suc n)
      (head-state head coefficient)) →
    Σ (Exponential L) (λ tail →
      Snoc head coefficient tail
        (exponential (suc n) (head-state head coefficient) history))
  snoc-of (hole ())
  snoc-of (node (sequential-next (first-step head coefficient good))
    children) =
    exponential zero empty-state (children unary-position) ,
    first-node head coefficient good children
  snoc-of (node
    (sequential-next
      (prepend-step {m} head tail-head coefficient tail-coefficient good
        decrease))
    children) =
    exponential (suc m) (head-state tail-head tail-coefficient)
      (children unary-position) ,
    later-node head tail-head coefficient tail-coefficient good decrease
      children

------------------------------------------------------------------------
-- The final node of a normal form built by prepend

  prepend-snoc : (head : Exponent) (coefficient : Coefficient)
    (good : Good coefficient) (tail : Exponential L)
    (below : TailBelow L head tail) →
    Snoc head coefficient tail (prepend L head coefficient good tail below)
  prepend-snoc head coefficient good
    .(exponential zero empty-state history) (below-empty history) =
    first-node head coefficient good
      (only-child (Step L) (first-step head coefficient good) history)
  prepend-snoc head coefficient good
    .(exponential (suc n) (head-state tail-head tail-coefficient) history)
    (below-head {n} tail-head tail-coefficient history decrease) =
    later-node head tail-head coefficient tail-coefficient good decrease
      (only-child (Step L)
        (prepend-step head tail-head coefficient tail-coefficient good
          decrease)
        history)

  zero-empty : Empty (zeroᴱ L)
  zero-empty = empty-view (support (zeroᴱ L))

  singleton-snoc : (head : Exponent) (coefficient : Coefficient)
    (good : Good coefficient) →
    Snoc head coefficient (zeroᴱ L) (singleton L head coefficient good)
  singleton-snoc head coefficient good =
    prepend-snoc head coefficient good (zeroᴱ L)
      (below-empty (support (zeroᴱ L)))

------------------------------------------------------------------------
-- The order

module _ {ℓe ℓc ℓg ℓre ℓrc : Level} {L : Layer ℓe ℓc ℓg ℓre ℓrc} where

  open Layer L

  infix 30 _≺ᴱ_

  data _≺ᴱ_ : Exponential L → Exponential L →
    Set (ℓe ⊔ ℓc ⊔ ℓg ⊔ ℓre ⊔ ℓrc) where
    proper-prefix : {left right-tail right : Exponential L}
      {right-head : Exponent} {right-coefficient : Coefficient} →
      Empty L left → Snoc L right-head right-coefficient right-tail right →
      left ≺ᴱ right
    first-difference : {left-tail left right-tail right : Exponential L}
      {left-head right-head : Exponent}
      {left-coefficient right-coefficient : Coefficient} →
      Snoc L left-head left-coefficient left-tail left →
      Snoc L right-head right-coefficient right-tail right →
      PairLess L left-head left-coefficient right-head right-coefficient →
      left ≺ᴱ right
    common-head : {left-tail left right-tail right : Exponential L}
      {head : Exponent} {coefficient : Coefficient} →
      Snoc L head coefficient left-tail left →
      Snoc L head coefficient right-tail right →
      left-tail ≺ᴱ right-tail → left ≺ᴱ right

------------------------------------------------------------------------
-- Removing the final node, and the formation order

  tail-below : {head : Exponent} {coefficient : Coefficient}
    {tail whole : Exponential L} →
    Snoc L head coefficient tail whole → tail ≺ᴱ whole
  tail-below final-node@(first-node head coefficient good children) =
    proper-prefix (empty-view L (children unary-position)) final-node
  tail-below final-node@(later-node head tail-head coefficient
    tail-coefficient good decrease children) =
    first-difference (pr₂ (snoc-of L (children unary-position))) final-node
      (exponent-less decrease)

  from-formation : Formation._≺ᴱ_ ⊆ _≺ᴱ_
  from-formation (Formation.proper-prefix left-empty right-head
    right-coefficient right-good right-tail right-below) =
    proper-prefix (empty-view L left-empty)
      (prepend-snoc L right-head right-coefficient right-good right-tail
        right-below)
  from-formation (Formation.first-difference left-head right-head
    left-coefficient right-coefficient left-tail right-tail left-good
    right-good left-below right-below difference) =
    first-difference
      (prepend-snoc L left-head left-coefficient left-good left-tail
        left-below)
      (prepend-snoc L right-head right-coefficient right-good right-tail
        right-below)
      difference
  from-formation (Formation.common-head head coefficient left-tail
    right-tail left-good right-good left-below right-below suffix) =
    common-head
      (prepend-snoc L head coefficient left-good left-tail left-below)
      (prepend-snoc L head coefficient right-good right-tail right-below)
      (from-formation suffix)

------------------------------------------------------------------------
-- The empty form has no predecessor

  empty-snoc-absurd : {term tail : Exponential L} {head : Exponent}
    {coefficient : Coefficient} →
    Empty L term → Snoc L head coefficient tail term → 𝟘
  empty-snoc-absurd (empty-node children) ()

  empty-no-predecessor : {left right : Exponential L} →
    Empty L right → left ≺ᴱ right → 𝟘
  empty-no-predecessor right-empty (proper-prefix left-empty right-node) =
    empty-snoc-absurd right-empty right-node
  empty-no-predecessor right-empty
    (first-difference left-node right-node difference) =
    empty-snoc-absurd right-empty right-node
  empty-no-predecessor right-empty (common-head left-node right-node suffix) =
    empty-snoc-absurd right-empty right-node

  empty-accessible : {term : Exponential L} → Empty L term →
    is-accessible _≺ᴱ_ term
  empty-accessible empty =
    acc (λ predecessor decrease →
      𝟘-elim (empty-no-predecessor empty decrease))

------------------------------------------------------------------------
-- Transitivity

  -- By cases on the views of the shared middle term.

  trans :
    ({left middle right : Exponent} →
      left ≺e middle → middle ≺e right → left ≺e right) →
    ({left middle right : Coefficient} →
      left ≺c middle → middle ≺c right → left ≺c right) →
    {left middle right : Exponential L} →
    left ≺ᴱ middle → middle ≺ᴱ right → left ≺ᴱ right
  trans te tc (proper-prefix left-empty middle-node)
    (proper-prefix middle-empty right-node) =
    𝟘-elim (empty-snoc-absurd middle-empty middle-node)
  trans te tc (proper-prefix left-empty middle-node)
    (first-difference middle-node′ right-node difference) =
    proper-prefix left-empty right-node
  trans te tc (proper-prefix left-empty middle-node)
    (common-head middle-node′ right-node suffix) =
    proper-prefix left-empty right-node
  trans te tc (first-difference left-node middle-node difference)
    (proper-prefix middle-empty right-node) =
    𝟘-elim (empty-snoc-absurd middle-empty middle-node)
  trans te tc (common-head left-node middle-node prefix)
    (proper-prefix middle-empty right-node) =
    𝟘-elim (empty-snoc-absurd middle-empty middle-node)
  trans te tc
    (first-difference left-node (first-node mh mc mg mk) left-difference)
    (first-difference (first-node .mh .mc .mg .mk) right-node
      right-difference) =
    first-difference left-node right-node
      (pair-trans L te tc left-difference right-difference)
  trans te tc
    (first-difference left-node (later-node mh mth mc mtc mg md mk)
      left-difference)
    (first-difference (later-node .mh .mth .mc .mtc .mg .md .mk) right-node
      right-difference) =
    first-difference left-node right-node
      (pair-trans L te tc left-difference right-difference)
  trans te tc
    (first-difference left-node (first-node mh mc mg mk) difference)
    (common-head (first-node .mh .mc .mg .mk) right-node suffix) =
    first-difference left-node right-node difference
  trans te tc
    (first-difference left-node (later-node mh mth mc mtc mg md mk)
      difference)
    (common-head (later-node .mh .mth .mc .mtc .mg .md .mk) right-node
      suffix) =
    first-difference left-node right-node difference
  trans te tc (common-head left-node (first-node mh mc mg mk) prefix)
    (first-difference (first-node .mh .mc .mg .mk) right-node difference) =
    first-difference left-node right-node difference
  trans te tc
    (common-head left-node (later-node mh mth mc mtc mg md mk) prefix)
    (first-difference (later-node .mh .mth .mc .mtc .mg .md .mk) right-node
      difference) =
    first-difference left-node right-node difference
  trans te tc (common-head left-node (first-node mh mc mg mk) prefix)
    (common-head (first-node .mh .mc .mg .mk) right-node suffix) =
    common-head left-node right-node (trans te tc prefix suffix)
  trans te tc
    (common-head left-node (later-node mh mth mc mtc mg md mk) prefix)
    (common-head (later-node .mh .mth .mc .mtc .mg .md .mk) right-node
      suffix) =
    common-head left-node right-node (trans te tc prefix suffix)

------------------------------------------------------------------------
-- Accessibility

  -- `HeadAcc h`, `CoefficientAcc h c` and `TailAcc h c t` say that every normal
  -- form whose final node has the given head, head and coefficient, or head,
  -- coefficient and tail is accessible.

  HeadAcc : Exponent → Set (ℓe ⊔ ℓc ⊔ ℓg ⊔ ℓre ⊔ ℓrc)
  HeadAcc head = {coefficient : Coefficient} {tail whole : Exponential L} →
    Snoc L head coefficient tail whole → is-accessible _≺ᴱ_ whole

  CoefficientAcc : Exponent → Coefficient → Set (ℓe ⊔ ℓc ⊔ ℓg ⊔ ℓre ⊔ ℓrc)
  CoefficientAcc head coefficient = {tail whole : Exponential L} →
    Snoc L head coefficient tail whole → is-accessible _≺ᴱ_ whole

  TailAcc : Exponent → Coefficient → Exponential L →
    Set (ℓe ⊔ ℓc ⊔ ℓg ⊔ ℓre ⊔ ℓrc)
  TailAcc head coefficient tail = {whole : Exponential L} →
    Snoc L head coefficient tail whole → is-accessible _≺ᴱ_ whole

  tail-accessible : {head : Exponent} →
    ({lower : Exponent} → lower ≺e head → HeadAcc lower) →
    {coefficient : Coefficient} {tail whole : Exponential L} →
    Snoc L head coefficient tail whole → is-accessible _≺ᴱ_ tail
  tail-accessible smaller-head (first-node head coefficient good children) =
    empty-accessible (empty-view L (children unary-position))
  tail-accessible smaller-head
    (later-node head tail-head coefficient tail-coefficient good decrease
      children) =
    smaller-head decrease (pr₂ (snoc-of L (children unary-position)))

  -- The induction on heads, on coefficients at one head, and on tails at one
  -- head and coefficient. The hypotheses about smaller points take the smaller
  -- point implicitly; at each induction, the step of `accessible-induction` is
  -- passed with it made implicit. Only the induction on heads uses the
  -- accessibility of the admissible coefficients (`good-accessible`).

  predecessor : {head : Exponent} {coefficient : Coefficient}
    {tail whole : Exponential L} →
    ({lower : Exponent} → lower ≺e head → HeadAcc lower) →
    ({lower : Coefficient} → lower ≺c coefficient →
      CoefficientAcc head lower) →
    ({lower : Exponential L} → lower ≺ᴱ tail →
      TailAcc head coefficient lower) →
    Snoc L head coefficient tail whole →
    (prior : Exponential L) → prior ≺ᴱ whole → is-accessible _≺ᴱ_ prior
  predecessor sh sc st (first-node head coefficient good children) prior
    (proper-prefix prior-empty
      (first-node .head .coefficient .good .children)) =
    empty-accessible prior-empty
  predecessor sh sc st (first-node head coefficient good children) prior
    (first-difference prior-node
      (first-node .head .coefficient .good .children)
      (exponent-less decrease)) =
    sh decrease prior-node
  predecessor sh sc st (first-node head coefficient good children) prior
    (first-difference prior-node
      (first-node .head .coefficient .good .children)
      (coefficient-less .head decrease)) =
    sc decrease prior-node
  predecessor sh sc st (first-node head coefficient good children) prior
    (common-head prior-node
      (first-node .head .coefficient .good .children) suffix) =
    st suffix prior-node
  predecessor sh sc st
    (later-node head tail-head coefficient tail-coefficient good
      support-decrease children)
    prior
    (proper-prefix prior-empty
      (later-node .head .tail-head .coefficient .tail-coefficient .good
        .support-decrease .children)) =
    empty-accessible prior-empty
  predecessor sh sc st
    (later-node head tail-head coefficient tail-coefficient good
      support-decrease children)
    prior
    (first-difference prior-node
      (later-node .head .tail-head .coefficient .tail-coefficient .good
        .support-decrease .children)
      (exponent-less decrease)) =
    sh decrease prior-node
  predecessor sh sc st
    (later-node head tail-head coefficient tail-coefficient good
      support-decrease children)
    prior
    (first-difference prior-node
      (later-node .head .tail-head .coefficient .tail-coefficient .good
        .support-decrease .children)
      (coefficient-less .head decrease)) =
    sc decrease prior-node
  predecessor sh sc st
    (later-node head tail-head coefficient tail-coefficient good
      support-decrease children)
    prior
    (common-head prior-node
      (later-node .head .tail-head .coefficient .tail-coefficient .good
        .support-decrease .children)
      suffix) =
    st suffix prior-node

  tail-step : (head : Exponent) (coefficient : Coefficient) →
    ({lower : Exponent} → lower ≺e head → HeadAcc lower) →
    ({lower : Coefficient} → lower ≺c coefficient →
      CoefficientAcc head lower) →
    (tail : Exponential L) →
    ((lower : Exponential L) → lower ≺ᴱ tail →
      TailAcc head coefficient lower) →
    TailAcc head coefficient tail
  tail-step head coefficient sh sc tail st final-node =
    acc (λ prior decrease →
      predecessor sh sc (λ {lower} → st lower) final-node prior decrease)

  tail-ind : (head : Exponent) (coefficient : Coefficient) →
    ({lower : Exponent} → lower ≺e head → HeadAcc lower) →
    ({lower : Coefficient} → lower ≺c coefficient →
      CoefficientAcc head lower) →
    (tail : Exponential L) → is-accessible _≺ᴱ_ tail →
    TailAcc head coefficient tail
  tail-ind head coefficient sh sc =
    accessible-induction (TailAcc head coefficient)
      (tail-step head coefficient sh sc)

  coefficient-step : (head : Exponent) →
    ({lower : Exponent} → lower ≺e head → HeadAcc lower) →
    (coefficient : Coefficient) →
    ({lower : Coefficient} → lower ≺c coefficient →
      CoefficientAcc head lower) →
    CoefficientAcc head coefficient
  coefficient-step head sh coefficient sc {tail} final-node =
    tail-ind head coefficient sh sc tail (tail-accessible sh final-node)
      final-node

  coefficient-ind : (head : Exponent) →
    ({lower : Exponent} → lower ≺e head → HeadAcc lower) →
    (coefficient : Coefficient) → is-accessible _≺c_ coefficient →
    CoefficientAcc head coefficient
  coefficient-ind head sh =
    accessible-induction (CoefficientAcc head)
      (λ coefficient smaller →
        coefficient-step head sh coefficient (λ {lower} → smaller lower))

  head-step : ((coefficient : Coefficient) → Good coefficient →
      is-accessible _≺c_ coefficient) →
    (head : Exponent) →
    ({lower : Exponent} → lower ≺e head → HeadAcc lower) → HeadAcc head
  head-step good-accessible head sh
    final-node@(first-node .head coefficient good children) =
    coefficient-ind head sh coefficient (good-accessible coefficient good)
      final-node
  head-step good-accessible head sh
    final-node@(later-node .head tail-head coefficient tail-coefficient good
      decrease children) =
    coefficient-ind head sh coefficient (good-accessible coefficient good)
      final-node

  head-ind : ((coefficient : Coefficient) → Good coefficient →
      is-accessible _≺c_ coefficient) →
    (head : Exponent) → is-accessible _≺e_ head → HeadAcc head
  head-ind good-accessible =
    accessible-induction HeadAcc
      (λ head smaller →
        head-step good-accessible head (λ {lower} → smaller lower))

------------------------------------------------------------------------
-- Well-foundedness

  well-founded : is-well-founded _≺e_ →
    ((coefficient : Coefficient) → Good coefficient →
      is-accessible _≺c_ coefficient) →
    is-well-founded _≺ᴱ_
  well-founded exponent-wf good-accessible
    (exponential zero empty-state history) =
    empty-accessible (empty-view L history)
  well-founded exponent-wf good-accessible
    (exponential (suc n) (head-state head coefficient) history) =
    head-ind good-accessible head (exponent-wf head)
      (pr₂ (snoc-of L history))

  formation-well-founded : is-well-founded _≺e_ →
    ((coefficient : Coefficient) → Good coefficient →
      is-accessible _≺c_ coefficient) →
    is-well-founded (Formation._≺ᴱ_ {L = L})
  formation-well-founded exponent-wf good-accessible =
    subrelations-are-well-founded from-formation
      (well-founded exponent-wf good-accessible)
