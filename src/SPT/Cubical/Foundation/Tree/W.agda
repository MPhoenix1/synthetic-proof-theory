{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Tree.W where

-- W-types as closed trees at a single judgment. Labels `a : A` branch over
-- `B a` (`Branching A B`, its `signature`); `Open X` is the type of its
-- trees with holes in X, and `W A B` the type of its closed trees. The tree
-- with label x and children f : B x → W A B is `sup x f`, a pattern
-- synonym for `Tree.node`, usable in patterns and in terms. A tree has its
-- label and branches (`top`, `branch`) and induction, which computes on
-- `sup` by refl (`induction`, `induction-β`); a closed tree has no holes,
-- so every definition by cases needs only the clause for `sup`.

open import SPT.Cubical.Base
import SPT.Cubical.Foundation.Tree as Tree

module Branching {ℓa ℓb : Level} (A : Set ℓa) (B : A → Set ℓb) where

  signature : Tree.Signature lzero ℓa ℓb
  signature = record
    { Judgment = 𝟙
    ; Op = λ _ → A
    ; Pos = B
    ; boundary = λ _ _ → ⋆
    }

  Open : {ℓx : Level} → Set ℓx → Set (ℓa ⊔ ℓb ⊔ ℓx)
  Open X = Tree.Tree signature (λ _ → X) ⋆

------------------------------------------------------------------------
-- W-types

W : {ℓa ℓb : Level} (A : Set ℓa) (B : A → Set ℓb) → Set (ℓa ⊔ ℓb)
W A B = Tree.History (Branching.signature A B) ⋆

pattern sup x f = Tree.node x f

-- The label of a tree and its branches.
module _ {a b : Level} {A : Set a} {B : A → Set b} where

  top : W A B → A
  top (sup x f) = x

  branch : (w : W A B) → B (top w) → W A B
  branch (sup x f) = f

module _ {a b ν : Level} {A : Set a} {B : A → Set b}
  (P : W A B → Set ν)
  (step : (x : A) (f : B x → W A B) → ((y : B x) → P (f y)) →
    P (sup x f)) where

  induction : (w : W A B) → P w
  induction (sup x f) = step x f (λ y → induction (f y))

  induction-β : (x : A) (f : B x → W A B) →
    induction (sup x f) ＝ step x f (λ y → induction (f y))
  induction-β x f = refl
