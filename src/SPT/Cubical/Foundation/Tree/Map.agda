{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Tree.Map where

-- A family of maps `f : (j : J) → X j → Y j` relabels the holes of a tree, `map
-- f : Tree S X j → Tree S Y j`, and changes nothing else. Both computation
-- rules hold by `refl`.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Tree

module _ {ℓj ℓo ℓp ℓx ℓy : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} {Y : Judgment S → Set ℓy} where

  map : ((j : Judgment S) → X j → Y j) → {j : Judgment S} →
    Tree S X j → Tree S Y j
  map f (hole {j} x) = hole (f j x)
  map f (node o child) = node o (λ p → map f (child p))

------------------------------------------------------------------------
-- Properties

  map-hole : (f : (j : Judgment S) → X j → Y j) {j : Judgment S}
    (x : X j) → map f (hole x) ＝ hole (f j x)
  map-hole f x = refl

  map-node : (f : (j : Judgment S) → X j → Y j) {j : Judgment S}
    (o : Op S j) (child : (p : Pos S o) → Tree S X (boundary S o p)) →
    map f (node o child) ＝ node o (λ p → map f (child p))
  map-node f o child = refl
