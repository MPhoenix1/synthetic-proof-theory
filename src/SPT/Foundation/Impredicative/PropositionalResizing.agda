{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Impredicative.PropositionalResizing where

-- Propositional resizing. A proposition with a weak presentation at a level
-- is small at that level (`weakly-presented-propositions-are-small`): the
-- maps through the proposition give a weakly constant endomap of the
-- presenting type (`through-the-proposition`,
-- `through-the-proposition-is-weakly-constant`), whose fixed points form a
-- proposition of its level isomorphic to the proposition
-- (`fixed-points-are-the-proposition`). Propositional resizing is the
-- statement that every proposition of the next level is small
-- (`Propositional-Resizing`):
--
--   Propositional-Resizing ℓ =
--     Π (P : Set (ℓ + 1)). is-proposition P → is-small ℓ P.
--
-- Weak resizing gives it (`weak-resizing-gives-propositional-resizing`). A
-- small proposition is returned from a cover at its small level, through
-- the small type it is equivalent to (`small-proposition-from-cover`,
-- `small-proposition-from-cover-at-points`), so under propositional
-- resizing a cover at ℓ is a cover at ℓ + 1 (`covers-rise-under-resizing`):
-- resizing lets a cover observe the propositions of the next level.
--
-- Between any two levels, a proposition of level ν resized to κ is a
-- proposition of level κ with maps both ways (`Resized`), and
-- `Propositional-Resizing-Between ν κ` resizes every proposition of level ν
-- to κ; every proposition resizes to its own level
-- (`propositions-resize-to-their-level`), and from ℓ + 1 to ℓ the two forms
-- are one strength (`propositional-resizing-between-levels`,
-- `resizing-between-levels-gives-propositional-resizing`). After Core's
-- FiberCoding.Proposition and FiberCoding.Proposition.Envelope; the form
-- between two levels moved here from Mahlo.DS.Univalent.Resizing.

open import SPT.Base
open import SPT.Foundation.Covers using
  (Covered; covered-by-point; map-covered; extract-proposition)
open import SPT.Foundation.Impredicative.Classification using (Resizing)
open import SPT.Foundation.Impredicative.WeakResizing using
  (Weak-Presentation; weak-resizing-presents)
open import SPT.Foundation.Isomorphisms using
  (_≅_; forward; backward; ≅-sym)
open import SPT.Foundation.Propositions using (is-proposition)
open import SPT.Foundation.Propositions.Closure using
  ( is-weakly-constant; fixed-points; fixed-points-form-a-proposition
  ; isomorphic-to-a-proposition)
open import SPT.Foundation.Size using (is-small)
open import SPT.Foundation.Univalence using
  (isomorphism-to-equivalence; equivalence-to-isomorphism)

------------------------------------------------------------------------
-- A weakly presented proposition is small

-- Maps both ways between a proposition and Q give a weakly constant endomap of
-- Q, whose fixed points form a proposition of the level of Q, isomorphic to P.

module _ {ℓ κ : Level} {P : Set κ} (h : is-proposition P) {Q : Set ℓ}
  (to : Q → P) (from : P → Q) where

  through-the-proposition : Q → Q
  through-the-proposition q = from (to q)

  through-the-proposition-is-weakly-constant :
    is-weakly-constant through-the-proposition
  through-the-proposition-is-weakly-constant x y = ap from (h (to x) (to y))

  fixed-points-are-the-proposition :
    fixed-points through-the-proposition ≅ P
  fixed-points-are-the-proposition = record
    { forward = λ w → to (pr₁ w)
    ; backward = λ p → from p , ap from (h p (to (from p)))
    ; backward-forward = λ w →
        fixed-points-form-a-proposition through-the-proposition
          through-the-proposition-is-weakly-constant
          ( from (to (pr₁ w))
          , ap from (h (to (pr₁ w)) (to (from (to (pr₁ w))))))
          w
    ; forward-backward = λ p → h (to (from p)) p
    }

module _ {ℓ κ : Level} {P : Set κ} (h : is-proposition P) where

  -- Mathematical shape: Q ⇔ P, P a proposition, gives P small at Q's level.
  weakly-presented-propositions-are-small :
    Weak-Presentation ℓ P → is-small ℓ P
  weakly-presented-propositions-are-small (Q , to , from) =
    fixed-points (through-the-proposition h to from) ,
    isomorphism-to-equivalence (fixed-points-are-the-proposition h to from)

------------------------------------------------------------------------
-- Propositional resizing

-- Mathematical shape: every proposition of the next level is small.
Propositional-Resizing : (ℓ : Level) → Set (lsuc (lsuc ℓ))
Propositional-Resizing ℓ =
  (P : Set (lsuc ℓ)) → is-proposition P → is-small ℓ P

-- Weak resizing presents every proposition of the next level, which makes
-- it small.
weak-resizing-gives-propositional-resizing : {ℓ : Level} →
  Resizing (λ (X : Set ℓ) → X) → Propositional-Resizing ℓ
weak-resizing-gives-propositional-resizing r P h =
  weakly-presented-propositions-are-small h (weak-resizing-presents r P)

------------------------------------------------------------------------
-- Covers through small propositions

module _ {ℓ κ : Level} {P : Set κ} (h : is-proposition P)
  (s : is-small ℓ P) where

  -- The cover proves the small type equivalent to P, a proposition of
  -- level ℓ, and its point goes forward to P.
  small-proposition-from-cover : Covered ℓ P → P
  small-proposition-from-cover c =
    forward (equivalence-to-isomorphism (pr₂ s))
      ( extract-proposition
          (map-covered (backward (equivalence-to-isomorphism (pr₂ s))) c)
          ( isomorphic-to-a-proposition
              (≅-sym (equivalence-to-isomorphism (pr₂ s))) h))

  small-proposition-from-cover-at-points : (p : P) →
    small-proposition-from-cover (covered-by-point p) ＝ p
  small-proposition-from-cover-at-points p =
    h (small-proposition-from-cover (covered-by-point p)) p

-- Mathematical shape: Covered ℓ A → Covered (ℓ + 1) A, under resizing at ℓ.
covers-rise-under-resizing : {ℓ μ : Level} {A : Set μ} →
  Propositional-Resizing ℓ → Covered ℓ A → Covered (lsuc ℓ) A
covers-rise-under-resizing resize c R h consequence =
  small-proposition-from-cover h (resize R h) (map-covered consequence c)

------------------------------------------------------------------------
-- Resizing between two levels

-- A proposition of level ν resized to level κ.
record Resized {ν : Level} (κ : Level) (P : Set ν) : Set (ν ⊔ lsuc κ) where
  field
    small : Set κ
    small-proposition : is-proposition small
    down : P → small
    up : small → P

-- Mathematical shape: Π (P : Set ν). is-proposition P → Resized κ P.
Propositional-Resizing-Between : (ν κ : Level) → Set (lsuc ν ⊔ lsuc κ)
Propositional-Resizing-Between ν κ =
  (P : Set ν) → is-proposition P → Resized κ P

-- Each proposition is resized to its own level by itself.
propositions-resize-to-their-level : (ν : Level) →
  Propositional-Resizing-Between ν ν
propositions-resize-to-their-level ν P h = record
  { small = P
  ; small-proposition = h
  ; down = λ x → x
  ; up = λ x → x
  }

-- The small type of a small proposition is a proposition, with the maps of
-- its equivalence.
propositional-resizing-between-levels : {ℓ : Level} →
  Propositional-Resizing ℓ → Propositional-Resizing-Between (lsuc ℓ) ℓ
propositional-resizing-between-levels resize P h = record
  { small = pr₁ (resize P h)
  ; small-proposition =
      isomorphic-to-a-proposition
        (≅-sym (equivalence-to-isomorphism (pr₂ (resize P h)))) h
  ; down = backward (equivalence-to-isomorphism (pr₂ (resize P h)))
  ; up = forward (equivalence-to-isomorphism (pr₂ (resize P h)))
  }

-- A resized proposition is weakly presented, so small.
resizing-between-levels-gives-propositional-resizing : {ℓ : Level} →
  Propositional-Resizing-Between (lsuc ℓ) ℓ → Propositional-Resizing ℓ
resizing-between-levels-gives-propositional-resizing resize P h =
  weakly-presented-propositions-are-small h
    (Resized.small (resize P h) , Resized.up (resize P h) ,
      Resized.down (resize P h))
