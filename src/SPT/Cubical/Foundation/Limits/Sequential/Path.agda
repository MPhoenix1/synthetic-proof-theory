{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Limits.Sequential.Path where

-- The functional sequential diagram of paths between two points u and v of
-- a functional sequential limit. Its stage n is the type of identifications
-- of the n-th stages (`Stage-Path`); its restriction carries an
-- identification one stage up along both retained adjacent witnesses
-- (`restricted-path`):
--
--   restricted-path n p = adjacent u n ⁻¹ ∙ (ap (r n) p ∙ adjacent v n).
--
-- An alignment is a family of stage paths with a commuting square at every
-- step (`Squares`, `Alignment`):
--
--   adjacent u n ∙ h n ＝ ap (r n) (h (n + 1)) ∙ adjacent v n.
--
-- Alignments and points of the limit of the path diagram correspond
-- (`assemble`, `observe`): a square is solved for the stage path and back,
-- each recovered exactly (`square-β`, `route-β`). With extensionality for
-- the squares and for the witnesses over one fixed family of paths, both
-- round trips are identifications (`alignments-are-path-limits`); the
-- paths themselves move with no hypothesis.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Extensionality using (FunExt)
open import SPT.Cubical.Foundation.Isomorphisms using (_≅_)
open import SPT.Cubical.Foundation.Limits.Sequential using
  (limit; stage; adjacent; Functional-Limit)

------------------------------------------------------------------------
-- The diagram of stage paths

module _ {ℓ : Level} {Stage : ℕ → Set ℓ}
  (r : (n : ℕ) → Stage (suc n) → Stage n) (u v : Functional-Limit Stage r)
  where

  Stage-Path : ℕ → Set ℓ
  Stage-Path n = stage u n ＝ stage v n

  restricted-path : (n : ℕ) → Stage-Path (suc n) → Stage-Path n
  restricted-path n p = adjacent u n ⁻¹ ∙ (ap (r n) p ∙ adjacent v n)

  Squares : ((n : ℕ) → Stage-Path n) → Set ℓ
  Squares h = (n : ℕ) →
    adjacent u n ∙ h n ＝ ap (r n) (h (suc n)) ∙ adjacent v n

-- Mathematical shape: Σ (h : Π n. Stage-Path n). Squares h.
record Alignment {ℓ : Level} {Stage : ℕ → Set ℓ}
  (r : (n : ℕ) → Stage (suc n) → Stage n) (u v : Functional-Limit Stage r) :
  Set ℓ where
  constructor alignment
  field
    stage-path : (n : ℕ) → Stage-Path r u v n
    square : Squares r u v stage-path

open Alignment public

------------------------------------------------------------------------
-- Solving a square for its path

-- Solving a ∙ p ＝ q for p, and back; both round trips compare the
-- witnesses themselves.

private
  solve : {κ : Level} {A : Set κ} {x y z : A} (a : x ＝ y) (p : y ＝ z)
    (q : x ＝ z) → a ∙ p ＝ q → a ⁻¹ ∙ q ＝ p
  solve refl p q h = h ⁻¹

  restore : {κ : Level} {A : Set κ} {x y z : A} (a : x ＝ y) (p : y ＝ z)
    (q : x ＝ z) → a ⁻¹ ∙ q ＝ p → a ∙ p ＝ q
  restore refl p q h = h ⁻¹

  restore-solve : {κ : Level} {A : Set κ} {x y z : A} (a : x ＝ y)
    (p : y ＝ z) (q : x ＝ z) (h : a ∙ p ＝ q) →
    restore a p q (solve a p q h) ＝ h
  restore-solve refl p .p refl = refl

  solve-restore : {κ : Level} {A : Set κ} {x y z : A} (a : x ＝ y)
    (p : y ＝ z) (q : x ＝ z) (h : a ⁻¹ ∙ q ＝ p) →
    solve a p q (restore a p q h) ＝ h
  solve-restore refl p .p refl = refl

------------------------------------------------------------------------
-- Alignments are points of the limit of stage paths

module _ {ℓ : Level} {Stage : ℕ → Set ℓ}
  (r : (n : ℕ) → Stage (suc n) → Stage n) (u v : Functional-Limit Stage r)
  where

  assemble : Alignment r u v →
    Functional-Limit (Stage-Path r u v) (restricted-path r u v)
  assemble h =
    limit (stage-path h) (λ n →
      solve (adjacent u n) (stage-path h n)
        (ap (r n) (stage-path h (suc n)) ∙ adjacent v n) (square h n))

  observe : Functional-Limit (Stage-Path r u v) (restricted-path r u v) →
    Alignment r u v
  observe t =
    alignment (stage t) (λ n →
      restore (adjacent u n) (stage t n)
        (ap (r n) (stage t (suc n)) ∙ adjacent v n) (adjacent t n))

  square-β : (h : Alignment r u v) (n : ℕ) →
    square (observe (assemble h)) n ＝ square h n
  square-β h n =
    restore-solve (adjacent u n) (stage-path h n)
      (ap (r n) (stage-path h (suc n)) ∙ adjacent v n) (square h n)

  route-β :
    (t : Functional-Limit (Stage-Path r u v) (restricted-path r u v))
    (n : ℕ) → adjacent (assemble (observe t)) n ＝ adjacent t n
  route-β t n =
    solve-restore (adjacent u n) (stage t n)
      (ap (r n) (stage t (suc n)) ∙ adjacent v n) (adjacent t n)

  -- Extensionality compares only the squares and the witnesses over one
  -- fixed family of paths; the family itself stays literal.

  module _
    (squares : (h : (n : ℕ) → Stage-Path r u v n) →
      FunExt ℕ (λ n →
        adjacent u n ∙ h n ＝ ap (r n) (h (suc n)) ∙ adjacent v n))
    (routes : (h : (n : ℕ) → Stage-Path r u v n) →
      FunExt ℕ (λ n → restricted-path r u v n (h (suc n)) ＝ h n))
    where

    observe-assemble : (h : Alignment r u v) → observe (assemble h) ＝ h
    observe-assemble h =
      ap (alignment (stage-path h))
        (squares (stage-path h) (square (observe (assemble h))) (square h)
          (square-β h))

    assemble-observe :
      (t : Functional-Limit (Stage-Path r u v) (restricted-path r u v)) →
      assemble (observe t) ＝ t
    assemble-observe t =
      ap (limit (stage t))
        (routes (stage t) (adjacent (assemble (observe t))) (adjacent t)
          (route-β t))

    alignments-are-path-limits :
      Alignment r u v
        ≅ Functional-Limit (Stage-Path r u v) (restricted-path r u v)
    alignments-are-path-limits = record
      { forward = assemble
      ; backward = observe
      ; backward-forward = observe-assemble
      ; forward-backward = assemble-observe
      }
