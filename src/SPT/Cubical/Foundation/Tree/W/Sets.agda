{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Tree.W.Sets where

-- Trees with a set of labels form a set. An identification of two trees
-- is an identification of their labels with one of their branch maps along
-- it (`to-tree-identification`, `from-tree-identification`), the first map
-- a retraction of the second (`to-from-tree-identification`):
--
--   sup x f ＝ sup x′ f′  ◁  Σ (p : x ＝ x′). f ＝ f′ ∘ transport B p.
--
-- Over a set of labels, under extensionality for the branch maps, the
-- right side is a proposition by induction on the trees, so the left side
-- is (`trees-over-a-set-are-sets`). After TypeTopology's W.Properties
-- (to-W-＝, from-W-＝, W-is-set), for the W-types of Foundation.Tree.W.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Extensionality
  using (FunExt; Π-is-proposition)
open import SPT.Cubical.Foundation.Happly using (happly; funext; funext-happly)
open import SPT.Cubical.Foundation.Propositions using
  (is-proposition; is-set; Σ-is-proposition)
open import SPT.Cubical.Foundation.Sets using
  (retracts-of-propositions-are-propositions)
open import SPT.Cubical.Foundation.Tree.W using (W; sup)

------------------------------------------------------------------------
-- Identifications of trees

module _ {a b : Level} {A : Set a} {B : A → Set b} where

  to-tree-identification : {x x′ : A} {f : B x → W A B}
    {f′ : B x′ → W A B} →
    Σ (x ＝ x′) (λ p → f ＝ (λ y → f′ (transport B p y))) →
    sup x f ＝ sup x′ f′
  to-tree-identification (refl , refl) = refl

  from-tree-identification : {x x′ : A} {f : B x → W A B}
    {f′ : B x′ → W A B} →
    sup x f ＝ sup x′ f′ →
    Σ (x ＝ x′) (λ p → f ＝ (λ y → f′ (transport B p y)))
  from-tree-identification refl = refl , refl

  to-from-tree-identification : {x x′ : A} {f : B x → W A B}
    {f′ : B x′ → W A B} (e : sup x f ＝ sup x′ f′) →
    to-tree-identification (from-tree-identification e) ＝ e
  to-from-tree-identification refl = refl

  ----------------------------------------------------------------------
  -- Over a set of labels

  -- The labels' identifications are propositions, and so are the branch
  -- maps', by induction: their homotopies are, and an identification of
  -- functions is the one extensionality makes from its homotopy.
  trees-over-a-set-are-sets :
    ((x : A) → FunExt (B x) (λ y → W A B)) →
    ((x : A) (f g : B x → W A B) → FunExt (B x) (λ y → f y ＝ g y)) →
    is-set A → is-set (W A B)
  trees-over-a-set-are-sets extensionality extensionality′ s (sup x f)
    (sup x′ f′) =
    retracts-of-propositions-are-propositions
      to-tree-identification from-tree-identification
      to-from-tree-identification
      (Σ-is-proposition (s x x′)
        (λ p → retracts-of-propositions-are-propositions
          (funext (extensionality x) f (λ y → f′ (transport B p y)))
          happly
          (funext-happly (extensionality x))
          (Π-is-proposition
            (extensionality′ x f (λ y → f′ (transport B p y)))
            (λ y → trees-over-a-set-are-sets extensionality extensionality′ s
              (f y) (f′ (transport B p y))))))
