{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Univalence.Substitution where

-- Substitution into the parts of the statement of univalence
-- (Univalence), as structural relation: each part, substituted, is
-- the part at the substituted inputs (`arrow-substituted`, `call-…`,
-- `identity-function-…`, `section-homotopy-…`, `has-section-…`,
-- `retraction-homotopy-…`, `is-section-…`, `is-equiv-…`,
-- `equivalence-…`, `refl-homotopy-…`, `id-is-equiv-…`,
-- `identity-equivalence-…`, `idtoeq-substituted`). Each law follows the
-- part's definition through the laws of the formers (Formers.Substitution)
-- and takes the relations of the substituted inputs to given expressions.
-- Inputs under binders take the substitution lifted over them, and
-- weakened inputs go to the weakened substituted ones
-- (`weakened-substituted`). The motive of J in idtoeq sits under two
-- binders: there the substitution lifted over both is replaced by the one
-- lifted twice over one (Lifting's `lifted-twice`,
-- `substitute-pointwise-rel`). Weakening is the substitution of the
-- shifted variables, so the parts weakened are the parts at the weakened
-- inputs (`paths-weakened`, `arrow-weakened`, `equivalence-weakened`,
-- `is-section-weakened`, `idtoeq-weakened`); and X → Y keeps the
-- relation (`arrow-related`).

open import SPT.Base
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Tree as Tree
import SPT.Foundation.Tree.Relation as Relation
import SPT.Foundation.Tree.Binding as Binding
import SPT.Foundation.Tree.Binding.Lifting as Lifting
open import SPT.MartinLof.Formers using
  (universe; pair; identity; reflexivity; path-induction; weaken)
open import SPT.MartinLof.Formers.Substitution using
  (universe-substituted; pi-substituted; lambda-substituted
  ; application-substituted; sigma-substituted; pair-substituted
  ; identity-substituted; reflexivity-substituted; path-induction-substituted
  ; weakened-substituted; shifted-from; weakened-as; weaken-related)
import SPT.MartinLof.Raw as Raw
import SPT.MartinLof.Univalence as Univalence

------------------------------------------------------------------------
-- Functions

-- X → Y.
arrow-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ l₂ : ℕ)
  (X Y : Raw.Expression C n) (X′ Y′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ X) X′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ Y) Y′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ (Univalence.arrow l₁ l₂ X Y))
      (Univalence.arrow l₁ l₂ X′ Y′)
arrow-substituted m σ l₁ l₂ X Y X′ Y′ rX rY =
  pi-substituted m σ l₁ l₂ X (weaken Y) X′ (weaken Y′) rX
    (weakened-substituted m σ Y Y′ rY)

-- f x.
call-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ l₂ : ℕ)
  (X Y f x : Raw.Expression C n) (X′ Y′ f′ x′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ X) X′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ Y) Y′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ f) f′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ x) x′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ
        (Univalence.call l₁ l₂ X Y f x))
      (Univalence.call l₁ l₂ X′ Y′ f′ x′)
call-substituted m σ l₁ l₂ X Y f x X′ Y′ f′ x′ rX rY rf rx =
  application-substituted m σ l₁ l₂ X (weaken Y) f x X′ (weaken Y′) f′ x′
    rX (weakened-substituted m σ Y Y′ rY) rf rx

-- id.
identity-function-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ : ℕ)
  (X : Raw.Expression C n) (X′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ X) X′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ
        (Univalence.identity-function l₁ X))
      (Univalence.identity-function l₁ X′)
identity-function-substituted m σ l₁ X X′ rX =
  lambda-substituted m σ l₁ l₁ X (weaken X) (Tree.hole fzero)
    X′ (weaken X′) (Tree.hole fzero) rX
    (weakened-substituted m σ X X′ rX)
    (Lifting.identical (Tree.hole fzero))

------------------------------------------------------------------------
-- Sections, retractions and equivalences

-- f ∘ s ∼ id, for s the last variable: the substitution lifted over s.
section-homotopy-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ l₂ : ℕ)
  (X Y f : Raw.Expression C n) (X′ Y′ f′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ X) X′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ Y) Y′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ f) f′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) (suc m)
        (Lifting.lifted (Raw.binding C) m 1 σ)
        (Univalence.section-homotopy l₁ l₂ X Y f))
      (Univalence.section-homotopy l₁ l₂ X′ Y′ f′)
section-homotopy-substituted {C} m σ l₁ l₂ X Y f X′ Y′ f′ rX rY rf =
  let τ = Lifting.lifted (Raw.binding C) m 1 σ
      ρ = Lifting.lifted (Raw.binding C) (suc m) 1 τ
      rX₁ = weakened-substituted m σ X X′ rX
      rY₁ = weakened-substituted m σ Y Y′ rY
      rf₁ = weakened-substituted m σ f f′ rf
      rX₂ = weakened-substituted (suc m) τ (weaken X) (weaken X′) rX₁
      rY₂ = weakened-substituted (suc m) τ (weaken Y) (weaken Y′) rY₁
      rf₂ = weakened-substituted (suc m) τ (weaken f) (weaken f′) rf₁
      X₂ = weaken (weaken X)
      Y₂ = weaken (weaken Y)
      f₂ = weaken (weaken f)
      X₂′ = weaken (weaken X′)
      Y₂′ = weaken (weaken Y′)
      f₂′ = weaken (weaken f′)
      inner = Univalence.call l₂ l₁ Y₂ X₂
                (Tree.hole (fsuc fzero)) (Tree.hole fzero)
      inner′ = Univalence.call l₂ l₁ Y₂′ X₂′
                 (Tree.hole (fsuc fzero)) (Tree.hole fzero)
      outer = Univalence.call l₁ l₂ X₂ Y₂ f₂ inner
      outer′ = Univalence.call l₁ l₂ X₂′ Y₂′ f₂′ inner′
  in pi-substituted (suc m) τ l₂ l₂ (weaken Y)
       (identity l₂ Y₂ outer (Tree.hole fzero)) (weaken Y′)
       (identity l₂ Y₂′ outer′ (Tree.hole fzero)) rY₁
       (identity-substituted (suc (suc m)) ρ l₂ Y₂ outer (Tree.hole fzero)
         Y₂′ outer′ (Tree.hole fzero) rY₂
         (call-substituted (suc (suc m)) ρ l₁ l₂ X₂ Y₂ f₂ inner
           X₂′ Y₂′ f₂′ inner′ rX₂ rY₂ rf₂
           (call-substituted (suc (suc m)) ρ l₂ l₁ Y₂ X₂
             (Tree.hole (fsuc fzero)) (Tree.hole fzero) Y₂′ X₂′
             (Tree.hole (fsuc fzero)) (Tree.hole fzero) rY₂ rX₂
             (Lifting.identical (Tree.hole (fsuc fzero)))
             (Lifting.identical (Tree.hole fzero))))
         (Lifting.identical (Tree.hole fzero)))

-- has-section f.
has-section-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ l₂ : ℕ)
  (X Y f : Raw.Expression C n) (X′ Y′ f′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ X) X′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ Y) Y′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ f) f′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ
        (Univalence.has-section l₁ l₂ X Y f))
      (Univalence.has-section l₁ l₂ X′ Y′ f′)
has-section-substituted m σ l₁ l₂ X Y f X′ Y′ f′ rX rY rf =
  sigma-substituted m σ (l₂ ⊔ℕ l₁) l₂
    (Univalence.arrow l₂ l₁ Y X) (Univalence.section-homotopy l₁ l₂ X Y f)
    (Univalence.arrow l₂ l₁ Y′ X′)
    (Univalence.section-homotopy l₁ l₂ X′ Y′ f′)
    (arrow-substituted m σ l₂ l₁ Y X Y′ X′ rY rX)
    (section-homotopy-substituted m σ l₁ l₂ X Y f X′ Y′ f′ rX rY rf)

-- r ∘ f ∼ id, for r the last variable: the substitution lifted over r.
retraction-homotopy-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ l₂ : ℕ)
  (X Y f : Raw.Expression C n) (X′ Y′ f′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ X) X′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ Y) Y′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ f) f′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) (suc m)
        (Lifting.lifted (Raw.binding C) m 1 σ)
        (Univalence.retraction-homotopy l₁ l₂ X Y f))
      (Univalence.retraction-homotopy l₁ l₂ X′ Y′ f′)
retraction-homotopy-substituted {C} m σ l₁ l₂ X Y f X′ Y′ f′ rX rY rf =
  let τ = Lifting.lifted (Raw.binding C) m 1 σ
      ρ = Lifting.lifted (Raw.binding C) (suc m) 1 τ
      rX₁ = weakened-substituted m σ X X′ rX
      rY₁ = weakened-substituted m σ Y Y′ rY
      rf₁ = weakened-substituted m σ f f′ rf
      rX₂ = weakened-substituted (suc m) τ (weaken X) (weaken X′) rX₁
      rY₂ = weakened-substituted (suc m) τ (weaken Y) (weaken Y′) rY₁
      rf₂ = weakened-substituted (suc m) τ (weaken f) (weaken f′) rf₁
      X₂ = weaken (weaken X)
      Y₂ = weaken (weaken Y)
      f₂ = weaken (weaken f)
      X₂′ = weaken (weaken X′)
      Y₂′ = weaken (weaken Y′)
      f₂′ = weaken (weaken f′)
      inner = Univalence.call l₁ l₂ X₂ Y₂ f₂ (Tree.hole fzero)
      inner′ = Univalence.call l₁ l₂ X₂′ Y₂′ f₂′ (Tree.hole fzero)
      outer = Univalence.call l₂ l₁ Y₂ X₂ (Tree.hole (fsuc fzero)) inner
      outer′ = Univalence.call l₂ l₁ Y₂′ X₂′
                 (Tree.hole (fsuc fzero)) inner′
  in pi-substituted (suc m) τ l₁ l₁ (weaken X)
       (identity l₁ X₂ outer (Tree.hole fzero)) (weaken X′)
       (identity l₁ X₂′ outer′ (Tree.hole fzero)) rX₁
       (identity-substituted (suc (suc m)) ρ l₁ X₂ outer (Tree.hole fzero)
         X₂′ outer′ (Tree.hole fzero) rX₂
         (call-substituted (suc (suc m)) ρ l₂ l₁ Y₂ X₂
           (Tree.hole (fsuc fzero)) inner Y₂′ X₂′
           (Tree.hole (fsuc fzero)) inner′ rY₂ rX₂
           (Lifting.identical (Tree.hole (fsuc fzero)))
           (call-substituted (suc (suc m)) ρ l₁ l₂ X₂ Y₂ f₂
             (Tree.hole fzero) X₂′ Y₂′ f₂′ (Tree.hole fzero)
             rX₂ rY₂ rf₂ (Lifting.identical (Tree.hole fzero))))
         (Lifting.identical (Tree.hole fzero)))

-- is-section f.
is-section-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ l₂ : ℕ)
  (X Y f : Raw.Expression C n) (X′ Y′ f′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ X) X′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ Y) Y′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ f) f′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ
        (Univalence.is-section l₁ l₂ X Y f))
      (Univalence.is-section l₁ l₂ X′ Y′ f′)
is-section-substituted m σ l₁ l₂ X Y f X′ Y′ f′ rX rY rf =
  sigma-substituted m σ (l₂ ⊔ℕ l₁) l₁
    (Univalence.arrow l₂ l₁ Y X)
    (Univalence.retraction-homotopy l₁ l₂ X Y f)
    (Univalence.arrow l₂ l₁ Y′ X′)
    (Univalence.retraction-homotopy l₁ l₂ X′ Y′ f′)
    (arrow-substituted m σ l₂ l₁ Y X Y′ X′ rY rX)
    (retraction-homotopy-substituted m σ l₁ l₂ X Y f X′ Y′ f′ rX rY rf)

-- is-equiv f.
is-equiv-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ l₂ : ℕ)
  (X Y f : Raw.Expression C n) (X′ Y′ f′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ X) X′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ Y) Y′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ f) f′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ
        (Univalence.is-equiv l₁ l₂ X Y f))
      (Univalence.is-equiv l₁ l₂ X′ Y′ f′)
is-equiv-substituted m σ l₁ l₂ X Y f X′ Y′ f′ rX rY rf =
  sigma-substituted m σ (l₁ ⊔ℕ l₂) (l₁ ⊔ℕ l₂)
    (Univalence.has-section l₁ l₂ X Y f)
    (weaken (Univalence.is-section l₁ l₂ X Y f))
    (Univalence.has-section l₁ l₂ X′ Y′ f′)
    (weaken (Univalence.is-section l₁ l₂ X′ Y′ f′))
    (has-section-substituted m σ l₁ l₂ X Y f X′ Y′ f′ rX rY rf)
    (weakened-substituted m σ (Univalence.is-section l₁ l₂ X Y f)
      (Univalence.is-section l₁ l₂ X′ Y′ f′)
      (is-section-substituted m σ l₁ l₂ X Y f X′ Y′ f′ rX rY rf))

-- X ≃ Y.
equivalence-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ l₂ : ℕ)
  (X Y : Raw.Expression C n) (X′ Y′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ X) X′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ Y) Y′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ
        (Univalence.equivalence l₁ l₂ X Y))
      (Univalence.equivalence l₁ l₂ X′ Y′)
equivalence-substituted {C} m σ l₁ l₂ X Y X′ Y′ rX rY =
  sigma-substituted m σ (l₁ ⊔ℕ l₂) (l₁ ⊔ℕ l₂)
    (Univalence.arrow l₁ l₂ X Y)
    (Univalence.is-equiv l₁ l₂ (weaken X) (weaken Y) (Tree.hole fzero))
    (Univalence.arrow l₁ l₂ X′ Y′)
    (Univalence.is-equiv l₁ l₂ (weaken X′) (weaken Y′) (Tree.hole fzero))
    (arrow-substituted m σ l₁ l₂ X Y X′ Y′ rX rY)
    (is-equiv-substituted (suc m) (Lifting.lifted (Raw.binding C) m 1 σ)
      l₁ l₂ (weaken X) (weaken Y) (Tree.hole fzero)
      (weaken X′) (weaken Y′) (Tree.hole fzero)
      (weakened-substituted m σ X X′ rX) (weakened-substituted m σ Y Y′ rY)
      (Lifting.identical (Tree.hole fzero)))

------------------------------------------------------------------------
-- The identity equivalence

-- λ x → refl.
refl-homotopy-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ : ℕ)
  (X : Raw.Expression C n) (X′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ X) X′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ
        (Univalence.refl-homotopy l₁ X))
      (Univalence.refl-homotopy l₁ X′)
refl-homotopy-substituted {C} m σ l₁ X X′ rX =
  let τ = Lifting.lifted (Raw.binding C) m 1 σ
      rX₁ = weakened-substituted m σ X X′ rX
      i₁ = weaken (Univalence.identity-function l₁ X)
      i₁′ = weaken (Univalence.identity-function l₁ X′)
      ri₁ = weakened-substituted m σ (Univalence.identity-function l₁ X)
              (Univalence.identity-function l₁ X′)
              (identity-function-substituted m σ l₁ X X′ rX)
      inner = Univalence.call l₁ l₁ (weaken X) (weaken X) i₁
                (Tree.hole fzero)
      inner′ = Univalence.call l₁ l₁ (weaken X′) (weaken X′) i₁′
                 (Tree.hole fzero)
      outer = Univalence.call l₁ l₁ (weaken X) (weaken X) i₁ inner
      outer′ = Univalence.call l₁ l₁ (weaken X′) (weaken X′) i₁′ inner′
  in lambda-substituted m σ l₁ l₁ X
       (identity l₁ (weaken X) outer (Tree.hole fzero))
       (reflexivity l₁ (weaken X) (Tree.hole fzero))
       X′ (identity l₁ (weaken X′) outer′ (Tree.hole fzero))
       (reflexivity l₁ (weaken X′) (Tree.hole fzero)) rX
       (identity-substituted (suc m) τ l₁ (weaken X) outer
         (Tree.hole fzero) (weaken X′) outer′ (Tree.hole fzero) rX₁
         (call-substituted (suc m) τ l₁ l₁ (weaken X) (weaken X) i₁ inner
           (weaken X′) (weaken X′) i₁′ inner′ rX₁ rX₁ ri₁
           (call-substituted (suc m) τ l₁ l₁ (weaken X) (weaken X) i₁
             (Tree.hole fzero) (weaken X′) (weaken X′) i₁′
             (Tree.hole fzero) rX₁ rX₁ ri₁
             (Lifting.identical (Tree.hole fzero))))
         (Lifting.identical (Tree.hole fzero)))
       (reflexivity-substituted (suc m) τ l₁ (weaken X) (Tree.hole fzero)
         (weaken X′) (Tree.hole fzero) rX₁
         (Lifting.identical (Tree.hole fzero)))

-- id-is-equiv X.
id-is-equiv-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ : ℕ)
  (X : Raw.Expression C n) (X′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ X) X′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ (Univalence.id-is-equiv l₁ X))
      (Univalence.id-is-equiv l₁ X′)
id-is-equiv-substituted m σ l₁ X X′ rX =
  let i = Univalence.identity-function l₁ X
      i′ = Univalence.identity-function l₁ X′
      ri = identity-function-substituted m σ l₁ X X′ rX
      h = Univalence.refl-homotopy l₁ X
      h′ = Univalence.refl-homotopy l₁ X′
      rh = refl-homotopy-substituted m σ l₁ X X′ rX
      rA = arrow-substituted m σ l₁ l₁ X X X′ X′ rX rX
  in pair-substituted m σ (l₁ ⊔ℕ l₁) (l₁ ⊔ℕ l₁)
       (Univalence.has-section l₁ l₁ X X i)
       (weaken (Univalence.is-section l₁ l₁ X X i))
       (pair (l₁ ⊔ℕ l₁) l₁ (Univalence.arrow l₁ l₁ X X)
         (Univalence.section-homotopy l₁ l₁ X X i) i h)
       (pair (l₁ ⊔ℕ l₁) l₁ (Univalence.arrow l₁ l₁ X X)
         (Univalence.retraction-homotopy l₁ l₁ X X i) i h)
       (Univalence.has-section l₁ l₁ X′ X′ i′)
       (weaken (Univalence.is-section l₁ l₁ X′ X′ i′))
       (pair (l₁ ⊔ℕ l₁) l₁ (Univalence.arrow l₁ l₁ X′ X′)
         (Univalence.section-homotopy l₁ l₁ X′ X′ i′) i′ h′)
       (pair (l₁ ⊔ℕ l₁) l₁ (Univalence.arrow l₁ l₁ X′ X′)
         (Univalence.retraction-homotopy l₁ l₁ X′ X′ i′) i′ h′)
       (has-section-substituted m σ l₁ l₁ X X i X′ X′ i′ rX rX ri)
       (weakened-substituted m σ (Univalence.is-section l₁ l₁ X X i)
         (Univalence.is-section l₁ l₁ X′ X′ i′)
         (is-section-substituted m σ l₁ l₁ X X i X′ X′ i′ rX rX ri))
       (pair-substituted m σ (l₁ ⊔ℕ l₁) l₁ (Univalence.arrow l₁ l₁ X X)
         (Univalence.section-homotopy l₁ l₁ X X i) i h
         (Univalence.arrow l₁ l₁ X′ X′)
         (Univalence.section-homotopy l₁ l₁ X′ X′ i′) i′ h′ rA
         (section-homotopy-substituted m σ l₁ l₁ X X i X′ X′ i′ rX rX ri)
         ri rh)
       (pair-substituted m σ (l₁ ⊔ℕ l₁) l₁ (Univalence.arrow l₁ l₁ X X)
         (Univalence.retraction-homotopy l₁ l₁ X X i) i h
         (Univalence.arrow l₁ l₁ X′ X′)
         (Univalence.retraction-homotopy l₁ l₁ X′ X′ i′) i′ h′ rA
         (retraction-homotopy-substituted m σ l₁ l₁ X X i X′ X′ i′
           rX rX ri)
         ri rh)

-- ≃-refl X.
identity-equivalence-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ : ℕ)
  (X : Raw.Expression C n) (X′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ X) X′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ
        (Univalence.identity-equivalence l₁ X))
      (Univalence.identity-equivalence l₁ X′)
identity-equivalence-substituted {C} m σ l₁ X X′ rX =
  let rX₁ = weakened-substituted m σ X X′ rX
  in pair-substituted m σ (l₁ ⊔ℕ l₁) (l₁ ⊔ℕ l₁)
       (Univalence.arrow l₁ l₁ X X)
       (Univalence.is-equiv l₁ l₁ (weaken X) (weaken X) (Tree.hole fzero))
       (Univalence.identity-function l₁ X) (Univalence.id-is-equiv l₁ X)
       (Univalence.arrow l₁ l₁ X′ X′)
       (Univalence.is-equiv l₁ l₁ (weaken X′) (weaken X′)
         (Tree.hole fzero))
       (Univalence.identity-function l₁ X′) (Univalence.id-is-equiv l₁ X′)
       (arrow-substituted m σ l₁ l₁ X X X′ X′ rX rX)
       (is-equiv-substituted (suc m) (Lifting.lifted (Raw.binding C) m 1 σ)
         l₁ l₁ (weaken X) (weaken X) (Tree.hole fzero)
         (weaken X′) (weaken X′) (Tree.hole fzero) rX₁ rX₁
         (Lifting.identical (Tree.hole fzero)))
       (identity-function-substituted m σ l₁ X X′ rX)
       (id-is-equiv-substituted m σ l₁ X X′ rX)

------------------------------------------------------------------------
-- idtoeq

idtoeq-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l : ℕ)
  (X Y : Raw.Expression C n) (X′ Y′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ X) X′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ Y) Y′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ (Univalence.idtoeq l X Y))
      (Univalence.idtoeq l X′ Y′)
idtoeq-substituted {C} m σ l X Y X′ Y′ rX rY =
  let τ = Lifting.lifted (Raw.binding C) m 1 σ
      ρ = Lifting.lifted (Raw.binding C) (suc m) 2 τ
      ρ₁ = Lifting.lifted (Raw.binding C) (suc (suc m)) 1
             (Lifting.lifted (Raw.binding C) (suc m) 1 τ)
      rX₁ = weakened-substituted m σ X X′ rX
      rY₁ = weakened-substituted m σ Y Y′ rY
      X₁ = weaken X
      X₁′ = weaken X′
      X₃ = weaken (weaken (weaken X))
      X₃′ = weaken (weaken (weaken X′))
      rX₃ = Relation.rel-compose _∙_
              (Lifting.substitute-pointwise-rel (Raw.binding C)
                (suc (suc (suc m))) ρ ρ₁
                (Lifting.lifted-twice (Raw.binding C) (suc m) τ) X₃)
              (weakened-substituted (suc (suc m))
                (Lifting.lifted (Raw.binding C) (suc m) 1 τ)
                (weaken (weaken X)) (weaken (weaken X′))
                (weakened-substituted (suc m) τ (weaken X) (weaken X′) rX₁))
      E₁₁ = Univalence.equivalence l l X₁ X₁
      E₁₁′ = Univalence.equivalence l l X₁′ X₁′
      E₁₂ = Univalence.equivalence l l X₁ (weaken Y)
      E₁₂′ = Univalence.equivalence l l X₁′ (weaken Y′)
      rE₁₁ = equivalence-substituted (suc m) τ l l X₁ X₁ X₁′ X₁′ rX₁ rX₁
      rE₁₂ = equivalence-substituted (suc m) τ l l X₁ (weaken Y) X₁′
               (weaken Y′) rX₁ rY₁
      E₃₃ = Univalence.equivalence l l X₃ X₃
      E₃₃′ = Univalence.equivalence l l X₃′ X₃′
      E₃y = Univalence.equivalence l l X₃ (Tree.hole (fsuc fzero))
      E₃y′ = Univalence.equivalence l l X₃′ (Tree.hole (fsuc fzero))
      M = Univalence.arrow l l E₃₃ E₃y
      M′ = Univalence.arrow l l E₃₃′ E₃y′
      rM = arrow-substituted (suc (suc (suc m))) ρ l l E₃₃ E₃y E₃₃′ E₃y′
             (equivalence-substituted (suc (suc (suc m))) ρ l l X₃ X₃
               X₃′ X₃′ rX₃ rX₃)
             (equivalence-substituted (suc (suc (suc m))) ρ l l X₃
               (Tree.hole (fsuc fzero)) X₃′
               (Tree.hole (fsuc fzero)) rX₃
               (Lifting.identical (Tree.hole (fsuc fzero))))
      i = Univalence.identity-function l E₁₁
      i′ = Univalence.identity-function l E₁₁′
      J = path-induction (suc l) l (universe l) M X₁ i (weaken Y)
            (Tree.hole fzero)
      J′ = path-induction (suc l) l (universe l) M′ X₁′ i′ (weaken Y′)
             (Tree.hole fzero)
      rJ = path-induction-substituted (suc m) τ (suc l) l (universe l) M X₁
             i (weaken Y) (Tree.hole fzero) (universe l) M′ X₁′ i′
             (weaken Y′) (Tree.hole fzero)
             (universe-substituted (suc m) τ l) rM rX₁
             (identity-function-substituted (suc m) τ l E₁₁ E₁₁′ rE₁₁)
             rY₁ (Lifting.identical (Tree.hole fzero))
      e = Univalence.identity-equivalence l X₁
      e′ = Univalence.identity-equivalence l X₁′
  in lambda-substituted m σ (suc l) l (identity (suc l) (universe l) X Y)
       (weaken (Univalence.equivalence l l X Y))
       (Univalence.call l l E₁₁ E₁₂ J e)
       (identity (suc l) (universe l) X′ Y′)
       (weaken (Univalence.equivalence l l X′ Y′))
       (Univalence.call l l E₁₁′ E₁₂′ J′ e′)
       (identity-substituted m σ (suc l) (universe l) X Y (universe l) X′ Y′
         (universe-substituted m σ l) rX rY)
       (weakened-substituted m σ (Univalence.equivalence l l X Y)
         (Univalence.equivalence l l X′ Y′)
         (equivalence-substituted m σ l l X Y X′ Y′ rX rY))
       (call-substituted (suc m) τ l l E₁₁ E₁₂ J e E₁₁′ E₁₂′ J′ e′
         rE₁₁ rE₁₂ rJ
         (identity-equivalence-substituted (suc m) τ l X₁ X₁′ rX₁))

------------------------------------------------------------------------
-- Weakened parts, and X → Y along the relation

-- X → Y keeps the structural relation.
arrow-related :
  {C : Set} {n : ℕ} (l₁ l₂ : ℕ) (X Y X′ Y′ : Raw.Expression C n)
  → Relation.TreeRel _＝_ X X′ → Relation.TreeRel _＝_ Y Y′
  → Relation.TreeRel _＝_
      (Univalence.arrow l₁ l₂ X Y) (Univalence.arrow l₁ l₂ X′ Y′)
arrow-related {C} {n} l₁ l₂ X Y X′ Y′ rX rY =
  Relation.node-rel
    (λ { Raw.pi-domain → rX
       ; Raw.pi-codomain →
           Lifting.bound-related (Raw.binding C) n 1
             (weaken-related Y Y′ rY) })

-- X ＝ Y in U at l, weakened.
paths-weakened :
  {C : Set} {n : ℕ} (l : ℕ) (X Y : Raw.Expression C n)
  (X′ Y′ : Raw.Expression C (suc n))
  → Relation.TreeRel _＝_ (weaken X) X′ → Relation.TreeRel _＝_ (weaken Y) Y′
  → Relation.TreeRel _＝_
      (weaken (identity (suc l) (universe l) X Y))
      (identity (suc l) (universe l) X′ Y′)
paths-weakened {C} {n} l X Y X′ Y′ rX rY =
  weakened-as (identity (suc l) (universe l) X Y)
    (identity (suc l) (universe l) X′ Y′)
    (identity-substituted (suc n) (λ i → Tree.hole (fsuc i)) (suc l)
      (universe l) X Y (universe l) X′ Y′
      (universe-substituted (suc n) (λ i → Tree.hole (fsuc i)) l)
      (shifted-from X X′ rX) (shifted-from Y Y′ rY))

-- X → Y, weakened.
arrow-weakened :
  {C : Set} {n : ℕ} (l₁ l₂ : ℕ) (X Y : Raw.Expression C n)
  (X′ Y′ : Raw.Expression C (suc n))
  → Relation.TreeRel _＝_ (weaken X) X′ → Relation.TreeRel _＝_ (weaken Y) Y′
  → Relation.TreeRel _＝_
      (weaken (Univalence.arrow l₁ l₂ X Y)) (Univalence.arrow l₁ l₂ X′ Y′)
arrow-weakened {C} {n} l₁ l₂ X Y X′ Y′ rX rY =
  weakened-as (Univalence.arrow l₁ l₂ X Y) (Univalence.arrow l₁ l₂ X′ Y′)
    (arrow-substituted (suc n) (λ i → Tree.hole (fsuc i)) l₁ l₂
      X Y X′ Y′ (shifted-from X X′ rX) (shifted-from Y Y′ rY))

-- X ≃ Y, weakened.
equivalence-weakened :
  {C : Set} {n : ℕ} (l₁ l₂ : ℕ) (X Y : Raw.Expression C n)
  (X′ Y′ : Raw.Expression C (suc n))
  → Relation.TreeRel _＝_ (weaken X) X′ → Relation.TreeRel _＝_ (weaken Y) Y′
  → Relation.TreeRel _＝_
      (weaken (Univalence.equivalence l₁ l₂ X Y))
      (Univalence.equivalence l₁ l₂ X′ Y′)
equivalence-weakened {C} {n} l₁ l₂ X Y X′ Y′ rX rY =
  weakened-as (Univalence.equivalence l₁ l₂ X Y)
    (Univalence.equivalence l₁ l₂ X′ Y′)
    (equivalence-substituted (suc n) (λ i → Tree.hole (fsuc i)) l₁ l₂
      X Y X′ Y′ (shifted-from X X′ rX) (shifted-from Y Y′ rY))

-- is-section f, weakened.
is-section-weakened :
  {C : Set} {n : ℕ} (l₁ l₂ : ℕ) (X Y f : Raw.Expression C n)
  (X′ Y′ f′ : Raw.Expression C (suc n))
  → Relation.TreeRel _＝_ (weaken X) X′ → Relation.TreeRel _＝_ (weaken Y) Y′
  → Relation.TreeRel _＝_ (weaken f) f′
  → Relation.TreeRel _＝_
      (weaken (Univalence.is-section l₁ l₂ X Y f))
      (Univalence.is-section l₁ l₂ X′ Y′ f′)
is-section-weakened {C} {n} l₁ l₂ X Y f X′ Y′ f′ rX rY rf =
  weakened-as (Univalence.is-section l₁ l₂ X Y f)
    (Univalence.is-section l₁ l₂ X′ Y′ f′)
    (is-section-substituted (suc n) (λ i → Tree.hole (fsuc i)) l₁ l₂
      X Y f X′ Y′ f′ (shifted-from X X′ rX) (shifted-from Y Y′ rY)
      (shifted-from f f′ rf))

-- idtoeq X Y, weakened.
idtoeq-weakened :
  {C : Set} {n : ℕ} (l : ℕ) (X Y : Raw.Expression C n)
  (X′ Y′ : Raw.Expression C (suc n))
  → Relation.TreeRel _＝_ (weaken X) X′ → Relation.TreeRel _＝_ (weaken Y) Y′
  → Relation.TreeRel _＝_
      (weaken (Univalence.idtoeq l X Y)) (Univalence.idtoeq l X′ Y′)
idtoeq-weakened {C} {n} l X Y X′ Y′ rX rY =
  weakened-as (Univalence.idtoeq l X Y) (Univalence.idtoeq l X′ Y′)
    (idtoeq-substituted (suc n) (λ i → Tree.hole (fsuc i)) l
      X Y X′ Y′ (shifted-from X X′ rX) (shifted-from Y Y′ rY))
