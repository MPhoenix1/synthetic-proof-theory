{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Univalence.Formation where

-- The statement of univalence (Univalence) is a type at level suc l in
-- the empty context (`univalence-type`), so the constant univalence l is
-- a term of it in every valid context (`univalence-term`, the constant
-- rule). Its parts are typed in every valid context, with the types X and
-- Y of U at l given as variables at positions a and b (codes):
-- - X ＝ Y in U, and X ≃ Y, whose is-equiv has variables for the types and
--   the map (`paths-type`, `has-section-variables-type`,
--   `is-section-variables-type`, `is-equiv-variables-type`,
--   `equivalence-type`);
-- - the identity function, λ x → refl at id (id x) ＝ x by two β steps,
--   id-is-equiv and ≃-refl (`identity-function-term`, `refl-homotopy-term`,
--   `has-section-identity-type`, `is-section-identity-type`,
--   `id-is-equiv-term`, `identity-equivalence-term`);
-- - idtoeq X Y : (X ＝ Y) → X ≃ Y, by J into (y , q) ↦ ((X ≃ X) → (X ≃ y))
--   at the identity function (`idtoeq-term`), and is-equiv (idtoeq X Y)
--   (`has-section-idtoeq-type`, `is-section-idtoeq-type`,
--   `is-equiv-idtoeq-type`).
-- A step that meets a weakened or substituted expression moves it to its
-- literal form along structural relation. Up to ≃-refl the
-- compared trees are shallow and are compared by skeletons (Derived's
-- `reshaped`, by `refl`); from idtoeq on, by the structural laws of
-- substitution (Univalence.Substitution, Formers.Substitution; Derived's
-- `rewritten`), which compose along the parts at variables. Levels
-- written by value meet the formation rules' levels through ⊔.

open import SPT.Base
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Tree as Tree
import SPT.Foundation.Tree.Relation as Relation
import SPT.Foundation.Tree.Binding.Lifting as Lifting
open import SPT.MartinLof.Derived using
  (empty-context; extended-context; rewritten; reshaped; equal-reshaped
  ; leveled; type-leveled; Assumed; newest-related; older-related; newest
  ; older; assumed; universe-type; pi-type; sigma-type; identity-type
  ; lambda-term; application-term; beta; pair-term; reflexivity-term
  ; path-induction-term; identity-equal; reflexive; symmetric; transitive
  ; conversion)
open import SPT.MartinLof.Formers using
  (universe; pi; lambda; application; pair; identity; reflexivity
  ; path-induction; constant; weaken; closed; extended; instantiate
  ; instantiate₂)
open import SPT.MartinLof.Formers.Substitution using
  (weaken-related; instantiate-weakened)
open import SPT.MartinLof.Judgment using
  (Context; ∅; _▸[_]_; context; term; term-equal; type)
import SPT.MartinLof.Raw as Raw
import SPT.MartinLof.Rules.Constant as Constants
open import SPT.MartinLof.Skeleton using (skeleton)
import SPT.MartinLof.Theory as Theory
import SPT.MartinLof.Univalence as Univalence
open import SPT.MartinLof.Univalence.Substitution using
  (arrow-substituted; arrow-related; equivalence-substituted; paths-weakened
  ; arrow-weakened; equivalence-weakened; is-section-weakened; idtoeq-weakened)

------------------------------------------------------------------------
-- Codes

-- A variable of type U at l, as a type at level l.
code-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (a : Fin n)
  → Theory.Derivation (context Γ) → Assumed Γ a (suc l) (universe l)
  → Theory.Derivation (type Γ l (Tree.hole a))
code-type Γ l a v c = assumed Γ a (suc l) (universe l) v c

-- The same variable past a further one.
code-older :
  {n : ℕ} (Γ : Context Theory.Constant n) (k : ℕ)
  (B : Raw.Expression Theory.Constant n) (l : ℕ) (a : Fin n)
  → Assumed Γ a (suc l) (universe l)
  → Assumed (Γ ▸[ k ] B) (fsuc a) (suc l) (universe l)
code-older Γ k B l a c = older Γ k B a (suc l) (universe l) (universe l) c refl

-- X ＝ Y in U, for codes X and Y.
paths-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (a b : Fin n)
  → Theory.Derivation (context Γ) → Assumed Γ a (suc l) (universe l)
  → Assumed Γ b (suc l) (universe l)
  → Theory.Derivation
      (type Γ (suc l)
        (identity (suc l) (universe l) (Tree.hole a) (Tree.hole b)))
paths-type Γ l a b v ca cb =
  identity-type Γ (suc l) (universe l) (Tree.hole a) (Tree.hole b)
    (universe-type Γ l v) (code-type Γ l a v ca) (code-type Γ l b v cb)

------------------------------------------------------------------------
-- Equivalences between codes, with variables for the types and the map

-- The functions from X to Y, for codes X and Y: a type at level l ⊔ l.
arrow-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (a b : Fin n)
  → Theory.Derivation (context Γ) → Assumed Γ a (suc l) (universe l)
  → Assumed Γ b (suc l) (universe l)
  → Theory.Derivation
      (type Γ (l ⊔ℕ l) (Univalence.arrow l l (Tree.hole a) (Tree.hole b)))
arrow-type Γ l a b v ca cb =
  let dA = code-type Γ l a v ca
  in pi-type Γ l l (Tree.hole a) (Tree.hole (fsuc b)) dA
       (code-type (Γ ▸[ l ] Tree.hole a) l (fsuc b)
         (extended-context Γ l (Tree.hole a) dA)
         (code-older Γ l (Tree.hole a) l b cb))

-- The map f, a variable from X to Y.
Mapped :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (a b z : Fin n) → Set
Mapped Γ l a b z =
  Assumed Γ z (l ⊔ℕ l) (Univalence.arrow l l (Tree.hole a) (Tree.hole b))

mapped-older :
  {n : ℕ} (Γ : Context Theory.Constant n) (k : ℕ)
  (B : Raw.Expression Theory.Constant n) (l : ℕ) (a b z : Fin n)
  → Mapped Γ l a b z
  → Mapped (Γ ▸[ k ] B) l (fsuc a) (fsuc b) (fsuc z)
mapped-older Γ k B l a b z f =
  older Γ k B z (l ⊔ℕ l) (Univalence.arrow l l (Tree.hole a) (Tree.hole b))
    (Univalence.arrow l l (Tree.hole (fsuc a)) (Tree.hole (fsuc b)))
    f refl

-- f x, for f a variable from X to Y and x an element of X: an element
-- of Y.
mapped-term :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (a b z : Fin n)
  (x : Raw.Expression Theory.Constant n)
  → Theory.Derivation (context Γ) → Assumed Γ a (suc l) (universe l)
  → Assumed Γ b (suc l) (universe l) → Mapped Γ l a b z
  → Theory.Derivation (term Γ l x (Tree.hole a))
  → Theory.Derivation
      (term Γ l
        (Univalence.call l l (Tree.hole a) (Tree.hole b) (Tree.hole z) x)
        (Tree.hole b))
mapped-term Γ l a b z x v ca cb f dx =
  let dA = code-type Γ l a v ca
      F = Univalence.call l l (Tree.hole a) (Tree.hole b) (Tree.hole z) x
  in reshaped Γ l F F (instantiate (Tree.hole (fsuc b)) x) (Tree.hole b)
       refl refl
       (application-term Γ l l (Tree.hole a) (Tree.hole (fsuc b))
         (Tree.hole z) x dA
         (code-type (Γ ▸[ l ] Tree.hole a) l (fsuc b)
           (extended-context Γ l (Tree.hole a) dA)
           (code-older Γ l (Tree.hole a) l b cb))
         (assumed Γ z (l ⊔ℕ l)
           (Univalence.arrow l l (Tree.hole a) (Tree.hole b)) v f)
         dx)

-- has-section f, for codes X and Y and a variable f.
has-section-variables-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (x y z : Fin n)
  → Theory.Derivation (context Γ) → Assumed Γ x (suc l) (universe l)
  → Assumed Γ y (suc l) (universe l) → Mapped Γ l x y z
  → Theory.Derivation
      (type Γ (l ⊔ℕ l)
        (Univalence.has-section l l (Tree.hole x) (Tree.hole y)
          (Tree.hole z)))
has-section-variables-type Γ l x y z v cx cy f =
  let A = Univalence.arrow l l (Tree.hole y) (Tree.hole x)
      dA = arrow-type Γ l y x v cy cx
      Γ₁ = Γ ▸[ l ⊔ℕ l ] A
      v₁ = extended-context Γ (l ⊔ℕ l) A dA
      cy₁ = code-older Γ (l ⊔ℕ l) A l y cy
      s₁ = newest Γ (l ⊔ℕ l) A
             (Univalence.arrow l l (Tree.hole (fsuc y))
               (Tree.hole (fsuc x)))
             refl
      dY₁ = code-type Γ₁ l (fsuc y) v₁ cy₁
      Y₂ = Tree.hole (fsuc (fsuc y))
      Γ₂ = Γ₁ ▸[ l ] Tree.hole (fsuc y)
      v₂ = extended-context Γ₁ l (Tree.hole (fsuc y)) dY₁
      cx₂ = code-older Γ₁ l (Tree.hole (fsuc y)) l (fsuc x)
              (code-older Γ (l ⊔ℕ l) A l x cx)
      cy₂ = code-older Γ₁ l (Tree.hole (fsuc y)) l (fsuc y) cy₁
      f₂ = mapped-older Γ₁ l (Tree.hole (fsuc y)) l (fsuc x)
             (fsuc y) (fsuc z)
             (mapped-older Γ (l ⊔ℕ l) A l x y z f)
      s₂ = mapped-older Γ₁ l (Tree.hole (fsuc y)) l (fsuc y)
             (fsuc x) fzero s₁
      dy = assumed Γ₂ fzero l Y₂ v₂
             (newest Γ₁ l (Tree.hole (fsuc y)) Y₂ refl)
      inner = Univalence.call l l Y₂ (Tree.hole (fsuc (fsuc x)))
                (Tree.hole (fsuc fzero)) (Tree.hole fzero)
      d-inner = mapped-term Γ₂ l (fsuc (fsuc y)) (fsuc (fsuc x))
                  (fsuc fzero) (Tree.hole fzero) v₂ cy₂ cx₂ s₂ dy
      outer = Univalence.call l l (Tree.hole (fsuc (fsuc x))) Y₂
                (Tree.hole (fsuc (fsuc z))) inner
      d-outer = mapped-term Γ₂ l (fsuc (fsuc x)) (fsuc (fsuc y))
                  (fsuc (fsuc z)) inner v₂ cx₂ cy₂ f₂ d-inner
      H = Univalence.section-homotopy l l (Tree.hole x) (Tree.hole y)
            (Tree.hole z)
      dH = type-leveled Γ₁ (l ⊔ℕ l) l H (⊔ℕ-idempotent l)
             (pi-type Γ₁ l l (Tree.hole (fsuc y))
               (identity l Y₂ outer (Tree.hole fzero)) dY₁
               (identity-type Γ₂ l Y₂ outer (Tree.hole fzero)
                 (code-type Γ₂ l (fsuc (fsuc y)) v₂ cy₂) d-outer dy))
  in type-leveled Γ ((l ⊔ℕ l) ⊔ℕ l) (l ⊔ℕ l)
       (Univalence.has-section l l (Tree.hole x) (Tree.hole y) (Tree.hole z))
       (ap (λ k → k ⊔ℕ l) (⊔ℕ-idempotent l))
       (sigma-type Γ (l ⊔ℕ l) l A H dA dH)

-- is-section f, for codes X and Y and a variable f.
is-section-variables-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (x y z : Fin n)
  → Theory.Derivation (context Γ) → Assumed Γ x (suc l) (universe l)
  → Assumed Γ y (suc l) (universe l) → Mapped Γ l x y z
  → Theory.Derivation
      (type Γ (l ⊔ℕ l)
        (Univalence.is-section l l (Tree.hole x) (Tree.hole y)
          (Tree.hole z)))
is-section-variables-type Γ l x y z v cx cy f =
  let A = Univalence.arrow l l (Tree.hole y) (Tree.hole x)
      dA = arrow-type Γ l y x v cy cx
      Γ₁ = Γ ▸[ l ⊔ℕ l ] A
      v₁ = extended-context Γ (l ⊔ℕ l) A dA
      cx₁ = code-older Γ (l ⊔ℕ l) A l x cx
      r₁ = newest Γ (l ⊔ℕ l) A
             (Univalence.arrow l l (Tree.hole (fsuc y))
               (Tree.hole (fsuc x)))
             refl
      dX₁ = code-type Γ₁ l (fsuc x) v₁ cx₁
      X₂ = Tree.hole (fsuc (fsuc x))
      Γ₂ = Γ₁ ▸[ l ] Tree.hole (fsuc x)
      v₂ = extended-context Γ₁ l (Tree.hole (fsuc x)) dX₁
      cx₂ = code-older Γ₁ l (Tree.hole (fsuc x)) l (fsuc x) cx₁
      cy₂ = code-older Γ₁ l (Tree.hole (fsuc x)) l (fsuc y)
              (code-older Γ (l ⊔ℕ l) A l y cy)
      f₂ = mapped-older Γ₁ l (Tree.hole (fsuc x)) l (fsuc x)
             (fsuc y) (fsuc z)
             (mapped-older Γ (l ⊔ℕ l) A l x y z f)
      r₂ = mapped-older Γ₁ l (Tree.hole (fsuc x)) l (fsuc y)
             (fsuc x) fzero r₁
      dx = assumed Γ₂ fzero l X₂ v₂
             (newest Γ₁ l (Tree.hole (fsuc x)) X₂ refl)
      inner = Univalence.call l l X₂ (Tree.hole (fsuc (fsuc y)))
                (Tree.hole (fsuc (fsuc z))) (Tree.hole fzero)
      d-inner = mapped-term Γ₂ l (fsuc (fsuc x)) (fsuc (fsuc y))
                  (fsuc (fsuc z)) (Tree.hole fzero) v₂ cx₂ cy₂ f₂ dx
      outer = Univalence.call l l (Tree.hole (fsuc (fsuc y))) X₂
                (Tree.hole (fsuc fzero)) inner
      d-outer = mapped-term Γ₂ l (fsuc (fsuc y)) (fsuc (fsuc x))
                  (fsuc fzero) inner v₂ cy₂ cx₂ r₂ d-inner
      H = Univalence.retraction-homotopy l l (Tree.hole x) (Tree.hole y)
            (Tree.hole z)
      dH = type-leveled Γ₁ (l ⊔ℕ l) l H (⊔ℕ-idempotent l)
             (pi-type Γ₁ l l (Tree.hole (fsuc x))
               (identity l X₂ outer (Tree.hole fzero)) dX₁
               (identity-type Γ₂ l X₂ outer (Tree.hole fzero)
                 (code-type Γ₂ l (fsuc (fsuc x)) v₂ cx₂) d-outer dx))
  in type-leveled Γ ((l ⊔ℕ l) ⊔ℕ l) (l ⊔ℕ l)
       (Univalence.is-section l l (Tree.hole x) (Tree.hole y) (Tree.hole z))
       (ap (λ k → k ⊔ℕ l) (⊔ℕ-idempotent l))
       (sigma-type Γ (l ⊔ℕ l) l A H dA dH)

-- is-equiv f, for codes X and Y and a variable f.
is-equiv-variables-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (x y z : Fin n)
  → Theory.Derivation (context Γ) → Assumed Γ x (suc l) (universe l)
  → Assumed Γ y (suc l) (universe l) → Mapped Γ l x y z
  → Theory.Derivation
      (type Γ (l ⊔ℕ l)
        (Univalence.is-equiv l l (Tree.hole x) (Tree.hole y) (Tree.hole z)))
is-equiv-variables-type Γ l x y z v cx cy f =
  let S = Univalence.has-section l l (Tree.hole x) (Tree.hole y)
            (Tree.hole z)
      dS = has-section-variables-type Γ l x y z v cx cy f
      Γ₁ = Γ ▸[ l ⊔ℕ l ] S
      v₁ = extended-context Γ (l ⊔ℕ l) S dS
      dR = reshaped Γ₁ (suc (l ⊔ℕ l))
             (Univalence.is-section l l (Tree.hole (fsuc x))
               (Tree.hole (fsuc y)) (Tree.hole (fsuc z)))
             (weaken
               (Univalence.is-section l l (Tree.hole x) (Tree.hole y)
                 (Tree.hole z)))
             (universe (l ⊔ℕ l)) (universe (l ⊔ℕ l)) refl refl
             (is-section-variables-type Γ₁ l (fsuc x) (fsuc y)
               (fsuc z) v₁ (code-older Γ (l ⊔ℕ l) S l x cx)
               (code-older Γ (l ⊔ℕ l) S l y cy)
               (mapped-older Γ (l ⊔ℕ l) S l x y z f))
  in type-leveled Γ ((l ⊔ℕ l) ⊔ℕ (l ⊔ℕ l)) (l ⊔ℕ l)
       (Univalence.is-equiv l l (Tree.hole x) (Tree.hole y) (Tree.hole z))
       (⊔ℕ-idempotent (l ⊔ℕ l))
       (sigma-type Γ (l ⊔ℕ l) (l ⊔ℕ l) S
         (weaken
           (Univalence.is-section l l (Tree.hole x) (Tree.hole y)
             (Tree.hole z)))
         dS dR)

-- X ≃ Y, for codes X and Y: a type at level l.
equivalence-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (a b : Fin n)
  → Theory.Derivation (context Γ) → Assumed Γ a (suc l) (universe l)
  → Assumed Γ b (suc l) (universe l)
  → Theory.Derivation
      (type Γ l (Univalence.equivalence l l (Tree.hole a) (Tree.hole b)))
equivalence-type Γ l a b v ca cb =
  let A = Univalence.arrow l l (Tree.hole a) (Tree.hole b)
      dA = arrow-type Γ l a b v ca cb
      Γ₁ = Γ ▸[ l ⊔ℕ l ] A
      v₁ = extended-context Γ (l ⊔ℕ l) A dA
  in type-leveled Γ ((l ⊔ℕ l) ⊔ℕ (l ⊔ℕ l)) l
       (Univalence.equivalence l l (Tree.hole a) (Tree.hole b))
       (⊔ℕ-idempotent (l ⊔ℕ l) ∙ ⊔ℕ-idempotent l)
       (sigma-type Γ (l ⊔ℕ l) (l ⊔ℕ l) A
         (Univalence.is-equiv l l (Tree.hole (fsuc a))
           (Tree.hole (fsuc b)) (Tree.hole fzero))
         dA
         (is-equiv-variables-type Γ₁ l (fsuc a) (fsuc b) fzero v₁
           (code-older Γ (l ⊔ℕ l) A l a ca) (code-older Γ (l ⊔ℕ l) A l b cb)
           (newest Γ (l ⊔ℕ l) A
             (Univalence.arrow l l (Tree.hole (fsuc a))
               (Tree.hole (fsuc b)))
             refl)))

------------------------------------------------------------------------
-- The identity equivalence of a code

-- id, for a type T given with its weakening.
identity-function-term :
  {n : ℕ} (Γ : Context Theory.Constant n) (m : ℕ)
  (T : Raw.Expression Theory.Constant n)
  → Theory.Derivation (type Γ m T)
  → Theory.Derivation (type (Γ ▸[ m ] T) m (weaken T))
  → Theory.Derivation
      (term Γ (m ⊔ℕ m) (Univalence.identity-function m T)
        (Univalence.arrow m m T T))
identity-function-term Γ m T dT dT₁ =
  lambda-term Γ m m T (weaken T) (Tree.hole fzero) dT dT₁
    (assumed (Γ ▸[ m ] T) fzero m (weaken T)
      (extended-context Γ m T dT) (newest Γ m T (weaken T) refl))

-- id on a code X, at level l.
identity-code-term :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (x : Fin n)
  → Theory.Derivation (context Γ) → Assumed Γ x (suc l) (universe l)
  → Theory.Derivation
      (term Γ (l ⊔ℕ l) (Univalence.identity-function l (Tree.hole x))
        (Univalence.arrow l l (Tree.hole x) (Tree.hole x)))
identity-code-term Γ l x v c =
  let dX = code-type Γ l x v c
  in identity-function-term Γ l (Tree.hole x) dX
       (code-type (Γ ▸[ l ] Tree.hole x) l (fsuc x)
         (extended-context Γ l (Tree.hole x) dX)
         (code-older Γ l (Tree.hole x) l x c))

-- id u, an element of a code X for u one.
identity-applied :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (x : Fin n)
  (u : Raw.Expression Theory.Constant n)
  → Theory.Derivation (context Γ) → Assumed Γ x (suc l) (universe l)
  → Theory.Derivation (term Γ l u (Tree.hole x))
  → Theory.Derivation
      (term Γ l
        (Univalence.call l l (Tree.hole x) (Tree.hole x)
          (Univalence.identity-function l (Tree.hole x)) u)
        (Tree.hole x))
identity-applied Γ l x u v c du =
  let dX = code-type Γ l x v c
      F = Univalence.call l l (Tree.hole x) (Tree.hole x)
            (Univalence.identity-function l (Tree.hole x)) u
  in reshaped Γ l F F (instantiate (Tree.hole (fsuc x)) u) (Tree.hole x)
       refl refl
       (application-term Γ l l (Tree.hole x) (Tree.hole (fsuc x))
         (Univalence.identity-function l (Tree.hole x)) u dX
         (code-type (Γ ▸[ l ] Tree.hole x) l (fsuc x)
           (extended-context Γ l (Tree.hole x) dX)
           (code-older Γ l (Tree.hole x) l x c))
         (identity-code-term Γ l x v c) du)

-- id u ＝ u, by the β rule.
identity-computes :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (x : Fin n)
  (u : Raw.Expression Theory.Constant n)
  → Theory.Derivation (context Γ) → Assumed Γ x (suc l) (universe l)
  → Theory.Derivation (term Γ l u (Tree.hole x))
  → skeleton (instantiate (Tree.hole fzero) u) ＝ skeleton u
  → Theory.Derivation
      (term-equal Γ l
        (Univalence.call l l (Tree.hole x) (Tree.hole x)
          (Univalence.identity-function l (Tree.hole x)) u)
        u (Tree.hole x))
identity-computes Γ l x u v c du eu =
  let dX = code-type Γ l x v c
      v₁ = extended-context Γ l (Tree.hole x) dX
      c₁ = code-older Γ l (Tree.hole x) l x c
      X₁ = Tree.hole (fsuc x)
  in equal-reshaped Γ l
       (application l l (Tree.hole x) X₁
         (lambda l l (Tree.hole x) X₁ (Tree.hole fzero)) u)
       (Univalence.call l l (Tree.hole x) (Tree.hole x)
         (Univalence.identity-function l (Tree.hole x)) u)
       (instantiate (Tree.hole fzero) u) u
       (instantiate X₁ u) (Tree.hole x) refl eu refl
       (beta Γ l l (Tree.hole x) X₁ (Tree.hole fzero) u dX
         (code-type (Γ ▸[ l ] Tree.hole x) l (fsuc x) v₁ c₁)
         (assumed (Γ ▸[ l ] Tree.hole x) fzero l X₁ v₁
           (newest Γ l (Tree.hole x) X₁ refl))
         du)

-- λ x → refl, of type Π x. id (id x) ＝ x, for a code X.
refl-homotopy-term :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (x : Fin n)
  → Theory.Derivation (context Γ) → Assumed Γ x (suc l) (universe l)
  → Theory.Derivation
      (term Γ (l ⊔ℕ l) (Univalence.refl-homotopy l (Tree.hole x))
        (pi l l (Tree.hole x)
          (identity l (Tree.hole (fsuc x))
            (Univalence.call l l (Tree.hole (fsuc x))
              (Tree.hole (fsuc x))
              (weaken (Univalence.identity-function l (Tree.hole x)))
              (Univalence.call l l (Tree.hole (fsuc x))
                (Tree.hole (fsuc x))
                (weaken (Univalence.identity-function l (Tree.hole x)))
                (Tree.hole fzero)))
            (Tree.hole fzero))))
refl-homotopy-term Γ l x v c =
  let dX = code-type Γ l x v c
      Γ₁ = Γ ▸[ l ] Tree.hole x
      v₁ = extended-context Γ l (Tree.hole x) dX
      x₁ = fsuc x
      X₁ = Tree.hole x₁
      c₁ = code-older Γ l (Tree.hole x) l x c
      dX₁ = code-type Γ₁ l x₁ v₁ c₁
      w = Tree.hole fzero
      dw = assumed Γ₁ fzero l X₁ v₁ (newest Γ l (Tree.hole x) X₁ refl)
      i = Univalence.identity-function l X₁
      i′ = weaken (Univalence.identity-function l (Tree.hole x))
      iw = Univalence.call l l X₁ X₁ i w
      iiw = Univalence.call l l X₁ X₁ i iw
      iw′ = Univalence.call l l X₁ X₁ i′ w
      iiw′ = Univalence.call l l X₁ X₁ i′ iw′
      diw = identity-applied Γ₁ l x₁ w v₁ c₁ dw
      e₁ = identity-computes Γ₁ l x₁ w v₁ c₁ dw refl
      e₂ = identity-computes Γ₁ l x₁ iw v₁ c₁ diw refl
      eii = equal-reshaped Γ₁ l iiw iiw′ w w X₁ X₁ refl refl refl
              (transitive Γ₁ l iiw iw w X₁ e₂ e₁)
      dXX = reflexive Γ₁ (suc l) X₁ (universe l) dX₁
      dId = identity-equal Γ₁ l X₁ X₁ w iiw′ w w dXX
              (symmetric Γ₁ l iiw′ w X₁ eii) (reflexive Γ₁ l w X₁ dw)
      B = identity l X₁ iiw′ w
      dB = identity-type Γ₁ l X₁ iiw′ w dX₁
             (reshaped Γ₁ l iiw iiw′ X₁ X₁ refl refl
               (identity-applied Γ₁ l x₁ iw v₁ c₁ diw))
             dw
  in lambda-term Γ l l (Tree.hole x) B (reflexivity l X₁ w) dX dB
       (conversion Γ₁ l (reflexivity l X₁ w) (identity l X₁ w w) B
         (reflexivity-term Γ₁ l X₁ w dX₁ dw) dId)

-- f ∘ s ∼ id at f = id, for a code X, in the scope of s.
section-identity-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (x : Fin n)
  → Theory.Derivation (context Γ) → Assumed Γ x (suc l) (universe l)
  → Theory.Derivation
      (type (Γ ▸[ l ⊔ℕ l ] Univalence.arrow l l (Tree.hole x) (Tree.hole x))
        l
        (Univalence.section-homotopy l l (Tree.hole x) (Tree.hole x)
          (Univalence.identity-function l (Tree.hole x))))
section-identity-type Γ l x v c =
  let A = Univalence.arrow l l (Tree.hole x) (Tree.hole x)
      Γ₁ = Γ ▸[ l ⊔ℕ l ] A
      v₁ = extended-context Γ (l ⊔ℕ l) A (arrow-type Γ l x x v c c)
      c₁ = code-older Γ (l ⊔ℕ l) A l x c
      s₁ = newest Γ (l ⊔ℕ l) A
             (Univalence.arrow l l (Tree.hole (fsuc x))
               (Tree.hole (fsuc x)))
             refl
      dX₁ = code-type Γ₁ l (fsuc x) v₁ c₁
      x₂ = fsuc (fsuc x)
      X₂ = Tree.hole x₂
      Γ₂ = Γ₁ ▸[ l ] Tree.hole (fsuc x)
      v₂ = extended-context Γ₁ l (Tree.hole (fsuc x)) dX₁
      c₂ = code-older Γ₁ l (Tree.hole (fsuc x)) l (fsuc x) c₁
      s₂ = mapped-older Γ₁ l (Tree.hole (fsuc x)) l (fsuc x)
             (fsuc x) fzero s₁
      dy = assumed Γ₂ fzero l X₂ v₂
             (newest Γ₁ l (Tree.hole (fsuc x)) X₂ refl)
      inner = Univalence.call l l X₂ X₂ (Tree.hole (fsuc fzero))
                (Tree.hole fzero)
      d-inner = mapped-term Γ₂ l x₂ x₂ (fsuc fzero) (Tree.hole fzero)
                  v₂ c₂ c₂ s₂ dy
      outer = Univalence.call l l X₂ X₂
                (weaken (weaken (Univalence.identity-function l (Tree.hole x))))
                inner
      d-outer = reshaped Γ₂ l
                  (Univalence.call l l X₂ X₂
                    (Univalence.identity-function l X₂) inner)
                  outer X₂ X₂ refl refl
                  (identity-applied Γ₂ l x₂ inner v₂ c₂ d-inner)
  in type-leveled Γ₁ (l ⊔ℕ l) l
       (Univalence.section-homotopy l l (Tree.hole x) (Tree.hole x)
         (Univalence.identity-function l (Tree.hole x)))
       (⊔ℕ-idempotent l)
       (pi-type Γ₁ l l (Tree.hole (fsuc x))
         (identity l X₂ outer (Tree.hole fzero)) dX₁
         (identity-type Γ₂ l X₂ outer (Tree.hole fzero)
           (code-type Γ₂ l x₂ v₂ c₂) d-outer dy))

-- r ∘ f ∼ id at f = id, for a code X, in the scope of r.
retraction-identity-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (x : Fin n)
  → Theory.Derivation (context Γ) → Assumed Γ x (suc l) (universe l)
  → Theory.Derivation
      (type (Γ ▸[ l ⊔ℕ l ] Univalence.arrow l l (Tree.hole x) (Tree.hole x))
        l
        (Univalence.retraction-homotopy l l (Tree.hole x) (Tree.hole x)
          (Univalence.identity-function l (Tree.hole x))))
retraction-identity-type Γ l x v c =
  let A = Univalence.arrow l l (Tree.hole x) (Tree.hole x)
      Γ₁ = Γ ▸[ l ⊔ℕ l ] A
      v₁ = extended-context Γ (l ⊔ℕ l) A (arrow-type Γ l x x v c c)
      c₁ = code-older Γ (l ⊔ℕ l) A l x c
      r₁ = newest Γ (l ⊔ℕ l) A
             (Univalence.arrow l l (Tree.hole (fsuc x))
               (Tree.hole (fsuc x)))
             refl
      dX₁ = code-type Γ₁ l (fsuc x) v₁ c₁
      x₂ = fsuc (fsuc x)
      X₂ = Tree.hole x₂
      Γ₂ = Γ₁ ▸[ l ] Tree.hole (fsuc x)
      v₂ = extended-context Γ₁ l (Tree.hole (fsuc x)) dX₁
      c₂ = code-older Γ₁ l (Tree.hole (fsuc x)) l (fsuc x) c₁
      r₂ = mapped-older Γ₁ l (Tree.hole (fsuc x)) l (fsuc x)
             (fsuc x) fzero r₁
      dz = assumed Γ₂ fzero l X₂ v₂
             (newest Γ₁ l (Tree.hole (fsuc x)) X₂ refl)
      inner = Univalence.call l l X₂ X₂
                (weaken (weaken (Univalence.identity-function l (Tree.hole x))))
                (Tree.hole fzero)
      d-inner = reshaped Γ₂ l
                  (Univalence.call l l X₂ X₂
                    (Univalence.identity-function l X₂) (Tree.hole fzero))
                  inner X₂ X₂ refl refl
                  (identity-applied Γ₂ l x₂ (Tree.hole fzero) v₂ c₂ dz)
      outer = Univalence.call l l X₂ X₂ (Tree.hole (fsuc fzero)) inner
      d-outer = mapped-term Γ₂ l x₂ x₂ (fsuc fzero) inner v₂ c₂ c₂ r₂
                  d-inner
  in type-leveled Γ₁ (l ⊔ℕ l) l
       (Univalence.retraction-homotopy l l (Tree.hole x) (Tree.hole x)
         (Univalence.identity-function l (Tree.hole x)))
       (⊔ℕ-idempotent l)
       (pi-type Γ₁ l l (Tree.hole (fsuc x))
         (identity l X₂ outer (Tree.hole fzero)) dX₁
         (identity-type Γ₂ l X₂ outer (Tree.hole fzero)
           (code-type Γ₂ l x₂ v₂ c₂) d-outer dz))

-- has-section id, for a code X.
has-section-identity-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (x : Fin n)
  → Theory.Derivation (context Γ) → Assumed Γ x (suc l) (universe l)
  → Theory.Derivation
      (type Γ (l ⊔ℕ l)
        (Univalence.has-section l l (Tree.hole x) (Tree.hole x)
          (Univalence.identity-function l (Tree.hole x))))
has-section-identity-type Γ l x v c =
  type-leveled Γ ((l ⊔ℕ l) ⊔ℕ l) (l ⊔ℕ l)
    (Univalence.has-section l l (Tree.hole x) (Tree.hole x)
      (Univalence.identity-function l (Tree.hole x)))
    (ap (λ k → k ⊔ℕ l) (⊔ℕ-idempotent l))
    (sigma-type Γ (l ⊔ℕ l) l (Univalence.arrow l l (Tree.hole x) (Tree.hole x))
      (Univalence.section-homotopy l l (Tree.hole x) (Tree.hole x)
        (Univalence.identity-function l (Tree.hole x)))
      (arrow-type Γ l x x v c c) (section-identity-type Γ l x v c))

-- is-section id, for a code X.
is-section-identity-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (x : Fin n)
  → Theory.Derivation (context Γ) → Assumed Γ x (suc l) (universe l)
  → Theory.Derivation
      (type Γ (l ⊔ℕ l)
        (Univalence.is-section l l (Tree.hole x) (Tree.hole x)
          (Univalence.identity-function l (Tree.hole x))))
is-section-identity-type Γ l x v c =
  type-leveled Γ ((l ⊔ℕ l) ⊔ℕ l) (l ⊔ℕ l)
    (Univalence.is-section l l (Tree.hole x) (Tree.hole x)
      (Univalence.identity-function l (Tree.hole x)))
    (ap (λ k → k ⊔ℕ l) (⊔ℕ-idempotent l))
    (sigma-type Γ (l ⊔ℕ l) l (Univalence.arrow l l (Tree.hole x) (Tree.hole x))
      (Univalence.retraction-homotopy l l (Tree.hole x) (Tree.hole x)
        (Univalence.identity-function l (Tree.hole x)))
      (arrow-type Γ l x x v c c) (retraction-identity-type Γ l x v c))

-- id-is-equiv X = (id , λ x → refl) , (id , λ x → refl).
id-is-equiv-term :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (x : Fin n)
  → Theory.Derivation (context Γ) → Assumed Γ x (suc l) (universe l)
  → Theory.Derivation
      (term Γ (l ⊔ℕ l) (Univalence.id-is-equiv l (Tree.hole x))
        (Univalence.is-equiv l l (Tree.hole x) (Tree.hole x)
          (Univalence.identity-function l (Tree.hole x))))
id-is-equiv-term Γ l x v c =
  let X = Tree.hole x
      i = Univalence.identity-function l X
      A = Univalence.arrow l l X X
      S = Univalence.has-section l l X X i
      R = Univalence.is-section l l X X i
      dA = arrow-type Γ l x x v c c
      di = identity-code-term Γ l x v c
      RH = pi l l X
             (identity l (Tree.hole (fsuc x))
               (Univalence.call l l (Tree.hole (fsuc x))
                 (Tree.hole (fsuc x)) (weaken i)
                 (Univalence.call l l (Tree.hole (fsuc x))
                   (Tree.hole (fsuc x)) (weaken i) (Tree.hole fzero)))
               (Tree.hole fzero))
      drh = leveled Γ (l ⊔ℕ l) l (Univalence.refl-homotopy l X) RH
              (⊔ℕ-idempotent l) (refl-homotopy-term Γ l x v c)
      HS = Univalence.section-homotopy l l X X i
      HR = Univalence.retraction-homotopy l l X X i
      s = pair (l ⊔ℕ l) l A HS i (Univalence.refl-homotopy l X)
      r = pair (l ⊔ℕ l) l A HR i (Univalence.refl-homotopy l X)
      ds = leveled Γ ((l ⊔ℕ l) ⊔ℕ l) (l ⊔ℕ l) s S
             (ap (λ k → k ⊔ℕ l) (⊔ℕ-idempotent l))
             (pair-term Γ (l ⊔ℕ l) l A HS i (Univalence.refl-homotopy l X) dA
               (section-identity-type Γ l x v c) di
               (reshaped Γ l (Univalence.refl-homotopy l X)
                 (Univalence.refl-homotopy l X) RH (instantiate HS i)
                 refl refl drh))
      dr = leveled Γ ((l ⊔ℕ l) ⊔ℕ l) (l ⊔ℕ l) r R
             (ap (λ k → k ⊔ℕ l) (⊔ℕ-idempotent l))
             (pair-term Γ (l ⊔ℕ l) l A HR i (Univalence.refl-homotopy l X) dA
               (retraction-identity-type Γ l x v c) di
               (reshaped Γ l (Univalence.refl-homotopy l X)
                 (Univalence.refl-homotopy l X) RH (instantiate HR i)
                 refl refl drh))
      dS = has-section-identity-type Γ l x v c
      Γ₁ = Γ ▸[ l ⊔ℕ l ] S
      v₁ = extended-context Γ (l ⊔ℕ l) S dS
      dR₁ = reshaped Γ₁ (suc (l ⊔ℕ l))
              (Univalence.is-section l l (Tree.hole (fsuc x))
                (Tree.hole (fsuc x))
                (Univalence.identity-function l (Tree.hole (fsuc x))))
              (weaken R) (universe (l ⊔ℕ l)) (universe (l ⊔ℕ l)) refl refl
              (is-section-identity-type Γ₁ l (fsuc x) v₁
                (code-older Γ (l ⊔ℕ l) S l x c))
  in leveled Γ ((l ⊔ℕ l) ⊔ℕ (l ⊔ℕ l)) (l ⊔ℕ l) (Univalence.id-is-equiv l X)
       (Univalence.is-equiv l l X X i) (⊔ℕ-idempotent (l ⊔ℕ l))
       (pair-term Γ (l ⊔ℕ l) (l ⊔ℕ l) S (weaken R) s r dS dR₁ ds
         (reshaped Γ (l ⊔ℕ l) r r R (instantiate (weaken R) s) refl refl dr))

-- ≃-refl X = id , id-is-equiv X: an element of X ≃ X, for a code X.
identity-equivalence-term :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (x : Fin n)
  → Theory.Derivation (context Γ) → Assumed Γ x (suc l) (universe l)
  → Theory.Derivation
      (term Γ l (Univalence.identity-equivalence l (Tree.hole x))
        (Univalence.equivalence l l (Tree.hole x) (Tree.hole x)))
identity-equivalence-term Γ l x v c =
  let X = Tree.hole x
      A = Univalence.arrow l l X X
      dA = arrow-type Γ l x x v c c
      Γ₁ = Γ ▸[ l ⊔ℕ l ] A
      v₁ = extended-context Γ (l ⊔ℕ l) A dA
      E = Univalence.is-equiv l l (Tree.hole (fsuc x))
            (Tree.hole (fsuc x)) (Tree.hole fzero)
      i = Univalence.identity-function l X
  in leveled Γ ((l ⊔ℕ l) ⊔ℕ (l ⊔ℕ l)) l (Univalence.identity-equivalence l X)
       (Univalence.equivalence l l X X)
       (⊔ℕ-idempotent (l ⊔ℕ l) ∙ ⊔ℕ-idempotent l)
       (pair-term Γ (l ⊔ℕ l) (l ⊔ℕ l) A E i (Univalence.id-is-equiv l X) dA
         (is-equiv-variables-type Γ₁ l (fsuc x) (fsuc x) fzero v₁
           (code-older Γ (l ⊔ℕ l) A l x c) (code-older Γ (l ⊔ℕ l) A l x c)
           (newest Γ (l ⊔ℕ l) A
             (Univalence.arrow l l (Tree.hole (fsuc x))
               (Tree.hole (fsuc x)))
             refl))
         (identity-code-term Γ l x v c)
         (reshaped Γ (l ⊔ℕ l) (Univalence.id-is-equiv l X)
           (Univalence.id-is-equiv l X) (Univalence.is-equiv l l X X i)
           (instantiate E i) refl refl (id-is-equiv-term Γ l x v c)))

------------------------------------------------------------------------
-- idtoeq and univalence
--
-- From here on, an expression met weakened or substituted is related to
-- its literal form by the structural laws of Univalence.Substitution and
-- Formers.Substitution, which compose along the parts; codes stay
-- variables, so every comparison is between parts at variables.

-- A type at level l built with U at l lives at suc l.
joined : (l : ℕ) → l ⊔ℕ suc l ＝ suc l
joined l = ≤ℕˢ-gives-⊔ℕ-right (≤ℕˢ-to-suc l)

-- suc l ⊔ l is suc l.
joined′ : (l : ℕ) → suc l ⊔ℕ l ＝ suc l
joined′ l = ≤ℕˢ-gives-⊔ℕ-left (≤ℕˢ-to-suc l)

-- idtoeq X Y : (X ＝ Y) → X ≃ Y, for codes X and Y.
idtoeq-term :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (a b : Fin n)
  → Theory.Derivation (context Γ) → Assumed Γ a (suc l) (universe l)
  → Assumed Γ b (suc l) (universe l)
  → Theory.Derivation
      (term Γ (suc l ⊔ℕ l) (Univalence.idtoeq l (Tree.hole a) (Tree.hole b))
        (Univalence.arrow (suc l) l
          (identity (suc l) (universe l) (Tree.hole a) (Tree.hole b))
          (Univalence.equivalence l l (Tree.hole a) (Tree.hole b))))
idtoeq-term {n} Γ l a b v ca cb =
  let X : Raw.Expression Theory.Constant n
      X = Tree.hole a
      Y : Raw.Expression Theory.Constant n
      Y = Tree.hole b
      a₁ = fsuc a
      b₁ = fsuc b
      X₁ : Raw.Expression Theory.Constant (suc n)
      X₁ = Tree.hole a₁
      Y₁ : Raw.Expression Theory.Constant (suc n)
      Y₁ = Tree.hole b₁
      P = identity (suc l) (universe l) X Y
      E = Univalence.equivalence l l X Y
      -- E weakened is X ≃ Y at the codes one further.
      rE = equivalence-weakened l l X Y X₁ Y₁
             (Lifting.identical X₁) (Lifting.identical Y₁)
      dP = paths-type Γ l a b v ca cb
      Γ₁ = Γ ▸[ suc l ] P
      v₁ = extended-context Γ (suc l) P dP
      ca₁ = code-older Γ (suc l) P l a ca
      cb₁ = code-older Γ (suc l) P l b cb
      E₁₁ = Univalence.equivalence l l X₁ X₁
      E₁₂ = Univalence.equivalence l l X₁ Y₁
      dE₁₁ = equivalence-type Γ₁ l a₁ a₁ v₁ ca₁ ca₁
      dE₁₂ = equivalence-type Γ₁ l a₁ b₁ v₁ ca₁ cb₁
      Γ₁₁ = Γ₁ ▸[ l ] E₁₁
      v₁₁ = extended-context Γ₁ l E₁₁ dE₁₁
      X₂ : Raw.Expression Theory.Constant (suc (suc n))
      X₂ = Tree.hole (fsuc a₁)
      Y₂ : Raw.Expression Theory.Constant (suc (suc n))
      Y₂ = Tree.hole (fsuc b₁)
      dE₁₁′ = rewritten Γ₁₁ (suc l) (Univalence.equivalence l l X₂ X₂)
                (weaken E₁₁) (universe l) (universe l)
                (Relation.rel-sym _⁻¹
                  (equivalence-weakened l l X₁ X₁ X₂ X₂
                    (Lifting.identical X₂) (Lifting.identical X₂)))
                (Lifting.identical (universe l))
                (equivalence-type Γ₁₁ l (fsuc a₁) (fsuc a₁) v₁₁
                  (code-older Γ₁ l E₁₁ l a₁ ca₁)
                  (code-older Γ₁ l E₁₁ l a₁ ca₁))
      dE₁₂′ = rewritten Γ₁₁ (suc l) (Univalence.equivalence l l X₂ Y₂)
                (weaken E₁₂) (universe l) (universe l)
                (Relation.rel-sym _⁻¹
                  (equivalence-weakened l l X₁ Y₁ X₂ Y₂
                    (Lifting.identical X₂) (Lifting.identical Y₂)))
                (Lifting.identical (universe l))
                (equivalence-type Γ₁₁ l (fsuc a₁) (fsuc b₁) v₁₁
                  (code-older Γ₁ l E₁₁ l a₁ ca₁)
                  (code-older Γ₁ l E₁₁ l b₁ cb₁))
      -- The context of the motive: y : U and q : X ＝ y.
      ΓU = Γ₁ ▸[ suc l ] universe l
      vU = extended-context Γ₁ (suc l) (universe l) (universe-type Γ₁ l v₁)
      a₂ = fsuc a₁
      ca₂ = code-older Γ₁ (suc l) (universe l) l a₁ ca₁
      cy = newest Γ₁ (suc l) (universe l) (universe l) refl
      Q = identity (suc l) (weaken (universe l)) (weaken X₁)
            (Tree.hole fzero)
      dQ = identity-type ΓU (suc l) (weaken (universe l)) (Tree.hole a₂)
             (Tree.hole fzero)
             (reshaped ΓU (suc (suc l)) (universe l) (weaken (universe l))
               (universe (suc l)) (universe (suc l)) refl refl
               (universe-type ΓU l vU))
             (assumed ΓU a₂ (suc l) (weaken (universe l)) vU
               (older Γ₁ (suc l) (universe l) a₁ (suc l) (universe l)
                 (weaken (universe l)) ca₁ refl))
             (assumed ΓU fzero (suc l) (weaken (universe l)) vU
               (newest Γ₁ (suc l) (universe l) (weaken (universe l)) refl))
      ΓP = ΓU ▸[ suc l ] Q
      vP = extended-context ΓU (suc l) Q dQ
      a₃ = fsuc a₂
      ca₃ = code-older ΓU (suc l) Q l a₂ ca₂
      cy₁ = code-older ΓU (suc l) Q l fzero cy
      X₃ : Raw.Expression Theory.Constant (suc (suc (suc n)))
      X₃ = Tree.hole a₃
      y₃ : Raw.Expression Theory.Constant (suc (suc (suc n)))
      y₃ = Tree.hole (fsuc fzero)
      E₃₃ = Univalence.equivalence l l X₃ X₃
      E₃y = Univalence.equivalence l l X₃ y₃
      M = Univalence.arrow l l E₃₃ E₃y
      dE₃₃ = equivalence-type ΓP l a₃ a₃ vP ca₃ ca₃
      ΓP₁ = ΓP ▸[ l ] E₃₃
      vP₁ = extended-context ΓP l E₃₃ dE₃₃
      X₄ : Raw.Expression Theory.Constant (suc (suc (suc (suc n))))
      X₄ = Tree.hole (fsuc a₃)
      y₄ : Raw.Expression Theory.Constant (suc (suc (suc (suc n))))
      y₄ = Tree.hole (fsuc (fsuc fzero))
      dM = type-leveled ΓP (l ⊔ℕ l) l M (⊔ℕ-idempotent l)
             (pi-type ΓP l l E₃₃ (weaken E₃y) dE₃₃
               (rewritten ΓP₁ (suc l) (Univalence.equivalence l l X₄ y₄)
                 (weaken E₃y) (universe l) (universe l)
                 (Relation.rel-sym _⁻¹
                   (equivalence-weakened l l X₃ y₃ X₄ y₄
                     (Lifting.identical X₄) (Lifting.identical y₄)))
                 (Lifting.identical (universe l))
                 (equivalence-type ΓP₁ l (fsuc a₃)
                   (fsuc (fsuc fzero)) vP₁
                   (code-older ΓP l E₃₃ l a₃ ca₃)
                   (code-older ΓP l E₃₃ l (fsuc fzero) cy₁))))
      -- J's method: the identity function, at the motive's instance at
      -- refl.
      i = Univalence.identity-function l E₁₁
      R = reflexivity (suc l) (universe l) X₁
      σ₀ = extended (extended (λ (j : Fin (suc n)) → Tree.hole j) X₁) R
      di = rewritten Γ₁ l i i (Univalence.arrow l l E₁₁ E₁₁)
             (instantiate₂ M X₁ R) (Lifting.identical i)
             (Relation.rel-sym _⁻¹
               (arrow-substituted (suc n) σ₀ l l E₃₃ E₃y E₁₁ E₁₁
                 (equivalence-substituted (suc n) σ₀ l l X₃ X₃ X₁ X₁
                   (Lifting.identical X₁) (Lifting.identical X₁))
                 (equivalence-substituted (suc n) σ₀ l l X₃ y₃ X₁ X₁
                   (Lifting.identical X₁) (Lifting.identical X₁))))
             (leveled Γ₁ (l ⊔ℕ l) l i (Univalence.arrow l l E₁₁ E₁₁)
               (⊔ℕ-idempotent l) (identity-function-term Γ₁ l E₁₁ dE₁₁ dE₁₁′))
      -- J at the path variable: from X ≃ X to X ≃ Y.
      P₁ = identity (suc l) (universe l) X₁ Y₁
      σ₁ = extended (extended (λ (j : Fin (suc n)) → Tree.hole j) Y₁)
             (Tree.hole fzero)
      J = path-induction (suc l) l (universe l) M X₁ i Y₁ (Tree.hole fzero)
      dJ =
        leveled Γ₁ l (l ⊔ℕ l) J (pi l l E₁₁ (weaken E₁₂)) (⊔ℕ-idempotent l ⁻¹)
             (rewritten Γ₁ l J J (instantiate₂ M Y₁ (Tree.hole fzero))
               (pi l l E₁₁ (weaken E₁₂)) (Lifting.identical J)
               (arrow-substituted (suc n) σ₁ l l E₃₃ E₃y E₁₁ E₁₂
                 (equivalence-substituted (suc n) σ₁ l l X₃ X₃ X₁ X₁
                   (Lifting.identical X₁) (Lifting.identical X₁))
                 (equivalence-substituted (suc n) σ₁ l l X₃ y₃ X₁ Y₁
                   (Lifting.identical X₁) (Lifting.identical Y₁)))
               (path-induction-term Γ₁ (suc l) l (universe l) M X₁ i Y₁
                 (Tree.hole fzero) (universe-type Γ₁ l v₁)
                 (code-type Γ₁ l a₁ v₁ ca₁) dM di (code-type Γ₁ l b₁ v₁ cb₁)
                 (assumed Γ₁ fzero (suc l) P₁ v₁
                   (newest-related Γ (suc l) P P₁
                     (paths-weakened l X Y X₁ Y₁
                       (Lifting.identical X₁) (Lifting.identical Y₁))))))
      e = Univalence.identity-equivalence l X₁
      body = Univalence.call l l E₁₁ E₁₂ J e
      dbody = rewritten Γ₁ l body body (instantiate (weaken E₁₂) e) (weaken E)
                (Lifting.identical body)
                (Relation.rel-compose _∙_ (instantiate-weakened E₁₂ e)
                  (Relation.rel-sym _⁻¹ rE))
                (application-term Γ₁ l l E₁₁ (weaken E₁₂) J e dE₁₁ dE₁₂′ dJ
                  (identity-equivalence-term Γ₁ l a₁ v₁ ca₁))
  in lambda-term Γ (suc l) l P (weaken E)
       (Univalence.call l l
         (Univalence.equivalence l l (weaken X) (weaken X))
         (Univalence.equivalence l l (weaken X) (weaken Y))
         (path-induction (suc l) l (universe l)
           (Univalence.arrow l l
             (Univalence.equivalence l l (weaken (weaken (weaken X)))
               (weaken (weaken (weaken X))))
             (Univalence.equivalence l l (weaken (weaken (weaken X)))
               (Tree.hole (fsuc fzero))))
           (weaken X)
           (Univalence.identity-function l
             (Univalence.equivalence l l (weaken X) (weaken X)))
           (weaken Y) (Tree.hole fzero))
         (Univalence.identity-equivalence l (weaken X)))
       dP
       (rewritten Γ₁ (suc l) E₁₂ (weaken E) (universe l) (universe l)
         (Relation.rel-sym _⁻¹ rE) (Lifting.identical (universe l)) dE₁₂)
       dbody

-- has-section (idtoeq X Y), for codes X and Y.
has-section-idtoeq-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (a b : Fin n)
  → Theory.Derivation (context Γ) → Assumed Γ a (suc l) (universe l)
  → Assumed Γ b (suc l) (universe l)
  → Theory.Derivation
      (type Γ (suc l ⊔ℕ l)
        (Univalence.has-section (suc l) l
          (identity (suc l) (universe l) (Tree.hole a) (Tree.hole b))
          (Univalence.equivalence l l (Tree.hole a) (Tree.hole b))
          (Univalence.idtoeq l (Tree.hole a) (Tree.hole b))))
has-section-idtoeq-type {n} Γ l a b v ca cb =
  let X : Raw.Expression Theory.Constant n
      X = Tree.hole a
      Y : Raw.Expression Theory.Constant n
      Y = Tree.hole b
      a₁ = fsuc a
      b₁ = fsuc b
      X₁ : Raw.Expression Theory.Constant (suc n)
      X₁ = Tree.hole a₁
      Y₁ : Raw.Expression Theory.Constant (suc n)
      Y₁ = Tree.hole b₁
      a₂ = fsuc a₁
      b₂ = fsuc b₁
      X₂ : Raw.Expression Theory.Constant (suc (suc n))
      X₂ = Tree.hole a₂
      Y₂ : Raw.Expression Theory.Constant (suc (suc n))
      Y₂ = Tree.hole b₂
      X₃ : Raw.Expression Theory.Constant (suc (suc (suc n)))
      X₃ = Tree.hole (fsuc a₂)
      Y₃ : Raw.Expression Theory.Constant (suc (suc (suc n)))
      Y₃ = Tree.hole (fsuc b₂)
      P = identity (suc l) (universe l) X Y
      E = Univalence.equivalence l l X Y
      f = Univalence.idtoeq l X Y
      P₁ = identity (suc l) (universe l) X₁ Y₁
      E₁ = Univalence.equivalence l l X₁ Y₁
      f₁ = Univalence.idtoeq l X₁ Y₁
      P₂ = identity (suc l) (universe l) X₂ Y₂
      E₂ = Univalence.equivalence l l X₂ Y₂
      P₃ = identity (suc l) (universe l) X₃ Y₃
      E₃ = Univalence.equivalence l l X₃ Y₃
      -- The parts weakened are the parts at the codes one further.
      rP = paths-weakened l X Y X₁ Y₁
             (Lifting.identical X₁) (Lifting.identical Y₁)
      rE = equivalence-weakened l l X Y X₁ Y₁
             (Lifting.identical X₁) (Lifting.identical Y₁)
      rf = idtoeq-weakened l X Y X₁ Y₁
             (Lifting.identical X₁) (Lifting.identical Y₁)
      -- Weakened twice, as section-homotopy writes them.
      Pw = weaken (weaken P)
      Ew = weaken (weaken E)
      fw = weaken (weaken f)
      rPw = Relation.rel-compose _∙_ (weaken-related (weaken P) P₁ rP)
              (paths-weakened l X₁ Y₁ X₂ Y₂
                (Lifting.identical X₂) (Lifting.identical Y₂))
      rEw = Relation.rel-compose _∙_ (weaken-related (weaken E) E₁ rE)
              (equivalence-weakened l l X₁ Y₁ X₂ Y₂
                (Lifting.identical X₂) (Lifting.identical Y₂))
      rfw = Relation.rel-compose _∙_ (weaken-related (weaken f) f₁ rf)
              (idtoeq-weakened l X₁ Y₁ X₂ Y₂
                (Lifting.identical X₂) (Lifting.identical Y₂))
      -- And once more.
      rPw₁ = Relation.rel-compose _∙_ (weaken-related Pw P₂ rPw)
               (paths-weakened l X₂ Y₂ X₃ Y₃
                 (Lifting.identical X₃) (Lifting.identical Y₃))
      rEw₁ = Relation.rel-compose _∙_ (weaken-related Ew E₂ rEw)
               (equivalence-weakened l l X₂ Y₂ X₃ Y₃
                 (Lifting.identical X₃) (Lifting.identical Y₃))
      dE = equivalence-type Γ l a b v ca cb
      ΓE = Γ ▸[ l ] E
      vE = extended-context Γ l E dE
      A = Univalence.arrow l (suc l) E P
      dA = pi-type Γ l (suc l) E (weaken P) dE
             (rewritten ΓE (suc (suc l)) P₁ (weaken P) (universe (suc l))
               (universe (suc l)) (Relation.rel-sym _⁻¹ rP)
               (Lifting.identical (universe (suc l)))
               (paths-type ΓE l a₁ b₁ vE (code-older Γ l E l a ca)
                 (code-older Γ l E l b cb)))
      Γ₁ = Γ ▸[ l ⊔ℕ suc l ] A
      v₁ = extended-context Γ (l ⊔ℕ suc l) A dA
      ca₁ = code-older Γ (l ⊔ℕ suc l) A l a ca
      cb₁ = code-older Γ (l ⊔ℕ suc l) A l b cb
      s₁ = newest-related Γ (l ⊔ℕ suc l) A (Univalence.arrow l (suc l) E₁ P₁)
             (arrow-weakened l (suc l) E P E₁ P₁ rE rP)
      dE₁ = rewritten Γ₁ (suc l) E₁ (weaken E) (universe l) (universe l)
              (Relation.rel-sym _⁻¹ rE) (Lifting.identical (universe l))
              (equivalence-type Γ₁ l a₁ b₁ v₁ ca₁ cb₁)
      Γ₂ = Γ₁ ▸[ l ] weaken E
      v₂ = extended-context Γ₁ l (weaken E) dE₁
      ca₂ = code-older Γ₁ l (weaken E) l a₁ ca₁
      cb₂ = code-older Γ₁ l (weaken E) l b₁ cb₁
      s₂ = older-related Γ₁ l (weaken E) fzero (l ⊔ℕ suc l)
             (Univalence.arrow l (suc l) E₁ P₁) (pi l (suc l) Ew (weaken Pw))
             s₁
             (arrow-weakened l (suc l) E₁ P₁ Ew Pw
               (weaken-related E₁ (weaken E) (Relation.rel-sym _⁻¹ rE))
               (weaken-related P₁ (weaken P) (Relation.rel-sym _⁻¹ rP)))
      dy = assumed Γ₂ fzero l Ew v₂
             (newest-related Γ₁ l (weaken E) Ew (Lifting.identical Ew))
      dEw = rewritten Γ₂ (suc l) E₂ Ew (universe l) (universe l)
              (Relation.rel-sym _⁻¹ rEw) (Lifting.identical (universe l))
              (equivalence-type Γ₂ l a₂ b₂ v₂ ca₂ cb₂)
      dPw = rewritten Γ₂ (suc (suc l)) P₂ Pw (universe (suc l))
              (universe (suc l)) (Relation.rel-sym _⁻¹ rPw)
              (Lifting.identical (universe (suc l)))
              (paths-type Γ₂ l a₂ b₂ v₂ ca₂ cb₂)
      ΓY = Γ₂ ▸[ l ] Ew
      vY = extended-context Γ₂ l Ew dEw
      dPw₁ = rewritten ΓY (suc (suc l)) P₃ (weaken Pw) (universe (suc l))
               (universe (suc l)) (Relation.rel-sym _⁻¹ rPw₁)
               (Lifting.identical (universe (suc l)))
               (paths-type ΓY l (fsuc a₂) (fsuc b₂) vY
                 (code-older Γ₂ l Ew l a₂ ca₂) (code-older Γ₂ l Ew l b₂ cb₂))
      ΓX = Γ₂ ▸[ suc l ] Pw
      vX = extended-context Γ₂ (suc l) Pw dPw
      dEw₁ = rewritten ΓX (suc l) E₃ (weaken Ew) (universe l) (universe l)
               (Relation.rel-sym _⁻¹ rEw₁)
               (Lifting.identical (universe l))
               (equivalence-type ΓX l (fsuc a₂) (fsuc b₂) vX
                 (code-older Γ₂ (suc l) Pw l a₂ ca₂)
                 (code-older Γ₂ (suc l) Pw l b₂ cb₂))
      -- s y, for s the section and y an element of X ≃ Y.
      inner = Univalence.call l (suc l) Ew Pw (Tree.hole (fsuc fzero))
                (Tree.hole fzero)
      d-inner = rewritten Γ₂ (suc l) inner inner
                  (instantiate (weaken Pw) (Tree.hole fzero)) Pw
                  (Lifting.identical inner)
                  (instantiate-weakened Pw (Tree.hole fzero))
                  (application-term Γ₂ l (suc l) Ew (weaken Pw)
                    (Tree.hole (fsuc fzero)) (Tree.hole fzero) dEw
                    dPw₁
                    (assumed Γ₂ (fsuc fzero) (l ⊔ℕ suc l)
                      (pi l (suc l) Ew (weaken Pw)) v₂ s₂)
                    dy)
      df = rewritten Γ₂ (suc l ⊔ℕ l) (Univalence.idtoeq l X₂ Y₂) fw
             (Univalence.arrow (suc l) l P₂ E₂) (pi (suc l) l Pw (weaken Ew))
             (Relation.rel-sym _⁻¹ rfw)
             (arrow-related (suc l) l P₂ E₂ Pw Ew
               (Relation.rel-sym _⁻¹ rPw) (Relation.rel-sym _⁻¹ rEw))
             (idtoeq-term Γ₂ l a₂ b₂ v₂ ca₂ cb₂)
      -- idtoeq (s y).
      outer = Univalence.call (suc l) l Pw Ew fw inner
      d-outer = rewritten Γ₂ l outer outer (instantiate (weaken Ew) inner) Ew
                  (Lifting.identical outer) (instantiate-weakened Ew inner)
                  (application-term Γ₂ (suc l) l Pw (weaken Ew) fw inner dPw
                    dEw₁ df d-inner)
      H = Univalence.section-homotopy (suc l) l P E f
  in type-leveled Γ ((l ⊔ℕ suc l) ⊔ℕ l) (suc l ⊔ℕ l)
       (Univalence.has-section (suc l) l P E f)
       (ap (λ k → k ⊔ℕ l) (joined l))
       (sigma-type Γ (l ⊔ℕ suc l) l A H dA
         (type-leveled Γ₁ (l ⊔ℕ l) l H (⊔ℕ-idempotent l)
           (pi-type Γ₁ l l (weaken E) (identity l Ew outer (Tree.hole fzero))
             dE₁
             (identity-type Γ₂ l Ew outer (Tree.hole fzero) dEw d-outer
               dy))))

-- is-section (idtoeq X Y), for codes X and Y.
is-section-idtoeq-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (a b : Fin n)
  → Theory.Derivation (context Γ) → Assumed Γ a (suc l) (universe l)
  → Assumed Γ b (suc l) (universe l)
  → Theory.Derivation
      (type Γ (suc l ⊔ℕ l)
        (Univalence.is-section (suc l) l
          (identity (suc l) (universe l) (Tree.hole a) (Tree.hole b))
          (Univalence.equivalence l l (Tree.hole a) (Tree.hole b))
          (Univalence.idtoeq l (Tree.hole a) (Tree.hole b))))
is-section-idtoeq-type {n} Γ l a b v ca cb =
  let X : Raw.Expression Theory.Constant n
      X = Tree.hole a
      Y : Raw.Expression Theory.Constant n
      Y = Tree.hole b
      a₁ = fsuc a
      b₁ = fsuc b
      X₁ : Raw.Expression Theory.Constant (suc n)
      X₁ = Tree.hole a₁
      Y₁ : Raw.Expression Theory.Constant (suc n)
      Y₁ = Tree.hole b₁
      a₂ = fsuc a₁
      b₂ = fsuc b₁
      X₂ : Raw.Expression Theory.Constant (suc (suc n))
      X₂ = Tree.hole a₂
      Y₂ : Raw.Expression Theory.Constant (suc (suc n))
      Y₂ = Tree.hole b₂
      X₃ : Raw.Expression Theory.Constant (suc (suc (suc n)))
      X₃ = Tree.hole (fsuc a₂)
      Y₃ : Raw.Expression Theory.Constant (suc (suc (suc n)))
      Y₃ = Tree.hole (fsuc b₂)
      P = identity (suc l) (universe l) X Y
      E = Univalence.equivalence l l X Y
      f = Univalence.idtoeq l X Y
      P₁ = identity (suc l) (universe l) X₁ Y₁
      E₁ = Univalence.equivalence l l X₁ Y₁
      f₁ = Univalence.idtoeq l X₁ Y₁
      P₂ = identity (suc l) (universe l) X₂ Y₂
      E₂ = Univalence.equivalence l l X₂ Y₂
      P₃ = identity (suc l) (universe l) X₃ Y₃
      E₃ = Univalence.equivalence l l X₃ Y₃
      -- The parts weakened are the parts at the codes one further.
      rP = paths-weakened l X Y X₁ Y₁
             (Lifting.identical X₁) (Lifting.identical Y₁)
      rE = equivalence-weakened l l X Y X₁ Y₁
             (Lifting.identical X₁) (Lifting.identical Y₁)
      rf = idtoeq-weakened l X Y X₁ Y₁
             (Lifting.identical X₁) (Lifting.identical Y₁)
      -- Weakened twice, as retraction-homotopy writes them.
      Pw = weaken (weaken P)
      Ew = weaken (weaken E)
      fw = weaken (weaken f)
      rPw = Relation.rel-compose _∙_ (weaken-related (weaken P) P₁ rP)
              (paths-weakened l X₁ Y₁ X₂ Y₂
                (Lifting.identical X₂) (Lifting.identical Y₂))
      rEw = Relation.rel-compose _∙_ (weaken-related (weaken E) E₁ rE)
              (equivalence-weakened l l X₁ Y₁ X₂ Y₂
                (Lifting.identical X₂) (Lifting.identical Y₂))
      rfw = Relation.rel-compose _∙_ (weaken-related (weaken f) f₁ rf)
              (idtoeq-weakened l X₁ Y₁ X₂ Y₂
                (Lifting.identical X₂) (Lifting.identical Y₂))
      -- And once more.
      rPw₁ = Relation.rel-compose _∙_ (weaken-related Pw P₂ rPw)
               (paths-weakened l X₂ Y₂ X₃ Y₃
                 (Lifting.identical X₃) (Lifting.identical Y₃))
      rEw₁ = Relation.rel-compose _∙_ (weaken-related Ew E₂ rEw)
               (equivalence-weakened l l X₂ Y₂ X₃ Y₃
                 (Lifting.identical X₃) (Lifting.identical Y₃))
      dE = equivalence-type Γ l a b v ca cb
      ΓE = Γ ▸[ l ] E
      vE = extended-context Γ l E dE
      A = Univalence.arrow l (suc l) E P
      dA = pi-type Γ l (suc l) E (weaken P) dE
             (rewritten ΓE (suc (suc l)) P₁ (weaken P) (universe (suc l))
               (universe (suc l)) (Relation.rel-sym _⁻¹ rP)
               (Lifting.identical (universe (suc l)))
               (paths-type ΓE l a₁ b₁ vE (code-older Γ l E l a ca)
                 (code-older Γ l E l b cb)))
      Γ₁ = Γ ▸[ l ⊔ℕ suc l ] A
      v₁ = extended-context Γ (l ⊔ℕ suc l) A dA
      ca₁ = code-older Γ (l ⊔ℕ suc l) A l a ca
      cb₁ = code-older Γ (l ⊔ℕ suc l) A l b cb
      r₁ = newest-related Γ (l ⊔ℕ suc l) A (Univalence.arrow l (suc l) E₁ P₁)
             (arrow-weakened l (suc l) E P E₁ P₁ rE rP)
      dP₁ = rewritten Γ₁ (suc (suc l)) P₁ (weaken P) (universe (suc l))
              (universe (suc l)) (Relation.rel-sym _⁻¹ rP)
              (Lifting.identical (universe (suc l)))
              (paths-type Γ₁ l a₁ b₁ v₁ ca₁ cb₁)
      Γ₂ = Γ₁ ▸[ suc l ] weaken P
      v₂ = extended-context Γ₁ (suc l) (weaken P) dP₁
      ca₂ = code-older Γ₁ (suc l) (weaken P) l a₁ ca₁
      cb₂ = code-older Γ₁ (suc l) (weaken P) l b₁ cb₁
      r₂ = older-related Γ₁ (suc l) (weaken P) fzero (l ⊔ℕ suc l)
             (Univalence.arrow l (suc l) E₁ P₁) (pi l (suc l) Ew (weaken Pw))
             r₁
             (arrow-weakened l (suc l) E₁ P₁ Ew Pw
               (weaken-related E₁ (weaken E) (Relation.rel-sym _⁻¹ rE))
               (weaken-related P₁ (weaken P) (Relation.rel-sym _⁻¹ rP)))
      dx = assumed Γ₂ fzero (suc l) Pw v₂
             (newest-related Γ₁ (suc l) (weaken P) Pw (Lifting.identical Pw))
      dEw = rewritten Γ₂ (suc l) E₂ Ew (universe l) (universe l)
              (Relation.rel-sym _⁻¹ rEw) (Lifting.identical (universe l))
              (equivalence-type Γ₂ l a₂ b₂ v₂ ca₂ cb₂)
      dPw = rewritten Γ₂ (suc (suc l)) P₂ Pw (universe (suc l))
              (universe (suc l)) (Relation.rel-sym _⁻¹ rPw)
              (Lifting.identical (universe (suc l)))
              (paths-type Γ₂ l a₂ b₂ v₂ ca₂ cb₂)
      ΓY = Γ₂ ▸[ l ] Ew
      vY = extended-context Γ₂ l Ew dEw
      dPw₁ = rewritten ΓY (suc (suc l)) P₃ (weaken Pw) (universe (suc l))
               (universe (suc l)) (Relation.rel-sym _⁻¹ rPw₁)
               (Lifting.identical (universe (suc l)))
               (paths-type ΓY l (fsuc a₂) (fsuc b₂) vY
                 (code-older Γ₂ l Ew l a₂ ca₂) (code-older Γ₂ l Ew l b₂ cb₂))
      ΓX = Γ₂ ▸[ suc l ] Pw
      vX = extended-context Γ₂ (suc l) Pw dPw
      dEw₁ = rewritten ΓX (suc l) E₃ (weaken Ew) (universe l) (universe l)
               (Relation.rel-sym _⁻¹ rEw₁)
               (Lifting.identical (universe l))
               (equivalence-type ΓX l (fsuc a₂) (fsuc b₂) vX
                 (code-older Γ₂ (suc l) Pw l a₂ ca₂)
                 (code-older Γ₂ (suc l) Pw l b₂ cb₂))
      df = rewritten Γ₂ (suc l ⊔ℕ l) (Univalence.idtoeq l X₂ Y₂) fw
             (Univalence.arrow (suc l) l P₂ E₂) (pi (suc l) l Pw (weaken Ew))
             (Relation.rel-sym _⁻¹ rfw)
             (arrow-related (suc l) l P₂ E₂ Pw Ew
               (Relation.rel-sym _⁻¹ rPw) (Relation.rel-sym _⁻¹ rEw))
             (idtoeq-term Γ₂ l a₂ b₂ v₂ ca₂ cb₂)
      -- idtoeq x, for x an element of X ＝ Y.
      inner = Univalence.call (suc l) l Pw Ew fw (Tree.hole fzero)
      d-inner = rewritten Γ₂ l inner inner
                  (instantiate (weaken Ew) (Tree.hole fzero)) Ew
                  (Lifting.identical inner)
                  (instantiate-weakened Ew (Tree.hole fzero))
                  (application-term Γ₂ (suc l) l Pw (weaken Ew) fw
                    (Tree.hole fzero) dPw dEw₁ df dx)
      -- r (idtoeq x), for r the retraction.
      outer = Univalence.call l (suc l) Ew Pw (Tree.hole (fsuc fzero))
                inner
      d-outer = rewritten Γ₂ (suc l) outer outer
                  (instantiate (weaken Pw) inner) Pw
                  (Lifting.identical outer) (instantiate-weakened Pw inner)
                  (application-term Γ₂ l (suc l) Ew (weaken Pw)
                    (Tree.hole (fsuc fzero)) inner dEw dPw₁
                    (assumed Γ₂ (fsuc fzero) (l ⊔ℕ suc l)
                      (pi l (suc l) Ew (weaken Pw)) v₂ r₂)
                    d-inner)
      H = Univalence.retraction-homotopy (suc l) l P E f
  in type-leveled Γ ((l ⊔ℕ suc l) ⊔ℕ suc l) (suc l ⊔ℕ l)
       (Univalence.is-section (suc l) l P E f)
       (ap (λ k → k ⊔ℕ suc l) (joined l) ∙
         (⊔ℕ-idempotent (suc l) ∙ joined′ l ⁻¹))
       (sigma-type Γ (l ⊔ℕ suc l) (suc l) A H dA
         (type-leveled Γ₁ (suc l ⊔ℕ suc l) (suc l) H (⊔ℕ-idempotent (suc l))
           (pi-type Γ₁ (suc l) (suc l) (weaken P)
             (identity (suc l) Pw outer (Tree.hole fzero)) dP₁
             (identity-type Γ₂ (suc l) Pw outer (Tree.hole fzero) dPw
               d-outer dx))))

-- is-equiv (idtoeq X Y), for codes X and Y: a type at level suc l.
is-equiv-idtoeq-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (a b : Fin n)
  → Theory.Derivation (context Γ) → Assumed Γ a (suc l) (universe l)
  → Assumed Γ b (suc l) (universe l)
  → Theory.Derivation
      (type Γ (suc l)
        (Univalence.is-equiv (suc l) l
          (identity (suc l) (universe l) (Tree.hole a) (Tree.hole b))
          (Univalence.equivalence l l (Tree.hole a) (Tree.hole b))
          (Univalence.idtoeq l (Tree.hole a) (Tree.hole b))))
is-equiv-idtoeq-type {n} Γ l a b v ca cb =
  let X : Raw.Expression Theory.Constant n
      X = Tree.hole a
      Y : Raw.Expression Theory.Constant n
      Y = Tree.hole b
      X₁ : Raw.Expression Theory.Constant (suc n)
      X₁ = Tree.hole (fsuc a)
      Y₁ : Raw.Expression Theory.Constant (suc n)
      Y₁ = Tree.hole (fsuc b)
      P = identity (suc l) (universe l) X Y
      E = Univalence.equivalence l l X Y
      f = Univalence.idtoeq l X Y
      S = Univalence.has-section (suc l) l P E f
      R = Univalence.is-section (suc l) l P E f
      R₁ = Univalence.is-section (suc l) l
             (identity (suc l) (universe l) X₁ Y₁)
             (Univalence.equivalence l l X₁ Y₁) (Univalence.idtoeq l X₁ Y₁)
      -- is-section weakened is is-section at the codes one further.
      rR = is-section-weakened (suc l) l P E f
             (identity (suc l) (universe l) X₁ Y₁)
             (Univalence.equivalence l l X₁ Y₁) (Univalence.idtoeq l X₁ Y₁)
             (paths-weakened l X Y X₁ Y₁
               (Lifting.identical X₁) (Lifting.identical Y₁))
             (equivalence-weakened l l X Y X₁ Y₁
               (Lifting.identical X₁) (Lifting.identical Y₁))
             (idtoeq-weakened l X Y X₁ Y₁
               (Lifting.identical X₁) (Lifting.identical Y₁))
      dS = has-section-idtoeq-type Γ l a b v ca cb
      Γ₁ = Γ ▸[ suc l ⊔ℕ l ] S
      v₁ = extended-context Γ (suc l ⊔ℕ l) S dS
      dR₁ = rewritten Γ₁ (suc (suc l ⊔ℕ l)) R₁ (weaken R)
              (universe (suc l ⊔ℕ l)) (universe (suc l ⊔ℕ l))
              (Relation.rel-sym _⁻¹ rR)
              (Lifting.identical (universe (suc l ⊔ℕ l)))
              (is-section-idtoeq-type Γ₁ l (fsuc a) (fsuc b) v₁
                (code-older Γ (suc l ⊔ℕ l) S l a ca)
                (code-older Γ (suc l ⊔ℕ l) S l b cb))
  in type-leveled Γ ((suc l ⊔ℕ l) ⊔ℕ (suc l ⊔ℕ l)) (suc l)
       (Univalence.is-equiv (suc l) l P E f)
       (⊔ℕ-idempotent (suc l ⊔ℕ l) ∙ joined′ l)
       (sigma-type Γ (suc l ⊔ℕ l) (suc l ⊔ℕ l) S (weaken R) dS dR₁)

-- is-univalent at l: (X Y : U) → is-equiv (idtoeq X Y). The statement of
-- the constant univalence l is a type at level suc l.
univalence-type :
  (l : ℕ) → Theory.Derivation (type ∅ (suc l) (Univalence.univalence l))
univalence-type l =
  let Γ₁ = ∅ ▸[ suc l ] universe l
      v₁ = extended-context ∅ (suc l) (universe l)
             (universe-type ∅ l empty-context)
      Γ₂ = Γ₁ ▸[ suc l ] universe l
      v₂ = extended-context Γ₁ (suc l) (universe l) (universe-type Γ₁ l v₁)
      E = Univalence.is-equiv (suc l) l
            (identity (suc l) (universe l) (Tree.hole (fsuc fzero))
              (Tree.hole fzero))
            (Univalence.equivalence l l (Tree.hole (fsuc fzero))
              (Tree.hole fzero))
            (Univalence.idtoeq l (Tree.hole (fsuc fzero))
              (Tree.hole fzero))
      dE = is-equiv-idtoeq-type Γ₂ l (fsuc fzero) fzero v₂
             (code-older Γ₁ (suc l) (universe l) l fzero
               (newest ∅ (suc l) (universe l) (universe l) refl))
             (newest Γ₁ (suc l) (universe l) (universe l) refl)
  in type-leveled ∅ (suc l ⊔ℕ suc l) (suc l) (Univalence.univalence l)
       (⊔ℕ-idempotent (suc l))
       (pi-type ∅ (suc l) (suc l) (universe l)
         (pi (suc l) (suc l) (universe l) E)
         (universe-type ∅ l empty-context)
         (type-leveled Γ₁ (suc l ⊔ℕ suc l) (suc l)
           (pi (suc l) (suc l) (universe l) E) (⊔ℕ-idempotent (suc l))
           (pi-type Γ₁ (suc l) (suc l) (universe l) E
             (universe-type Γ₁ l v₁) dE)))

-- The constant univalence l is a term of its statement in every valid
-- context: the constant rule, with `univalence-type` as its premise.
univalence-term :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ)
  → Theory.Derivation (context Γ)
  → Theory.Derivation
      (term Γ (suc l) (constant (Theory.univalence l))
        (closed n (Univalence.univalence l)))
univalence-term Γ l v =
  Tree.node (Theory.constants , Constants.axiom Γ (Theory.univalence l))
    (λ { fzero → v ; (fsuc fzero) → univalence-type l
       ; (fsuc (fsuc ())) })
