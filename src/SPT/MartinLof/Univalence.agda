{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Univalence where

-- Univalence of the universe at level l, as a closed type of the core
-- theory at level suc l (`univalence`). It is TypeTopology's statement
-- (SPT/Cubical/TypeTopology, UF.Univalence):
--
--   is-univalent 𝓤 = (X Y : 𝓤 ̇) → is-equiv (idtoeq X Y).
--
-- The parts follow UF.Retracts and UF.Equiv:
-- - the functions from X to Y and their application (`arrow`, `call`);
-- - has-section f = Σ s ꞉ (Y → X), f ∘ s ∼ id (`has-section`, with
--   `section-homotopy`), and is-section f = Σ r ꞉ (Y → X), r ∘ f ∼ id
--   (`is-section`, with `retraction-homotopy`);
-- - is-equiv f = has-section f × is-section f (`is-equiv`), and
--   X ≃ Y = Σ f ꞉ (X → Y), is-equiv f (`equivalence`);
-- - id, id-is-equiv X = (id , λ x → refl) , (id , λ x → refl), and
--   ≃-refl X = id , id-is-equiv X (`identity-function`, `refl-homotopy`,
--   `id-is-equiv`, `identity-equivalence`);
-- - idtoeq X Y p = transport (X ≃_) p (≃-refl X), where transport along p
--   is J at the identity function, as TypeTopology's `transport A refl =
--   id` (`idtoeq`).
-- Composites and homotopies are written applied: f ∘ s ∼ id is
-- Π y. f (s y) ＝ y.
--
-- Levels are written by value. A type built from types at levels m and k
-- is annotated m ⊔ k; a few places write m where the formation rules give
-- m ⊔ m. At every numeral the two agree, since Data.Nat's ⊔ computes on
-- numerals. A pair or λ carries the annotations of its Σ- or Π-type.

open import SPT.Base
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Tree as Tree
open import SPT.MartinLof.Formers using
  (universe; pi; lambda; application; sigma; pair; identity; reflexivity
  ; path-induction; weaken)
import SPT.MartinLof.Raw as Raw

------------------------------------------------------------------------
-- Functions

-- The functions from X at level m to Y at level k.
arrow :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n → Raw.Expression C n
  → Raw.Expression C n
arrow m k X Y = pi m k X (weaken Y)

-- f x, for f from X at level m to Y at level k.
call :
  {C : Set} {n : ℕ} (m k : ℕ) (X Y f x : Raw.Expression C n)
  → Raw.Expression C n
call m k X Y f x = application m k X (weaken Y) f x

-- id, the identity function of X at level m.
identity-function :
  {C : Set} {n : ℕ} (m : ℕ) → Raw.Expression C n → Raw.Expression C n
identity-function m X = lambda m m X (weaken X) (Tree.hole fzero)

------------------------------------------------------------------------
-- Sections, retractions and equivalences, for f from X at level m to Y
-- at level k

-- f ∘ s ∼ id, that is Π y. f (s y) ＝ y, for s the last variable.
section-homotopy :
  {C : Set} {n : ℕ} (m k : ℕ) (X Y f : Raw.Expression C n)
  → Raw.Expression C (suc n)
section-homotopy m k X Y f =
  pi k k (weaken Y)
    (identity k (weaken (weaken Y))
      (call m k (weaken (weaken X)) (weaken (weaken Y)) (weaken (weaken f))
        (call k m (weaken (weaken Y)) (weaken (weaken X))
          (Tree.hole (fsuc fzero)) (Tree.hole fzero)))
      (Tree.hole fzero))

-- has-section f = Σ s ꞉ (Y → X), f ∘ s ∼ id.
has-section :
  {C : Set} {n : ℕ} (m k : ℕ) (X Y f : Raw.Expression C n)
  → Raw.Expression C n
has-section m k X Y f =
  sigma (k ⊔ℕ m) k (arrow k m Y X) (section-homotopy m k X Y f)

-- r ∘ f ∼ id, that is Π x. r (f x) ＝ x, for r the last variable.
retraction-homotopy :
  {C : Set} {n : ℕ} (m k : ℕ) (X Y f : Raw.Expression C n)
  → Raw.Expression C (suc n)
retraction-homotopy m k X Y f =
  pi m m (weaken X)
    (identity m (weaken (weaken X))
      (call k m (weaken (weaken Y)) (weaken (weaken X))
        (Tree.hole (fsuc fzero))
        (call m k (weaken (weaken X)) (weaken (weaken Y)) (weaken (weaken f))
          (Tree.hole fzero)))
      (Tree.hole fzero))

-- is-section f = Σ r ꞉ (Y → X), r ∘ f ∼ id.
is-section :
  {C : Set} {n : ℕ} (m k : ℕ) (X Y f : Raw.Expression C n)
  → Raw.Expression C n
is-section m k X Y f =
  sigma (k ⊔ℕ m) m (arrow k m Y X) (retraction-homotopy m k X Y f)

-- is-equiv f = has-section f × is-section f.
is-equiv :
  {C : Set} {n : ℕ} (m k : ℕ) (X Y f : Raw.Expression C n)
  → Raw.Expression C n
is-equiv m k X Y f =
  sigma (m ⊔ℕ k) (m ⊔ℕ k) (has-section m k X Y f)
    (weaken (is-section m k X Y f))

-- X ≃ Y = Σ f ꞉ (X → Y), is-equiv f.
equivalence :
  {C : Set} {n : ℕ} (m k : ℕ) → Raw.Expression C n → Raw.Expression C n
  → Raw.Expression C n
equivalence m k X Y =
  sigma (m ⊔ℕ k) (m ⊔ℕ k) (arrow m k X Y)
    (is-equiv m k (weaken X) (weaken Y) (Tree.hole fzero))

------------------------------------------------------------------------
-- The identity equivalence of X at level m

-- λ x → refl, of type Π x. id (id x) ＝ x.
refl-homotopy :
  {C : Set} {n : ℕ} (m : ℕ) → Raw.Expression C n → Raw.Expression C n
refl-homotopy m X =
  lambda m m X
    (identity m (weaken X)
      (call m m (weaken X) (weaken X) (weaken (identity-function m X))
        (call m m (weaken X) (weaken X) (weaken (identity-function m X))
          (Tree.hole fzero)))
      (Tree.hole fzero))
    (reflexivity m (weaken X) (Tree.hole fzero))

-- id-is-equiv X = (id , λ x → refl) , (id , λ x → refl).
id-is-equiv :
  {C : Set} {n : ℕ} (m : ℕ) → Raw.Expression C n → Raw.Expression C n
id-is-equiv m X =
  pair (m ⊔ℕ m) (m ⊔ℕ m) (has-section m m X X (identity-function m X))
    (weaken (is-section m m X X (identity-function m X)))
    (pair (m ⊔ℕ m) m (arrow m m X X)
      (section-homotopy m m X X (identity-function m X))
      (identity-function m X) (refl-homotopy m X))
    (pair (m ⊔ℕ m) m (arrow m m X X)
      (retraction-homotopy m m X X (identity-function m X))
      (identity-function m X) (refl-homotopy m X))

-- ≃-refl X = id , id-is-equiv X.
identity-equivalence :
  {C : Set} {n : ℕ} (m : ℕ) → Raw.Expression C n → Raw.Expression C n
identity-equivalence m X =
  pair (m ⊔ℕ m) (m ⊔ℕ m) (arrow m m X X)
    (is-equiv m m (weaken X) (weaken X) (Tree.hole fzero))
    (identity-function m X) (id-is-equiv m X)

------------------------------------------------------------------------
-- Univalence

-- idtoeq X Y = λ p. transport (X ≃_) p (≃-refl X), for X and Y in the
-- universe at l. Transport along p is J into the motive
-- (y , q) ↦ ((X ≃ X) → (X ≃ y)) at the identity function.
idtoeq :
  {C : Set} {n : ℕ} (l : ℕ) → Raw.Expression C n → Raw.Expression C n
  → Raw.Expression C n
idtoeq l X Y =
  lambda (suc l) l (identity (suc l) (universe l) X Y)
    (weaken (equivalence l l X Y))
    (call l l (equivalence l l (weaken X) (weaken X))
      (equivalence l l (weaken X) (weaken Y))
      (path-induction (suc l) l (universe l)
        (arrow l l
          (equivalence l l (weaken (weaken (weaken X)))
            (weaken (weaken (weaken X))))
          (equivalence l l (weaken (weaken (weaken X)))
            (Tree.hole (fsuc fzero))))
        (weaken X)
        (identity-function l (equivalence l l (weaken X) (weaken X)))
        (weaken Y) (Tree.hole fzero))
      (identity-equivalence l (weaken X)))

-- is-univalent at l: (X Y : U) → is-equiv (idtoeq X Y).
univalence : {C : Set} (l : ℕ) → Raw.Expression C 0
univalence l =
  pi (suc l) (suc l) (universe l)
    (pi (suc l) (suc l) (universe l)
      (is-equiv (suc l) l
        (identity (suc l) (universe l)
          (Tree.hole (fsuc fzero)) (Tree.hole fzero))
        (equivalence l l (Tree.hole (fsuc fzero)) (Tree.hole fzero))
        (idtoeq l (Tree.hole (fsuc fzero)) (Tree.hole fzero))))
