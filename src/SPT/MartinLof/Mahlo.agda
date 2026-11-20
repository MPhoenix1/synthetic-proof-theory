{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Mahlo where

-- The ambient Mahlo rule at level l, `Mahlo (Ambient.formers ℓ)` of
-- SPT.Mahlo.Specification and SPT.Mahlo.Ambient, as a closed type of the
-- core theory at level suc l (`mahlo`). The ambient parent has as codes
-- the types at level l, each decoding to itself: a code is a term of the
-- universe U at l. Records become iterated Σ-types in the order of their
-- fields, `_＝_` the identity type, and 𝟚 is 1 + 1. Agda's definitional
-- unfolding is written out: map D interpret F is the pair of
-- interpret (pr₁ F) and λ x → interpret (pr₂ F x), and the product, sum
-- and tree of it are Π, Σ and W of these.
--
-- - Family D = Σ a ꞉ U , (a → U) and Operator D = Family D → Family D
--   (`family`, `operator`).
-- - For interpret : A → U, interpret a (`decode`), Name interpret c =
--   Σ a ꞉ A , (interpret a ＝ c) (`name`), Family (Decode D interpret) =
--   Σ a ꞉ A , (interpret a → A) (`decoded-family`), and map D interpret
--   (`map`, from `index` and `branch`).
-- - The fields of Closure Q Ψ A (`closure`): interpret : A → U; names of
--   Lift 𝟘, Lift 𝟙, Lift (1 + 1) and Lift ℕ; names of the products, sums
--   and trees of the families of A (`names-products`, `names-sums`,
--   `names-trees`) and of its identity types (`names-identities`); inner
--   (`inner-map`) and inner-β (`inner-law`).
-- - Reflection Q Ψ = Σ carrier ꞉ U , Closure Q Ψ carrier (`reflection`),
--   and Mahlo Q = (Ψ : Operator D) → Reflection Q Ψ (`mahlo`).
--
-- Levels are written by value, as in Univalence: a type built from types
-- at level l is annotated l, one built from U at l suc l. At every numeral
-- these are the levels the formation rules give.

open import SPT.Base
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Tree as Tree
open import SPT.MartinLof.Formers using
  (universe; lifted; pi; lambda; application; sigma; pair; first; second
  ; identity; tree; empty; unit; sum; natural; weaken)
import SPT.MartinLof.Raw as Raw

------------------------------------------------------------------------
-- Families and operators of the universe at l

-- a → U, for a the last variable.
family-branches : {C : Set} {n : ℕ} (l : ℕ) → Raw.Expression C (suc n)
family-branches l = pi l (suc l) (Tree.hole fzero) (universe l)

-- Family D = Σ a ꞉ U , (a → U).
family : {C : Set} {n : ℕ} (l : ℕ) → Raw.Expression C n
family l = sigma (suc l) (suc l) (universe l) (family-branches l)

-- Operator D = Family D → Family D.
operator : {C : Set} {n : ℕ} (l : ℕ) → Raw.Expression C n
operator l = pi (suc l) (suc l) (family l) (family l)

------------------------------------------------------------------------
-- An interpretation I : A → U of a code A

-- interpret a.
decode :
  {C : Set} {n : ℕ} (l : ℕ) (A I a : Raw.Expression C n)
  → Raw.Expression C n
decode l A I a = application l (suc l) A (universe l) I a

-- Name interpret c = Σ a ꞉ A , (interpret a ＝ c).
name :
  {C : Set} {n : ℕ} (l : ℕ) (A I c : Raw.Expression C n)
  → Raw.Expression C n
name l A I c =
  sigma l (suc l) A
    (identity (suc l) (universe l)
      (decode l (weaken A) (weaken I) (Tree.hole fzero)) (weaken c))

-- interpret a → A, for a the last variable.
decoded-branches :
  {C : Set} {n : ℕ} (l : ℕ) (A I : Raw.Expression C n)
  → Raw.Expression C (suc n)
decoded-branches l A I =
  pi l l (decode l (weaken A) (weaken I) (Tree.hole fzero))
    (weaken (weaken A))

-- Family (Decode D interpret) = Σ a ꞉ A , (interpret a → A).
decoded-family :
  {C : Set} {n : ℕ} (l : ℕ) (A I : Raw.Expression C n)
  → Raw.Expression C n
decoded-family l A I = sigma l l A (decoded-branches l A I)

-- interpret (pr₁ F), for F a family of Decode D interpret.
index :
  {C : Set} {n : ℕ} (l : ℕ) (A I F : Raw.Expression C n)
  → Raw.Expression C n
index l A I F = decode l A I (first l l A (decoded-branches l A I) F)

-- interpret (pr₂ F x), for x the last variable.
branch :
  {C : Set} {n : ℕ} (l : ℕ) (A I F : Raw.Expression C n)
  → Raw.Expression C (suc n)
branch l A I F =
  decode l (weaken A) (weaken I)
    (application l l (weaken (index l A I F)) (weaken (weaken A))
      (weaken (second l l A (decoded-branches l A I) F))
      (Tree.hole fzero))

-- map D interpret F = interpret (pr₁ F) , λ x → interpret (pr₂ F x).
map :
  {C : Set} {n : ℕ} (l : ℕ) (A I F : Raw.Expression C n)
  → Raw.Expression C n
map l A I F =
  pair (suc l) (suc l) (universe l) (family-branches l) (index l A I F)
    (lambda l (suc l) (index l A I F) (universe l) (branch l A I F))

------------------------------------------------------------------------
-- The fields of a closure, for I : A → U

-- (F : Family (Decode D interpret))
-- → Name interpret ((x : interpret (pr₁ F)) → interpret (pr₂ F x)).
names-products :
  {C : Set} {n : ℕ} (l : ℕ) (A I : Raw.Expression C n)
  → Raw.Expression C n
names-products l A I =
  pi l (suc l) (decoded-family l A I)
    (name l (weaken A) (weaken I)
      (pi l l (index l (weaken A) (weaken I) (Tree.hole fzero))
        (branch l (weaken A) (weaken I) (Tree.hole fzero))))

-- (F : Family (Decode D interpret))
-- → Name interpret (Σ (interpret (pr₁ F)) (λ x → interpret (pr₂ F x))).
names-sums :
  {C : Set} {n : ℕ} (l : ℕ) (A I : Raw.Expression C n)
  → Raw.Expression C n
names-sums l A I =
  pi l (suc l) (decoded-family l A I)
    (name l (weaken A) (weaken I)
      (sigma l l (index l (weaken A) (weaken I) (Tree.hole fzero))
        (branch l (weaken A) (weaken I) (Tree.hole fzero))))

-- (F : Family (Decode D interpret))
-- → Name interpret (W (interpret (pr₁ F)) (λ x → interpret (pr₂ F x))).
names-trees :
  {C : Set} {n : ℕ} (l : ℕ) (A I : Raw.Expression C n)
  → Raw.Expression C n
names-trees l A I =
  pi l (suc l) (decoded-family l A I)
    (name l (weaken A) (weaken I)
      (tree l l (index l (weaken A) (weaken I) (Tree.hole fzero))
        (branch l (weaken A) (weaken I) (Tree.hole fzero))))

-- (a : A) (x y : interpret a) → Name interpret (x ＝ y).
names-identities :
  {C : Set} {n : ℕ} (l : ℕ) (A I : Raw.Expression C n)
  → Raw.Expression C n
names-identities l A I =
  pi l (suc l) A
    (pi l (suc l) (decode l (weaken A) (weaken I) (Tree.hole fzero))
      (pi l (suc l)
        (decode l (weaken (weaken A)) (weaken (weaken I))
          (Tree.hole (fsuc fzero)))
        (name l (weaken (weaken (weaken A))) (weaken (weaken (weaken I)))
          (identity l
            (decode l (weaken (weaken (weaken A)))
              (weaken (weaken (weaken I)))
              (Tree.hole (fsuc (fsuc fzero))))
            (Tree.hole (fsuc fzero)) (Tree.hole fzero)))))

-- inner : Family (Decode D interpret) → Family (Decode D interpret).
inner-map :
  {C : Set} {n : ℕ} (l : ℕ) (A I : Raw.Expression C n)
  → Raw.Expression C n
inner-map l A I =
  pi l l (decoded-family l A I) (decoded-family l (weaken A) (weaken I))

-- inner-β : (F : Family (Decode D interpret))
-- → map D interpret (inner F) ＝ Ψ (map D interpret F), for inner J.
inner-law :
  {C : Set} {n : ℕ} (l : ℕ) (Ψ A I J : Raw.Expression C n)
  → Raw.Expression C n
inner-law l Ψ A I J =
  pi l (suc l) (decoded-family l A I)
    (identity (suc l) (family l)
      (map l (weaken A) (weaken I)
        (application l l (decoded-family l (weaken A) (weaken I))
          (decoded-family l (weaken (weaken A)) (weaken (weaken I)))
          (weaken J) (Tree.hole fzero)))
      (application (suc l) (suc l) (family l) (family l) (weaken Ψ)
        (map l (weaken A) (weaken I) (Tree.hole fzero))))

------------------------------------------------------------------------
-- Closures, reflections and the Mahlo rule

-- Closure Q Ψ A, for A the last variable and Ψ the one before: the
-- iterated Σ of its fields. After the j-th field, interpret is the
-- variable j - 1 and A the variable j.
closure : {C : Set} (l : ℕ) → Raw.Expression C 2
closure l =
  sigma (suc l) (suc l) (pi l (suc l) (Tree.hole (# 0)) (universe l))
  (sigma (suc l) (suc l)
    (name l (Tree.hole (# 1)) (Tree.hole (# 0)) (lifted 0 l empty))
  (sigma (suc l) (suc l)
    (name l (Tree.hole (# 2)) (Tree.hole (# 1)) (lifted 0 l unit))
  (sigma (suc l) (suc l)
    (name l (Tree.hole (# 3)) (Tree.hole (# 2))
      (lifted 0 l (sum 0 0 unit unit)))
  (sigma (suc l) (suc l)
    (name l (Tree.hole (# 4)) (Tree.hole (# 3)) (lifted 0 l natural))
  (sigma (suc l) (suc l)
    (names-products l (Tree.hole (# 5)) (Tree.hole (# 4)))
  (sigma (suc l) (suc l)
    (names-sums l (Tree.hole (# 6)) (Tree.hole (# 5)))
  (sigma (suc l) (suc l)
    (names-trees l (Tree.hole (# 7)) (Tree.hole (# 6)))
  (sigma (suc l) (suc l)
    (names-identities l (Tree.hole (# 8)) (Tree.hole (# 7)))
  (sigma l (suc l)
    (inner-map l (Tree.hole (# 9)) (Tree.hole (# 8)))
    (inner-law l (Tree.hole (# 11)) (Tree.hole (# 10)) (Tree.hole (# 9))
      (Tree.hole (# 0))))))))))))

-- Reflection Q Ψ = Σ carrier ꞉ U , Closure Q Ψ carrier, for Ψ the last
-- variable.
reflection : {C : Set} (l : ℕ) → Raw.Expression C 1
reflection l = sigma (suc l) (suc l) (universe l) (closure l)

-- Mahlo Q = (Ψ : Operator D) → Reflection Q Ψ.
mahlo : {C : Set} (l : ℕ) → Raw.Expression C 0
mahlo l = pi (suc l) (suc l) (operator l) (reflection l)
