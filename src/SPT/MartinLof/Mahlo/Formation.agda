{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Mahlo.Formation where

-- The statement of the ambient Mahlo rule (Mahlo) is a type at level suc l
-- in the empty context (`mahlo-type`), so the constant rule applies to the
-- constants mahlo l.
--
-- The parts are typed in every valid context, with the code A, the
-- interpretation I : A → U and the operator Ψ given as variables at
-- positions p, i and ψ (`Interpreted`, `past`):
-- - the families and operators of U (`family-type`, `operator-type`);
-- - interpret a, names, the families of the decoding and their parts,
--   and map D interpret (`decode-term`, `name-type`,
--   `decoded-family-type`, `index-term`, `branch-term`, `map-term`);
-- - the fields of a closure (`names-former-type` for products, sums and
--   trees, `names-identities-type`, `inner-map-type`, `inner-law-type`);
-- - the closure, the reflection and the rule (`closure-type`,
--   `reflection-type`, `mahlo-type`);
-- - the constant mahlo l as a term of its statement in every valid
--   context, by the constant rule (`mahlo-term`).
-- Every step that meets a weakened or substituted expression replaces it
-- by its literal form with the same skeleton (Derived's `reshaped`, by
-- `refl`). Where a family F is abstract, the substitution of an
-- expression containing it does not compute, and the lemma takes that
-- skeleton equation as an argument; its uses pass `refl`. Levels written
-- by value meet the formation rules' levels through ⊔ (`joined`).

open import SPT.Base
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Tree as Tree
open import SPT.MartinLof.Derived using
  (empty-context; extended-context; reshaped; leveled; type-leveled; Assumed
  ; newest; older; assumed; universe-type; lifted-type; pi-type; sigma-type
  ; tree-type; identity-type; empty-type; unit-type; natural-type; sum-type
  ; lambda-term; application-term; pair-term; first-term; second-term)
open import SPT.MartinLof.Formers using
  (universe; lifted; pi; lambda; sigma; tree; identity; empty; unit; sum
  ; natural; application; first; second; weaken; instantiate; constant; closed)
open import SPT.MartinLof.Judgment using
  (Context; ∅; _▸[_]_; context; term; type)
import SPT.MartinLof.Mahlo as Mahlo
import SPT.MartinLof.Raw as Raw
import SPT.MartinLof.Rules.Constant as Constants
open import SPT.MartinLof.Skeleton using (skeleton)
import SPT.MartinLof.Theory as Theory

------------------------------------------------------------------------
-- Levels

-- A type at level l built with U at l lives at suc l.
joined : (l : ℕ) → l ⊔ℕ suc l ＝ suc l
joined l = ≤ℕˢ-gives-⊔ℕ-right (≤ℕˢ-to-suc l)

------------------------------------------------------------------------
-- Families and operators of U at l

-- a → U, for a the last variable, a code.
family-branches-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ)
  → Theory.Derivation (context Γ)
  → Theory.Derivation
      (type (Γ ▸[ suc l ] universe l) (suc l) (Mahlo.family-branches l))
family-branches-type Γ l v =
  let Γ₁ = Γ ▸[ suc l ] universe l
      v₁ = extended-context Γ (suc l) (universe l) (universe-type Γ l v)
      da = assumed Γ₁ fzero (suc l) (universe l) v₁
             (newest Γ (suc l) (universe l) (universe l) refl)
      v₂ = extended-context Γ₁ l (Tree.hole fzero) da
  in type-leveled Γ₁ (l ⊔ℕ suc l) (suc l) (Mahlo.family-branches l)
       (joined l)
       (pi-type Γ₁ l (suc l) (Tree.hole fzero) (universe l) da
         (universe-type (Γ₁ ▸[ l ] Tree.hole fzero) l v₂))

-- Family D = Σ a ꞉ U , (a → U).
family-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ)
  → Theory.Derivation (context Γ)
  → Theory.Derivation (type Γ (suc l) (Mahlo.family l))
family-type Γ l v =
  type-leveled Γ (suc l ⊔ℕ suc l) (suc l) (Mahlo.family l)
    (⊔ℕ-idempotent (suc l))
    (sigma-type Γ (suc l) (suc l) (universe l) (Mahlo.family-branches l)
      (universe-type Γ l v) (family-branches-type Γ l v))

-- Operator D = Family D → Family D.
operator-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ)
  → Theory.Derivation (context Γ)
  → Theory.Derivation (type Γ (suc l) (Mahlo.operator l))
operator-type Γ l v =
  let dF = family-type Γ l v
      v₁ = extended-context Γ (suc l) (Mahlo.family l) dF
  in type-leveled Γ (suc l ⊔ℕ suc l) (suc l) (Mahlo.operator l)
       (⊔ℕ-idempotent (suc l))
       (pi-type Γ (suc l) (suc l) (Mahlo.family l) (Mahlo.family l) dF
         (family-type (Γ ▸[ suc l ] Mahlo.family l) l v₁))

------------------------------------------------------------------------
-- A code with an interpretation

-- In the valid context Γ, the variable p is a code of U at l and the
-- variable i an interpretation of it, of type p → U.
record Interpreted
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (p i : Fin n) : Set where
  field
    valid : Theory.Derivation (context Γ)
    code : Assumed Γ p (suc l) (universe l)
    interpretation :
      Assumed Γ i (suc l) (pi l (suc l) (Tree.hole p) (universe l))

-- The same, past a further variable.
past :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (p i : Fin n) (k : ℕ)
  (B : Raw.Expression Theory.Constant n)
  → Interpreted Γ l p i → Theory.Derivation (type Γ k B)
  → Interpreted (Γ ▸[ k ] B) l (fsuc p) (fsuc i)
past Γ l p i k B h dB = record
  { valid = extended-context Γ k B dB
  ; code =
      older Γ k B p (suc l) (universe l) (universe l) (Interpreted.code h)
        refl
  ; interpretation =
      older Γ k B i (suc l) (pi l (suc l) (Tree.hole p) (universe l))
        (pi l (suc l) (Tree.hole (fsuc p)) (universe l))
        (Interpreted.interpretation h) refl
  }

-- The code as a type at level l.
code-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (p i : Fin n)
  → Interpreted Γ l p i → Theory.Derivation (type Γ l (Tree.hole p))
code-type Γ l p i h =
  assumed Γ p (suc l) (universe l) (Interpreted.valid h)
    (Interpreted.code h)

-- The newest variable, an element of the code.
element :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (p i : Fin n)
  → (h : Interpreted Γ l p i)
  → Theory.Derivation
      (term (Γ ▸[ l ] Tree.hole p) l (Tree.hole fzero)
        (Tree.hole (fsuc p)))
element Γ l p i h =
  assumed (Γ ▸[ l ] Tree.hole p) fzero l (Tree.hole (fsuc p))
    (extended-context Γ l (Tree.hole p) (code-type Γ l p i h))
    (newest Γ l (Tree.hole p) (Tree.hole (fsuc p)) refl)

-- interpret a, a type at level l, for a an element of the code.
decode-term :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (p i : Fin n)
  (a : Raw.Expression Theory.Constant n)
  → Interpreted Γ l p i → Theory.Derivation (term Γ l a (Tree.hole p))
  → Theory.Derivation
      (type Γ l (Mahlo.decode l (Tree.hole p) (Tree.hole i) a))
decode-term Γ l p i a h da =
  let v = Interpreted.valid h
      dA = code-type Γ l p i h
      v₁ = extended-context Γ l (Tree.hole p) dA
      dI = leveled Γ (suc l) (l ⊔ℕ suc l) (Tree.hole i)
             (pi l (suc l) (Tree.hole p) (universe l)) (joined l ⁻¹)
             (assumed Γ i (suc l) (pi l (suc l) (Tree.hole p) (universe l))
               v (Interpreted.interpretation h))
  in reshaped Γ (suc l)
       (application l (suc l) (Tree.hole p) (universe l) (Tree.hole i) a)
       (Mahlo.decode l (Tree.hole p) (Tree.hole i) a)
       (instantiate (universe l) a) (universe l) refl refl
       (application-term Γ l (suc l) (Tree.hole p) (universe l)
         (Tree.hole i) a dA
         (universe-type (Γ ▸[ l ] Tree.hole p) l v₁) dI da)

-- Name interpret c = Σ a ꞉ A , (interpret a ＝ c), for c in U, given in
-- the scope of a.
name-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (p i : Fin n)
  (c : Raw.Expression Theory.Constant n)
  → Interpreted Γ l p i
  → Theory.Derivation
      (term (Γ ▸[ l ] Tree.hole p) (suc l) (weaken c) (universe l))
  → Theory.Derivation
      (type Γ (suc l) (Mahlo.name l (Tree.hole p) (Tree.hole i) c))
name-type Γ l p i c h dc =
  let Γ₁ = Γ ▸[ l ] Tree.hole p
      dA = code-type Γ l p i h
      h₁ = past Γ l p i l (Tree.hole p) h dA
      dD = decode-term Γ₁ l (fsuc p) (fsuc i) (Tree.hole fzero) h₁
             (element Γ l p i h)
  in type-leveled Γ (l ⊔ℕ suc l) (suc l)
       (Mahlo.name l (Tree.hole p) (Tree.hole i) c) (joined l)
       (sigma-type Γ l (suc l) (Tree.hole p)
         (identity (suc l) (universe l)
           (Mahlo.decode l (Tree.hole (fsuc p)) (Tree.hole (fsuc i))
             (Tree.hole fzero))
           (weaken c))
         dA
         (identity-type Γ₁ (suc l) (universe l)
           (Mahlo.decode l (Tree.hole (fsuc p)) (Tree.hole (fsuc i))
             (Tree.hole fzero))
           (weaken c) (universe-type Γ₁ l (Interpreted.valid h₁)) dD dc))

------------------------------------------------------------------------
-- The families of the decoding

-- interpret a → A, for a the last variable.
decoded-branches-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (p i : Fin n)
  → Interpreted Γ l p i
  → Theory.Derivation
      (type (Γ ▸[ l ] Tree.hole p) l
        (Mahlo.decoded-branches l (Tree.hole p) (Tree.hole i)))
decoded-branches-type Γ l p i h =
  let Γ₁ = Γ ▸[ l ] Tree.hole p
      dA = code-type Γ l p i h
      h₁ = past Γ l p i l (Tree.hole p) h dA
      dD = decode-term Γ₁ l (fsuc p) (fsuc i) (Tree.hole fzero) h₁
             (element Γ l p i h)
      D = Mahlo.decode l (Tree.hole (fsuc p)) (Tree.hole (fsuc i))
            (Tree.hole fzero)
      h₂ = past Γ₁ l (fsuc p) (fsuc i) l D h₁ dD
  in type-leveled Γ₁ (l ⊔ℕ l) l
       (Mahlo.decoded-branches l (Tree.hole p) (Tree.hole i)) (⊔ℕ-idempotent l)
       (pi-type Γ₁ l l D (Tree.hole (fsuc (fsuc p))) dD
         (code-type (Γ₁ ▸[ l ] D) l (fsuc (fsuc p))
           (fsuc (fsuc i)) h₂))

-- Family (Decode D interpret) = Σ a ꞉ A , (interpret a → A).
decoded-family-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (p i : Fin n)
  → Interpreted Γ l p i
  → Theory.Derivation
      (type Γ l (Mahlo.decoded-family l (Tree.hole p) (Tree.hole i)))
decoded-family-type Γ l p i h =
  type-leveled Γ (l ⊔ℕ l) l
    (Mahlo.decoded-family l (Tree.hole p) (Tree.hole i)) (⊔ℕ-idempotent l)
    (sigma-type Γ l l (Tree.hole p)
      (Mahlo.decoded-branches l (Tree.hole p) (Tree.hole i))
      (code-type Γ l p i h) (decoded-branches-type Γ l p i h))

-- interpret (pr₁ F).
index-term :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (p i : Fin n)
  (F : Raw.Expression Theory.Constant n)
  → Interpreted Γ l p i
  → Theory.Derivation
      (term Γ l F (Mahlo.decoded-family l (Tree.hole p) (Tree.hole i)))
  → Theory.Derivation
      (type Γ l (Mahlo.index l (Tree.hole p) (Tree.hole i) F))
index-term Γ l p i F h dF =
  let B = Mahlo.decoded-branches l (Tree.hole p) (Tree.hole i)
  in decode-term Γ l p i (first l l (Tree.hole p) B F) h
       (first-term Γ l l (Tree.hole p) B F (code-type Γ l p i h)
         (decoded-branches-type Γ l p i h)
         (leveled Γ l (l ⊔ℕ l) F
           (Mahlo.decoded-family l (Tree.hole p) (Tree.hole i))
           (⊔ℕ-idempotent l ⁻¹) dF))

-- interpret (pr₂ F x), for x the last variable, of type interpret (pr₁ F).
branch-term :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (p i : Fin n)
  (F : Raw.Expression Theory.Constant n)
  → Interpreted Γ l p i
  → Theory.Derivation
      (term Γ l F (Mahlo.decoded-family l (Tree.hole p) (Tree.hole i)))
  → Theory.Derivation
      (term (Γ ▸[ l ] Mahlo.index l (Tree.hole p) (Tree.hole i) F) l
        (weaken F)
        (Mahlo.decoded-family l (Tree.hole (fsuc p))
          (Tree.hole (fsuc i))))
  → skeleton
      (instantiate
        (Mahlo.decoded-branches l (Tree.hole (fsuc p))
          (Tree.hole (fsuc i)))
        (first l l (Tree.hole (fsuc p))
          (Mahlo.decoded-branches l (Tree.hole (fsuc p))
            (Tree.hole (fsuc i)))
          (weaken F)))
    ＝ skeleton
        (pi l l (weaken (Mahlo.index l (Tree.hole p) (Tree.hole i) F))
          (weaken (weaken (Tree.hole p))))
  → Theory.Derivation
      (type (Γ ▸[ l ] Mahlo.index l (Tree.hole p) (Tree.hole i) F) l
        (Mahlo.branch l (Tree.hole p) (Tree.hole i) F))
branch-term Γ l p i F h dF dF₁ eT =
  let X = Mahlo.index l (Tree.hole p) (Tree.hole i) F
      Γ₁ = Γ ▸[ l ] X
      dX = index-term Γ l p i F h dF
      h₁ = past Γ l p i l X h dX
      B = Mahlo.decoded-branches l (Tree.hole p) (Tree.hole i)
      B₁ = Mahlo.decoded-branches l (Tree.hole (fsuc p))
             (Tree.hole (fsuc i))
      dX₁ = reshaped Γ₁ (suc l)
              (Mahlo.index l (Tree.hole (fsuc p)) (Tree.hole (fsuc i))
                (weaken F))
              (weaken X) (universe l) (universe l) refl refl
              (index-term Γ₁ l (fsuc p) (fsuc i) (weaken F) h₁ dF₁)
      h₂ = past Γ₁ l (fsuc p) (fsuc i) l (weaken X) h₁ dX₁
      dsecond =
        leveled Γ₁ l (l ⊔ℕ l)
          (weaken (second l l (Tree.hole p) B F))
          (pi l l (weaken X) (weaken (weaken (Tree.hole p))))
          (⊔ℕ-idempotent l ⁻¹)
          (reshaped Γ₁ l
            (second l l (Tree.hole (fsuc p)) B₁ (weaken F))
            (weaken (second l l (Tree.hole p) B F))
            (instantiate B₁
              (first l l (Tree.hole (fsuc p)) B₁ (weaken F)))
            (pi l l (weaken X) (weaken (weaken (Tree.hole p))))
            refl eT
            (second-term Γ₁ l l (Tree.hole (fsuc p)) B₁ (weaken F)
              (code-type Γ₁ l (fsuc p) (fsuc i) h₁)
              (decoded-branches-type Γ₁ l (fsuc p) (fsuc i) h₁)
              (leveled Γ₁ l (l ⊔ℕ l) (weaken F)
                (Mahlo.decoded-family l (Tree.hole (fsuc p))
                  (Tree.hole (fsuc i)))
                (⊔ℕ-idempotent l ⁻¹) dF₁)))
      dx = assumed Γ₁ fzero l (weaken X) (Interpreted.valid h₁)
             (newest Γ l X (weaken X) refl)
      dy = reshaped Γ₁ l
             (application l l (weaken X) (weaken (weaken (Tree.hole p)))
               (weaken (second l l (Tree.hole p) B F))
               (Tree.hole fzero))
             (application l l (weaken X) (weaken (weaken (Tree.hole p)))
               (weaken (second l l (Tree.hole p) B F))
               (Tree.hole fzero))
             (instantiate (weaken (weaken (Tree.hole p))) (Tree.hole fzero))
             (Tree.hole (fsuc p)) refl refl
             (application-term Γ₁ l l (weaken X) (weaken (weaken (Tree.hole p)))
               (weaken (second l l (Tree.hole p) B F))
               (Tree.hole fzero) dX₁
               (code-type (Γ₁ ▸[ l ] weaken X) l (fsuc (fsuc p))
                 (fsuc (fsuc i)) h₂)
               dsecond dx)
  in decode-term Γ₁ l (fsuc p) (fsuc i)
       (application l l (weaken X) (weaken (weaken (Tree.hole p)))
         (weaken (second l l (Tree.hole p) B F)) (Tree.hole fzero))
       h₁ dy

-- map D interpret F = interpret (pr₁ F) , λ x → interpret (pr₂ F x).
map-term :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (p i : Fin n)
  (F : Raw.Expression Theory.Constant n)
  → Interpreted Γ l p i
  → Theory.Derivation
      (term Γ l F (Mahlo.decoded-family l (Tree.hole p) (Tree.hole i)))
  → Theory.Derivation
      (term (Γ ▸[ l ] Mahlo.index l (Tree.hole p) (Tree.hole i) F) l
        (weaken F)
        (Mahlo.decoded-family l (Tree.hole (fsuc p))
          (Tree.hole (fsuc i))))
  → skeleton
      (instantiate
        (Mahlo.decoded-branches l (Tree.hole (fsuc p))
          (Tree.hole (fsuc i)))
        (first l l (Tree.hole (fsuc p))
          (Mahlo.decoded-branches l (Tree.hole (fsuc p))
            (Tree.hole (fsuc i)))
          (weaken F)))
    ＝ skeleton
        (pi l l (weaken (Mahlo.index l (Tree.hole p) (Tree.hole i) F))
          (weaken (weaken (Tree.hole p))))
  → skeleton
      (pi l (suc l) (Mahlo.index l (Tree.hole p) (Tree.hole i) F)
        (universe l))
    ＝ skeleton
        (instantiate (Mahlo.family-branches l)
          (Mahlo.index l (Tree.hole p) (Tree.hole i) F))
  → Theory.Derivation
      (term Γ (suc l) (Mahlo.map l (Tree.hole p) (Tree.hole i) F)
        (Mahlo.family l))
map-term Γ l p i F h dF dF₁ eT eF =
  let X = Mahlo.index l (Tree.hole p) (Tree.hole i) F
      v = Interpreted.valid h
      dX = index-term Γ l p i F h dF
      v₁ = extended-context Γ l X dX
      dλ = reshaped Γ (suc l)
             (lambda l (suc l) X (universe l)
               (Mahlo.branch l (Tree.hole p) (Tree.hole i) F))
             (lambda l (suc l) X (universe l)
               (Mahlo.branch l (Tree.hole p) (Tree.hole i) F))
             (pi l (suc l) X (universe l))
             (instantiate (Mahlo.family-branches l) X) refl eF
             (leveled Γ (l ⊔ℕ suc l) (suc l)
               (lambda l (suc l) X (universe l)
                 (Mahlo.branch l (Tree.hole p) (Tree.hole i) F))
               (pi l (suc l) X (universe l)) (joined l)
               (lambda-term Γ l (suc l) X (universe l)
                 (Mahlo.branch l (Tree.hole p) (Tree.hole i) F) dX
                 (universe-type (Γ ▸[ l ] X) l v₁)
                 (branch-term Γ l p i F h dF dF₁ eT)))
  in leveled Γ (suc l ⊔ℕ suc l) (suc l)
       (Mahlo.map l (Tree.hole p) (Tree.hole i) F) (Mahlo.family l)
       (⊔ℕ-idempotent (suc l))
       (pair-term Γ (suc l) (suc l) (universe l) (Mahlo.family-branches l) X
         (lambda l (suc l) X (universe l)
           (Mahlo.branch l (Tree.hole p) (Tree.hole i) F))
         (universe-type Γ l v) (family-branches-type Γ l v) dX dλ)

------------------------------------------------------------------------
-- The fields of a closure

-- (F : Family (Decode D interpret)) → Name interpret (former of map F),
-- for the former of Π, Σ or W with its formation rule.
names-former-type :
  (former :
     {k : ℕ} → ℕ → ℕ → Raw.Expression Theory.Constant k
     → Raw.Expression Theory.Constant (suc k)
     → Raw.Expression Theory.Constant k)
  → (formation :
       {k : ℕ} (Δ : Context Theory.Constant k) (m m′ : ℕ)
       (A : Raw.Expression Theory.Constant k)
       (B : Raw.Expression Theory.Constant (suc k))
       → Theory.Derivation (type Δ m A)
       → Theory.Derivation (type (Δ ▸[ m ] A) m′ B)
       → Theory.Derivation (type Δ (m ⊔ℕ m′) (former m m′ A B)))
  → {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (p i : Fin n)
  → Interpreted Γ l p i
  → skeleton
      (former l l
        (Mahlo.index l (Tree.hole (fsuc (fsuc p)))
          (Tree.hole (fsuc (fsuc i))) (Tree.hole (fsuc fzero)))
        (Mahlo.branch l (Tree.hole (fsuc (fsuc p)))
          (Tree.hole (fsuc (fsuc i))) (Tree.hole (fsuc fzero))))
    ＝ skeleton
        (weaken
          (former l l
            (Mahlo.index l (Tree.hole (fsuc p)) (Tree.hole (fsuc i))
              (Tree.hole fzero))
            (Mahlo.branch l (Tree.hole (fsuc p)) (Tree.hole (fsuc i))
              (Tree.hole fzero))))
  → Theory.Derivation
      (type Γ (suc l)
        (pi l (suc l) (Mahlo.decoded-family l (Tree.hole p) (Tree.hole i))
          (Mahlo.name l (Tree.hole (fsuc p)) (Tree.hole (fsuc i))
            (former l l
              (Mahlo.index l (Tree.hole (fsuc p)) (Tree.hole (fsuc i))
                (Tree.hole fzero))
              (Mahlo.branch l (Tree.hole (fsuc p)) (Tree.hole (fsuc i))
                (Tree.hole fzero))))))
names-former-type former formation Γ l p i h e =
  let DF = Mahlo.decoded-family l (Tree.hole p) (Tree.hole i)
      DF₁ = Mahlo.decoded-family l (Tree.hole (fsuc p))
              (Tree.hole (fsuc i))
      DF₂ = Mahlo.decoded-family l (Tree.hole (fsuc (fsuc p)))
              (Tree.hole (fsuc (fsuc i)))
      DF₃ = Mahlo.decoded-family l (Tree.hole (fsuc (fsuc (fsuc p))))
              (Tree.hole (fsuc (fsuc (fsuc i))))
      dDF = decoded-family-type Γ l p i h
      Γ₁ = Γ ▸[ l ] DF
      h₁ = past Γ l p i l DF h dDF
      F₁ = newest Γ l DF DF₁ refl
      Γ₂ = Γ₁ ▸[ l ] Tree.hole (fsuc p)
      h₂ = past Γ₁ l (fsuc p) (fsuc i) l (Tree.hole (fsuc p)) h₁
             (code-type Γ₁ l (fsuc p) (fsuc i) h₁)
      F₂ = older Γ₁ l (Tree.hole (fsuc p)) fzero l DF₁ DF₂ F₁ refl
      dF₂ = assumed Γ₂ (fsuc fzero) l DF₂ (Interpreted.valid h₂) F₂
      X₂ = Mahlo.index l (Tree.hole (fsuc (fsuc p)))
             (Tree.hole (fsuc (fsuc i))) (Tree.hole (fsuc fzero))
      Y₂ = Mahlo.branch l (Tree.hole (fsuc (fsuc p)))
             (Tree.hole (fsuc (fsuc i))) (Tree.hole (fsuc fzero))
      X₁ = Mahlo.index l (Tree.hole (fsuc p)) (Tree.hole (fsuc i))
             (Tree.hole fzero)
      Y₁ = Mahlo.branch l (Tree.hole (fsuc p)) (Tree.hole (fsuc i))
             (Tree.hole fzero)
      dX₂ = index-term Γ₂ l (fsuc (fsuc p)) (fsuc (fsuc i))
              (Tree.hole (fsuc fzero)) h₂ dF₂
      h₃ = past Γ₂ l (fsuc (fsuc p)) (fsuc (fsuc i)) l X₂ h₂ dX₂
      dF₃ = assumed (Γ₂ ▸[ l ] X₂) (fsuc (fsuc fzero)) l DF₃
              (Interpreted.valid h₃)
              (older Γ₂ l X₂ (fsuc fzero) l DF₂ DF₃ F₂ refl)
      dY₂ = branch-term Γ₂ l (fsuc (fsuc p)) (fsuc (fsuc i))
              (Tree.hole (fsuc fzero)) h₂ dF₂ dF₃ refl
      dc = reshaped Γ₂ (suc l) (former l l X₂ Y₂)
             (weaken (former l l X₁ Y₁)) (universe l) (universe l) e refl
             (type-leveled Γ₂ (l ⊔ℕ l) l (former l l X₂ Y₂) (⊔ℕ-idempotent l)
               (formation Γ₂ l l X₂ Y₂ dX₂ dY₂))
      N = Mahlo.name l (Tree.hole (fsuc p)) (Tree.hole (fsuc i))
            (former l l X₁ Y₁)
  in type-leveled Γ (l ⊔ℕ suc l) (suc l) (pi l (suc l) DF N) (joined l)
       (pi-type Γ l (suc l) DF N dDF
         (name-type Γ₁ l (fsuc p) (fsuc i) (former l l X₁ Y₁) h₁ dc))

-- (a : A) (x y : interpret a) → Name interpret (x ＝ y).
names-identities-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (p i : Fin n)
  → Interpreted Γ l p i
  → Theory.Derivation
      (type Γ (suc l) (Mahlo.names-identities l (Tree.hole p) (Tree.hole i)))
names-identities-type Γ l p i h =
  let p₁ = fsuc p
      i₁ = fsuc i
      p₂ = fsuc p₁
      i₂ = fsuc i₁
      p₃ = fsuc p₂
      i₃ = fsuc i₂
      p₄ = fsuc p₃
      i₄ = fsuc i₃
      dA = code-type Γ l p i h
      Γ₁ = Γ ▸[ l ] Tree.hole p
      h₁ = past Γ l p i l (Tree.hole p) h dA
      a₁ = newest Γ l (Tree.hole p) (Tree.hole p₁) refl
      D₁ = Mahlo.decode l (Tree.hole p₁) (Tree.hole i₁) (Tree.hole fzero)
      dD₁ = decode-term Γ₁ l p₁ i₁ (Tree.hole fzero) h₁
              (element Γ l p i h)
      Γ₂ = Γ₁ ▸[ l ] D₁
      h₂ = past Γ₁ l p₁ i₁ l D₁ h₁ dD₁
      a₂ = older Γ₁ l D₁ fzero l (Tree.hole p₁) (Tree.hole p₂) a₁ refl
      x₂ = newest Γ₁ l D₁
             (Mahlo.decode l (Tree.hole p₂) (Tree.hole i₂)
               (Tree.hole (fsuc fzero)))
             refl
      D₂ = Mahlo.decode l (Tree.hole p₂) (Tree.hole i₂)
             (Tree.hole (fsuc fzero))
      dD₂ = decode-term Γ₂ l p₂ i₂ (Tree.hole (fsuc fzero)) h₂
              (assumed Γ₂ (fsuc fzero) l (Tree.hole p₂)
                (Interpreted.valid h₂) a₂)
      Γ₃ = Γ₂ ▸[ l ] D₂
      h₃ = past Γ₂ l p₂ i₂ l D₂ h₂ dD₂
      a₃ = older Γ₂ l D₂ (fsuc fzero) l (Tree.hole p₂) (Tree.hole p₃)
             a₂ refl
      D₃ = Mahlo.decode l (Tree.hole p₃) (Tree.hole i₃)
             (Tree.hole (fsuc (fsuc fzero)))
      x₃ = older Γ₂ l D₂ fzero l D₂ D₃ x₂ refl
      y₃ = newest Γ₂ l D₂ D₃ refl
      c = identity l D₃ (Tree.hole (fsuc fzero)) (Tree.hole fzero)
      Γ₄ = Γ₃ ▸[ l ] Tree.hole p₃
      h₄ = past Γ₃ l p₃ i₃ l (Tree.hole p₃) h₃ (code-type Γ₃ l p₃ i₃ h₃)
      v₄ = Interpreted.valid h₄
      D₄ = Mahlo.decode l (Tree.hole p₄) (Tree.hole i₄)
             (Tree.hole (fsuc (fsuc (fsuc fzero))))
      da₄ = assumed Γ₄ (fsuc (fsuc (fsuc fzero))) l
              (Tree.hole p₄) v₄
              (older Γ₃ l (Tree.hole p₃) (fsuc (fsuc fzero)) l
                (Tree.hole p₃) (Tree.hole p₄) a₃ refl)
      dx₄ = assumed Γ₄ (fsuc (fsuc fzero)) l D₄ v₄
              (older Γ₃ l (Tree.hole p₃) (fsuc fzero) l D₃ D₄ x₃ refl)
      dy₄ = assumed Γ₄ (fsuc fzero) l D₄ v₄
              (older Γ₃ l (Tree.hole p₃) fzero l D₃ D₄ y₃ refl)
      dc = reshaped Γ₄ (suc l)
             (identity l D₄ (Tree.hole (fsuc (fsuc fzero)))
               (Tree.hole (fsuc fzero)))
             (weaken c) (universe l) (universe l) refl refl
             (identity-type Γ₄ l D₄ (Tree.hole (fsuc (fsuc fzero)))
               (Tree.hole (fsuc fzero))
               (decode-term Γ₄ l p₄ i₄
                 (Tree.hole (fsuc (fsuc (fsuc fzero)))) h₄ da₄)
               dx₄ dy₄)
      N = Mahlo.name l (Tree.hole p₃) (Tree.hole i₃) c
      dN = name-type Γ₃ l p₃ i₃ c h₃ dc
      dy = type-leveled Γ₂ (l ⊔ℕ suc l) (suc l) (pi l (suc l) D₂ N) (joined l)
             (pi-type Γ₂ l (suc l) D₂ N dD₂ dN)
      dx = type-leveled Γ₁ (l ⊔ℕ suc l) (suc l)
             (pi l (suc l) D₁ (pi l (suc l) D₂ N)) (joined l)
             (pi-type Γ₁ l (suc l) D₁ (pi l (suc l) D₂ N) dD₁ dy)
  in type-leveled Γ (l ⊔ℕ suc l) (suc l)
       (Mahlo.names-identities l (Tree.hole p) (Tree.hole i)) (joined l)
       (pi-type Γ l (suc l) (Tree.hole p)
         (pi l (suc l) D₁ (pi l (suc l) D₂ N)) dA dx)

-- inner : Family (Decode D interpret) → Family (Decode D interpret).
inner-map-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (p i : Fin n)
  → Interpreted Γ l p i
  → Theory.Derivation
      (type Γ l (Mahlo.inner-map l (Tree.hole p) (Tree.hole i)))
inner-map-type Γ l p i h =
  let DF = Mahlo.decoded-family l (Tree.hole p) (Tree.hole i)
      dDF = decoded-family-type Γ l p i h
  in type-leveled Γ (l ⊔ℕ l) l
       (Mahlo.inner-map l (Tree.hole p) (Tree.hole i)) (⊔ℕ-idempotent l)
       (pi-type Γ l l DF
         (Mahlo.decoded-family l (Tree.hole (fsuc p))
           (Tree.hole (fsuc i)))
         dDF
         (decoded-family-type (Γ ▸[ l ] DF) l (fsuc p) (fsuc i)
           (past Γ l p i l DF h dDF)))

-- inner-β : (F : Family (Decode D interpret))
-- → map D interpret (inner F) ＝ Ψ (map D interpret F), for Ψ an
-- operator at position ψ and inner at position j.
inner-law-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (ψ p i j : Fin n)
  → Interpreted Γ l p i
  → Assumed Γ ψ (suc l) (Mahlo.operator l)
  → Assumed Γ j l (Mahlo.inner-map l (Tree.hole p) (Tree.hole i))
  → Theory.Derivation
      (type Γ (suc l)
        (Mahlo.inner-law l (Tree.hole ψ) (Tree.hole p) (Tree.hole i)
          (Tree.hole j)))
inner-law-type Γ l ψ p i j h aΨ aJ =
  let p₁ = fsuc p
      i₁ = fsuc i
      p₂ = fsuc p₁
      i₂ = fsuc i₁
      p₃ = fsuc p₂
      i₃ = fsuc i₂
      DF = Mahlo.decoded-family l (Tree.hole p) (Tree.hole i)
      DF₁ = Mahlo.decoded-family l (Tree.hole p₁) (Tree.hole i₁)
      DF₂ = Mahlo.decoded-family l (Tree.hole p₂) (Tree.hole i₂)
      DF₃ = Mahlo.decoded-family l (Tree.hole p₃) (Tree.hole i₃)
      dDF = decoded-family-type Γ l p i h
      Γ₁ = Γ ▸[ l ] DF
      h₁ = past Γ l p i l DF h dDF
      v₁ = Interpreted.valid h₁
      F₁ = newest Γ l DF DF₁ refl
      dF₁ = assumed Γ₁ fzero l DF₁ v₁ F₁
      J₁ = older Γ l DF j l (Mahlo.inner-map l (Tree.hole p) (Tree.hole i))
             (pi l l DF₁ DF₂) aJ refl
      dDF₁ = decoded-family-type Γ₁ l p₁ i₁ h₁
      dDF₂ = decoded-family-type (Γ₁ ▸[ l ] DF₁) l p₂ i₂
               (past Γ₁ l p₁ i₁ l DF₁ h₁ dDF₁)
      JF = application l l DF₁ DF₂ (Tree.hole (fsuc j))
             (Tree.hole fzero)
      dJF = reshaped Γ₁ l JF JF (instantiate DF₂ (Tree.hole fzero)) DF₁
              refl refl
              (application-term Γ₁ l l DF₁ DF₂ (Tree.hole (fsuc j))
                (Tree.hole fzero) dDF₁ dDF₂
                (leveled Γ₁ l (l ⊔ℕ l) (Tree.hole (fsuc j)) (pi l l DF₁ DF₂)
                  (⊔ℕ-idempotent l ⁻¹)
                  (assumed Γ₁ (fsuc j) l (pi l l DF₁ DF₂) v₁ J₁))
                dF₁)
      XJ = Mahlo.index l (Tree.hole p₁) (Tree.hole i₁) JF
      Γ₂ = Γ₁ ▸[ l ] XJ
      h₂ = past Γ₁ l p₁ i₁ l XJ h₁ (index-term Γ₁ l p₁ i₁ JF h₁ dJF)
      v₂ = Interpreted.valid h₂
      dDF₂′ = decoded-family-type Γ₂ l p₂ i₂ h₂
      dDF₃ = decoded-family-type (Γ₂ ▸[ l ] DF₂) l p₃ i₃
               (past Γ₂ l p₂ i₂ l DF₂ h₂ dDF₂′)
      JF₂ = application l l DF₂ DF₃ (Tree.hole (fsuc (fsuc j)))
              (Tree.hole (fsuc fzero))
      dJF₂ = reshaped Γ₂ l JF₂ (weaken JF)
               (instantiate DF₃ (Tree.hole (fsuc fzero))) DF₂ refl refl
               (application-term Γ₂ l l DF₂ DF₃
                 (Tree.hole (fsuc (fsuc j)))
                 (Tree.hole (fsuc fzero)) dDF₂′ dDF₃
                 (leveled Γ₂ l (l ⊔ℕ l) (Tree.hole (fsuc (fsuc j)))
                   (pi l l DF₂ DF₃) (⊔ℕ-idempotent l ⁻¹)
                   (assumed Γ₂ (fsuc (fsuc j)) l (pi l l DF₂ DF₃) v₂
                     (older Γ₁ l XJ (fsuc j) l (pi l l DF₁ DF₂)
                       (pi l l DF₂ DF₃) J₁ refl)))
                 (assumed Γ₂ (fsuc fzero) l DF₂ v₂
                   (older Γ₁ l XJ fzero l DF₁ DF₂ F₁ refl)))
      dL = map-term Γ₁ l p₁ i₁ JF h₁ dJF dJF₂ refl refl
      X₀ = Mahlo.index l (Tree.hole p₁) (Tree.hole i₁) (Tree.hole fzero)
      h₀ = past Γ₁ l p₁ i₁ l X₀ h₁
             (index-term Γ₁ l p₁ i₁ (Tree.hole fzero) h₁ dF₁)
      dF₀ = assumed (Γ₁ ▸[ l ] X₀) (fsuc fzero) l DF₂
              (Interpreted.valid h₀)
              (older Γ₁ l X₀ fzero l DF₁ DF₂ F₁ refl)
      dmap = map-term Γ₁ l p₁ i₁ (Tree.hole fzero) h₁ dF₁ dF₀ refl refl
      M = Mahlo.map l (Tree.hole p₁) (Tree.hole i₁) (Tree.hole fzero)
      dFam = family-type Γ₁ l v₁
      dΨ = leveled Γ₁ (suc l) (suc l ⊔ℕ suc l) (Tree.hole (fsuc ψ))
             (pi (suc l) (suc l) (Mahlo.family l) (Mahlo.family l))
             (⊔ℕ-idempotent (suc l) ⁻¹)
             (assumed Γ₁ (fsuc ψ) (suc l)
               (pi (suc l) (suc l) (Mahlo.family l) (Mahlo.family l)) v₁
               (older Γ l DF ψ (suc l) (Mahlo.operator l)
                 (pi (suc l) (suc l) (Mahlo.family l) (Mahlo.family l)) aΨ
                 refl))
      ΨM = application (suc l) (suc l) (Mahlo.family l) (Mahlo.family l)
             (Tree.hole (fsuc ψ)) M
      dR = reshaped Γ₁ (suc l) ΨM ΨM (instantiate (Mahlo.family l) M)
             (Mahlo.family l) refl refl
             (application-term Γ₁ (suc l) (suc l) (Mahlo.family l)
               (Mahlo.family l) (Tree.hole (fsuc ψ)) M dFam
               (family-type (Γ₁ ▸[ suc l ] Mahlo.family l) l
                 (extended-context Γ₁ (suc l) (Mahlo.family l) dFam))
               dΨ dmap)
      E = identity (suc l) (Mahlo.family l)
            (Mahlo.map l (Tree.hole p₁) (Tree.hole i₁) JF) ΨM
  in type-leveled Γ (l ⊔ℕ suc l) (suc l)
       (Mahlo.inner-law l (Tree.hole ψ) (Tree.hole p) (Tree.hole i)
         (Tree.hole j))
       (joined l)
       (pi-type Γ l (suc l) DF E dDF
         (identity-type Γ₁ (suc l) (Mahlo.family l)
           (Mahlo.map l (Tree.hole p₁) (Tree.hole i₁) JF) ΨM dFam dL dR))

-- Name interpret (Lift B), for B a type at level 0 written in the scope of
-- a further element of the code.
lifted-name-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ) (p i : Fin n)
  (B : Raw.Expression Theory.Constant n)
  (B′ : Raw.Expression Theory.Constant (suc n))
  → Interpreted Γ l p i
  → (Theory.Derivation (context (Γ ▸[ l ] Tree.hole p))
     → Theory.Derivation (type (Γ ▸[ l ] Tree.hole p) 0 B′))
  → skeleton (lifted 0 l B′) ＝ skeleton (weaken (lifted 0 l B))
  → Theory.Derivation
      (type Γ (suc l) (Mahlo.name l (Tree.hole p) (Tree.hole i) (lifted 0 l B)))
lifted-name-type Γ l p i B B′ h dB e =
  let Γ₁ = Γ ▸[ l ] Tree.hole p
      v₁ = extended-context Γ l (Tree.hole p) (code-type Γ l p i h)
  in name-type Γ l p i (lifted 0 l B) h
       (reshaped Γ₁ (suc l) (lifted 0 l B′) (weaken (lifted 0 l B))
         (universe l) (universe l) e refl
         (lifted-type Γ₁ 0 l B′ (dB v₁)))

------------------------------------------------------------------------
-- Closures, reflections and the Mahlo rule

-- Closure Q Ψ A in the context of Ψ and A: the iterated Σ of its fields,
-- each typed in the context of the fields before it.
closure-type :
  (l : ℕ)
  → Theory.Derivation
      (type (∅ ▸[ suc l ] Mahlo.operator l ▸[ suc l ] universe l) (suc l)
        (Mahlo.closure l))
closure-type l =
  let Δ = ∅ ▸[ suc l ] Mahlo.operator l
      vΔ = extended-context ∅ (suc l) (Mahlo.operator l)
             (operator-type ∅ l empty-context)
      Δ₀ = Δ ▸[ suc l ] universe l
      v₀ = extended-context Δ (suc l) (universe l) (universe-type Δ l vΔ)
      A₀ = newest Δ (suc l) (universe l) (universe l) refl
      Ψ₀ = older Δ (suc l) (universe l) (# 0) (suc l) (Mahlo.operator l)
             (Mahlo.operator l)
             (newest ∅ (suc l) (Mahlo.operator l) (Mahlo.operator l) refl)
             refl
      dA₀ = assumed Δ₀ (# 0) (suc l) (universe l) v₀ A₀
      T₁ = pi l (suc l) (Tree.hole (# 0)) (universe l)
      d₁ = type-leveled Δ₀ (l ⊔ℕ suc l) (suc l) T₁ (joined l)
             (pi-type Δ₀ l (suc l) (Tree.hole (# 0)) (universe l) dA₀
               (universe-type (Δ₀ ▸[ l ] Tree.hole (# 0)) l
                 (extended-context Δ₀ l (Tree.hole (# 0)) dA₀)))
      Δ₁ = Δ₀ ▸[ suc l ] T₁
      h₁ : Interpreted Δ₁ l (# 1) (# 0)
      h₁ = record
        { valid = extended-context Δ₀ (suc l) T₁ d₁
        ; code =
            older Δ₀ (suc l) T₁ (# 0) (suc l) (universe l) (universe l) A₀
              refl
        ; interpretation =
            newest Δ₀ (suc l) T₁ (pi l (suc l) (Tree.hole (# 1)) (universe l))
              refl
        }
      Ψ₁ = older Δ₀ (suc l) T₁ (# 1) (suc l) (Mahlo.operator l)
             (Mahlo.operator l) Ψ₀ refl
      T₂ = Mahlo.name l (Tree.hole (# 1)) (Tree.hole (# 0)) (lifted 0 l empty)
      d₂ = lifted-name-type Δ₁ l (# 1) (# 0) empty empty h₁
             (empty-type (Δ₁ ▸[ l ] Tree.hole (# 1))) refl
      Δ₂ = Δ₁ ▸[ suc l ] T₂
      h₂ = past Δ₁ l (# 1) (# 0) (suc l) T₂ h₁ d₂
      Ψ₂ = older Δ₁ (suc l) T₂ (# 2) (suc l) (Mahlo.operator l)
             (Mahlo.operator l) Ψ₁ refl
      T₃ = Mahlo.name l (Tree.hole (# 2)) (Tree.hole (# 1)) (lifted 0 l unit)
      d₃ = lifted-name-type Δ₂ l (# 2) (# 1) unit unit h₂
             (unit-type (Δ₂ ▸[ l ] Tree.hole (# 2))) refl
      Δ₃ = Δ₂ ▸[ suc l ] T₃
      h₃ = past Δ₂ l (# 2) (# 1) (suc l) T₃ h₂ d₃
      Ψ₃ = older Δ₂ (suc l) T₃ (# 3) (suc l) (Mahlo.operator l)
             (Mahlo.operator l) Ψ₂ refl
      T₄ = Mahlo.name l (Tree.hole (# 3)) (Tree.hole (# 2))
             (lifted 0 l (sum 0 0 unit unit))
      d₄ = lifted-name-type Δ₃ l (# 3) (# 2) (sum 0 0 unit unit)
             (sum 0 0 unit unit) h₃
             (λ v → sum-type (Δ₃ ▸[ l ] Tree.hole (# 3)) 0 0 unit unit
                      (unit-type (Δ₃ ▸[ l ] Tree.hole (# 3)) v)
                      (unit-type (Δ₃ ▸[ l ] Tree.hole (# 3)) v))
             refl
      Δ₄ = Δ₃ ▸[ suc l ] T₄
      h₄ = past Δ₃ l (# 3) (# 2) (suc l) T₄ h₃ d₄
      Ψ₄ = older Δ₃ (suc l) T₄ (# 4) (suc l) (Mahlo.operator l)
             (Mahlo.operator l) Ψ₃ refl
      T₅ = Mahlo.name l (Tree.hole (# 4)) (Tree.hole (# 3))
             (lifted 0 l natural)
      d₅ = lifted-name-type Δ₄ l (# 4) (# 3) natural natural h₄
             (natural-type (Δ₄ ▸[ l ] Tree.hole (# 4))) refl
      Δ₅ = Δ₄ ▸[ suc l ] T₅
      h₅ = past Δ₄ l (# 4) (# 3) (suc l) T₅ h₄ d₅
      Ψ₅ = older Δ₄ (suc l) T₅ (# 5) (suc l) (Mahlo.operator l)
             (Mahlo.operator l) Ψ₄ refl
      T₆ = Mahlo.names-products l (Tree.hole (# 5)) (Tree.hole (# 4))
      d₆ = names-former-type pi pi-type Δ₅ l (# 5) (# 4) h₅ refl
      Δ₆ = Δ₅ ▸[ suc l ] T₆
      h₆ = past Δ₅ l (# 5) (# 4) (suc l) T₆ h₅ d₆
      Ψ₆ = older Δ₅ (suc l) T₆ (# 6) (suc l) (Mahlo.operator l)
             (Mahlo.operator l) Ψ₅ refl
      T₇ = Mahlo.names-sums l (Tree.hole (# 6)) (Tree.hole (# 5))
      d₇ = names-former-type sigma sigma-type Δ₆ l (# 6) (# 5) h₆ refl
      Δ₇ = Δ₆ ▸[ suc l ] T₇
      h₇ = past Δ₆ l (# 6) (# 5) (suc l) T₇ h₆ d₇
      Ψ₇ = older Δ₆ (suc l) T₇ (# 7) (suc l) (Mahlo.operator l)
             (Mahlo.operator l) Ψ₆ refl
      T₈ = Mahlo.names-trees l (Tree.hole (# 7)) (Tree.hole (# 6))
      d₈ = names-former-type tree tree-type Δ₇ l (# 7) (# 6) h₇ refl
      Δ₈ = Δ₇ ▸[ suc l ] T₈
      h₈ = past Δ₇ l (# 7) (# 6) (suc l) T₈ h₇ d₈
      Ψ₈ = older Δ₇ (suc l) T₈ (# 8) (suc l) (Mahlo.operator l)
             (Mahlo.operator l) Ψ₇ refl
      T₉ = Mahlo.names-identities l (Tree.hole (# 8)) (Tree.hole (# 7))
      d₉ = names-identities-type Δ₈ l (# 8) (# 7) h₈
      Δ₉ = Δ₈ ▸[ suc l ] T₉
      h₉ = past Δ₈ l (# 8) (# 7) (suc l) T₉ h₈ d₉
      Ψ₉ = older Δ₈ (suc l) T₉ (# 9) (suc l) (Mahlo.operator l)
             (Mahlo.operator l) Ψ₈ refl
      T₁₀ = Mahlo.inner-map l (Tree.hole (# 9)) (Tree.hole (# 8))
      d₁₀ = inner-map-type Δ₉ l (# 9) (# 8) h₉
      Δ₁₀ = Δ₉ ▸[ l ] T₁₀
      h₁₀ = past Δ₉ l (# 9) (# 8) l T₁₀ h₉ d₁₀
      Ψ₁₀ = older Δ₉ l T₁₀ (# 10) (suc l) (Mahlo.operator l)
             (Mahlo.operator l) Ψ₉ refl
      J₁₀ = newest Δ₉ l T₁₀
              (Mahlo.inner-map l (Tree.hole (# 10)) (Tree.hole (# 9))) refl
      T₁₁ = Mahlo.inner-law l (Tree.hole (# 11)) (Tree.hole (# 10))
              (Tree.hole (# 9)) (Tree.hole (# 0))
      d₁₁ = inner-law-type Δ₁₀ l (# 11) (# 10) (# 9) (# 0) h₁₀ Ψ₁₀ J₁₀
      S₁₀ = sigma l (suc l) T₁₀ T₁₁
      e₁₀ = type-leveled Δ₉ (l ⊔ℕ suc l) (suc l) S₁₀ (joined l)
              (sigma-type Δ₉ l (suc l) T₁₀ T₁₁ d₁₀ d₁₁)
      S₉ = sigma (suc l) (suc l) T₉ S₁₀
      e₉ = type-leveled Δ₈ (suc l ⊔ℕ suc l) (suc l) S₉ (⊔ℕ-idempotent (suc l))
             (sigma-type Δ₈ (suc l) (suc l) T₉ S₁₀ d₉ e₁₀)
      S₈ = sigma (suc l) (suc l) T₈ S₉
      e₈ = type-leveled Δ₇ (suc l ⊔ℕ suc l) (suc l) S₈ (⊔ℕ-idempotent (suc l))
             (sigma-type Δ₇ (suc l) (suc l) T₈ S₉ d₈ e₉)
      S₇ = sigma (suc l) (suc l) T₇ S₈
      e₇ = type-leveled Δ₆ (suc l ⊔ℕ suc l) (suc l) S₇ (⊔ℕ-idempotent (suc l))
             (sigma-type Δ₆ (suc l) (suc l) T₇ S₈ d₇ e₈)
      S₆ = sigma (suc l) (suc l) T₆ S₇
      e₆ = type-leveled Δ₅ (suc l ⊔ℕ suc l) (suc l) S₆ (⊔ℕ-idempotent (suc l))
             (sigma-type Δ₅ (suc l) (suc l) T₆ S₇ d₆ e₇)
      S₅ = sigma (suc l) (suc l) T₅ S₆
      e₅ = type-leveled Δ₄ (suc l ⊔ℕ suc l) (suc l) S₅ (⊔ℕ-idempotent (suc l))
             (sigma-type Δ₄ (suc l) (suc l) T₅ S₆ d₅ e₆)
      S₄ = sigma (suc l) (suc l) T₄ S₅
      e₄ = type-leveled Δ₃ (suc l ⊔ℕ suc l) (suc l) S₄ (⊔ℕ-idempotent (suc l))
             (sigma-type Δ₃ (suc l) (suc l) T₄ S₅ d₄ e₅)
      S₃ = sigma (suc l) (suc l) T₃ S₄
      e₃ = type-leveled Δ₂ (suc l ⊔ℕ suc l) (suc l) S₃ (⊔ℕ-idempotent (suc l))
             (sigma-type Δ₂ (suc l) (suc l) T₃ S₄ d₃ e₄)
      S₂ = sigma (suc l) (suc l) T₂ S₃
      e₂ = type-leveled Δ₁ (suc l ⊔ℕ suc l) (suc l) S₂ (⊔ℕ-idempotent (suc l))
             (sigma-type Δ₁ (suc l) (suc l) T₂ S₃ d₂ e₃)
  in type-leveled Δ₀ (suc l ⊔ℕ suc l) (suc l) (Mahlo.closure l)
       (⊔ℕ-idempotent (suc l))
       (sigma-type Δ₀ (suc l) (suc l) T₁ S₂ d₁ e₂)

-- Reflection Q Ψ = Σ carrier ꞉ U , Closure Q Ψ carrier.
reflection-type :
  (l : ℕ)
  → Theory.Derivation
      (type (∅ ▸[ suc l ] Mahlo.operator l) (suc l) (Mahlo.reflection l))
reflection-type l =
  let Δ = ∅ ▸[ suc l ] Mahlo.operator l
      vΔ = extended-context ∅ (suc l) (Mahlo.operator l)
             (operator-type ∅ l empty-context)
  in type-leveled Δ (suc l ⊔ℕ suc l) (suc l) (Mahlo.reflection l)
       (⊔ℕ-idempotent (suc l))
       (sigma-type Δ (suc l) (suc l) (universe l) (Mahlo.closure l)
         (universe-type Δ l vΔ) (closure-type l))

-- Mahlo Q = (Ψ : Operator D) → Reflection Q Ψ: the statement of the
-- constant mahlo l is a type at level suc l.
mahlo-type :
  (l : ℕ) → Theory.Derivation (type ∅ (suc l) (Mahlo.mahlo l))
mahlo-type l =
  type-leveled ∅ (suc l ⊔ℕ suc l) (suc l) (Mahlo.mahlo l)
    (⊔ℕ-idempotent (suc l))
    (pi-type ∅ (suc l) (suc l) (Mahlo.operator l) (Mahlo.reflection l)
      (operator-type ∅ l empty-context) (reflection-type l))

-- The constant mahlo l is a term of its statement in every valid context:
-- the constant rule, with `mahlo-type` as its premise.
mahlo-term :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ)
  → Theory.Derivation (context Γ)
  → Theory.Derivation
      (term Γ (suc l) (constant (Theory.mahlo l)) (closed n (Mahlo.mahlo l)))
mahlo-term Γ l v =
  Tree.node (Theory.constants , Constants.axiom Γ (Theory.mahlo l))
    (λ { fzero → v ; (fsuc fzero) → mahlo-type l
       ; (fsuc (fsuc ())) })
