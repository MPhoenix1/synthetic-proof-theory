{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Derived where

-- The rules of the core theory as functions on its derivations
-- (Theory.Derivation), and rules derived from them, for building
-- derivations of judgments about given expressions.
--
-- - Contexts: the empty context and its extensions (`empty-context`,
--   `extended-context`).
-- - Moving a judgment along extensional equality (`extensional`): a term
--   judgment with its term and type replaced by related trees
--   (`rewritten`), in particular by trees with the same skeletons
--   (`reshaped`, by Skeleton's `related`), and at an equal level
--   (`leveled`, `type-leveled`).
-- - Variables: the level and type a variable is assumed to have, up to
--   extensional equality (`Assumed`), for the newest variable and the
--   older ones of an extended context, along a relation or by skeletons
--   (`newest-related`, `older-related`, `newest`, `older`), and the
--   variable with them (`assumed`). Weakening keeps extensional equality
--   (`weakened`, Formers.Substitution's `weaken-related`).
-- - One function per rule used: formation of the universes, Lift, Π, Σ,
--   identity types, W, 0, 1, + and ℕ; λ, application and its β rule; pairs
--   and projections; reflexivity and J; congruence of application and of
--   identity types; reflexivity, symmetry and transitivity of equality,
--   and conversion.

open import SPT.Base
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Tree as Tree
import SPT.Foundation.Tree.Relation as Relation
open import SPT.MartinLof.Formers using
  (universe; lifted; pi; lambda; application; sigma; pair; first; second
  ; identity; reflexivity; path-induction; tree; empty; unit; sum; natural
  ; weaken; instantiate; instantiate₂)
open import SPT.MartinLof.Formers.Substitution using (weaken-related)
open import SPT.MartinLof.Judgment using
  (Context; ∅; _▸[_]_; level; lookup; Judgment; context; term; term-equal; type
  ; type-equal; Judgment-Rel; term-rel; term-equal-rel; context-refl)
import SPT.MartinLof.Raw as Raw
import SPT.MartinLof.Rules.Empty as Empty
import SPT.MartinLof.Rules.Identity as Identity
import SPT.MartinLof.Rules.Lift as Lift
import SPT.MartinLof.Rules.Natural as Natural
import SPT.MartinLof.Rules.Pi as Pi
import SPT.MartinLof.Rules.Sigma as Sigma
import SPT.MartinLof.Rules.Sum as Sum
import SPT.MartinLof.Rules.Unit as Unit
import SPT.MartinLof.Rules.Universe as Universe
import SPT.MartinLof.Rules.WellFounded as WellFounded
open import SPT.MartinLof.Skeleton using (skeleton; related)
import SPT.MartinLof.Structural as Structural
import SPT.MartinLof.Theory as Theory

------------------------------------------------------------------------
-- Contexts

empty-context : Theory.Derivation (context ∅)
empty-context = Tree.node (Theory.structural , Structural.empty) (λ ())

extended-context :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ)
  (A : Raw.Expression Theory.Constant n)
  → Theory.Derivation (type Γ l A)
  → Theory.Derivation (context (Γ ▸[ l ] A))
extended-context Γ l A d =
  Tree.node (Theory.structural , Structural.extend Γ l A)
    (λ { fzero → d ; (fsuc ()) })

------------------------------------------------------------------------
-- Extensional equality and levels

extensional :
  (j j′ : Judgment Theory.Constant) → Judgment-Rel j j′
  → Theory.Derivation j → Theory.Derivation j′
extensional j j′ r d =
  Tree.node (Theory.structural , Structural.extensional j r)
    (λ { fzero → d ; (fsuc ()) })

-- A term judgment with its term and type replaced by related trees.
rewritten :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ)
  (t t′ A A′ : Raw.Expression Theory.Constant n)
  → Relation.TreeRel _＝_ t t′ → Relation.TreeRel _＝_ A A′
  → Theory.Derivation (term Γ l t A) → Theory.Derivation (term Γ l t′ A′)
rewritten Γ l t t′ A A′ rt rA d =
  extensional (term Γ l t A) (term Γ l t′ A′)
    (term-rel (context-refl Γ) rt rA) d

-- A term judgment with its term and type replaced by trees with the same
-- skeletons.
reshaped :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ)
  (t t′ A A′ : Raw.Expression Theory.Constant n)
  → skeleton t ＝ skeleton t′ → skeleton A ＝ skeleton A′
  → Theory.Derivation (term Γ l t A) → Theory.Derivation (term Γ l t′ A′)
reshaped Γ l t t′ A A′ et eA d =
  rewritten Γ l t t′ A A′ (related t t′ et) (related A A′ eA) d

leveled :
  {n : ℕ} (Γ : Context Theory.Constant n) (l l′ : ℕ)
  (t A : Raw.Expression Theory.Constant n)
  → l ＝ l′ → Theory.Derivation (term Γ l t A)
  → Theory.Derivation (term Γ l′ t A)
leveled Γ l l′ t A refl d = d

type-leveled :
  {n : ℕ} (Γ : Context Theory.Constant n) (l l′ : ℕ)
  (A : Raw.Expression Theory.Constant n)
  → l ＝ l′ → Theory.Derivation (type Γ l A)
  → Theory.Derivation (type Γ l′ A)
type-leveled Γ l l′ A refl d = d

------------------------------------------------------------------------
-- Variables

-- Variable i of Γ has level l and a type extensionally equal to T.
record Assumed
  {n : ℕ} (Γ : Context Theory.Constant n) (i : Fin n) (l : ℕ)
  (T : Raw.Expression Theory.Constant n) : Set where
  field
    level-is : level Γ i ＝ l
    type-is : Relation.TreeRel _＝_ (lookup Γ i) T

-- Weakening keeps extensional equality.
weakened :
  {n : ℕ} (s t : Raw.Expression Theory.Constant n)
  → Relation.TreeRel _＝_ s t → Relation.TreeRel _＝_ (weaken s) (weaken t)
weakened s t r = weaken-related s t r

newest-related :
  {n : ℕ} (Γ : Context Theory.Constant n) (k : ℕ)
  (B : Raw.Expression Theory.Constant n)
  (T : Raw.Expression Theory.Constant (suc n))
  → Relation.TreeRel _＝_ (weaken B) T → Assumed (Γ ▸[ k ] B) fzero k T
newest-related Γ k B T r = record { level-is = refl ; type-is = r }

older-related :
  {n : ℕ} (Γ : Context Theory.Constant n) (k : ℕ)
  (B : Raw.Expression Theory.Constant n) (i : Fin n) (l : ℕ)
  (T : Raw.Expression Theory.Constant n)
  (T′ : Raw.Expression Theory.Constant (suc n))
  → Assumed Γ i l T → Relation.TreeRel _＝_ (weaken T) T′
  → Assumed (Γ ▸[ k ] B) (fsuc i) l T′
older-related Γ k B i l T T′ a r =
  record
    { level-is = Assumed.level-is a
    ; type-is =
        Relation.rel-compose _∙_
          (weakened (lookup Γ i) T (Assumed.type-is a)) r
    }

newest :
  {n : ℕ} (Γ : Context Theory.Constant n) (k : ℕ)
  (B : Raw.Expression Theory.Constant n)
  (T : Raw.Expression Theory.Constant (suc n))
  → skeleton (weaken B) ＝ skeleton T → Assumed (Γ ▸[ k ] B) fzero k T
newest Γ k B T e = newest-related Γ k B T (related (weaken B) T e)

older :
  {n : ℕ} (Γ : Context Theory.Constant n) (k : ℕ)
  (B : Raw.Expression Theory.Constant n) (i : Fin n) (l : ℕ)
  (T : Raw.Expression Theory.Constant n)
  (T′ : Raw.Expression Theory.Constant (suc n))
  → Assumed Γ i l T → skeleton (weaken T) ＝ skeleton T′
  → Assumed (Γ ▸[ k ] B) (fsuc i) l T′
older Γ k B i l T T′ a e =
  older-related Γ k B i l T T′ a (related (weaken T) T′ e)

assumed :
  {n : ℕ} (Γ : Context Theory.Constant n) (i : Fin n) (l : ℕ)
  (T : Raw.Expression Theory.Constant n)
  → Theory.Derivation (context Γ) → Assumed Γ i l T
  → Theory.Derivation (term Γ l (Tree.hole i) T)
assumed Γ i l T v a =
  let el = Assumed.level-is a
      rT = Assumed.type-is a
  in leveled Γ (level Γ i) l (Tree.hole i) T el
       (extensional (term Γ (level Γ i) (Tree.hole i) (lookup Γ i))
         (term Γ (level Γ i) (Tree.hole i) T)
         (term-rel (context-refl Γ)
           (Relation.rel-refl (λ x → refl) (Tree.hole i)) rT)
         (Tree.node (Theory.structural , Structural.assumption Γ i)
           (λ { fzero → v ; (fsuc ()) })))

------------------------------------------------------------------------
-- Formation

universe-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ)
  → Theory.Derivation (context Γ)
  → Theory.Derivation (type Γ (suc l) (universe l))
universe-type Γ l v =
  Tree.node (Theory.universe , Universe.formation Γ l)
    (λ { fzero → v ; (fsuc ()) })

lifted-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (m k : ℕ)
  (A : Raw.Expression Theory.Constant n)
  → Theory.Derivation (type Γ m A)
  → Theory.Derivation (type Γ (m ⊔ℕ k) (lifted m k A))
lifted-type Γ m k A dA =
  Tree.node (Theory.lift , Lift.formation Γ m k A)
    (λ { fzero → dA ; (fsuc ()) })

pi-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (m k : ℕ)
  (A : Raw.Expression Theory.Constant n)
  (B : Raw.Expression Theory.Constant (suc n))
  → Theory.Derivation (type Γ m A)
  → Theory.Derivation (type (Γ ▸[ m ] A) k B)
  → Theory.Derivation (type Γ (m ⊔ℕ k) (pi m k A B))
pi-type Γ m k A B dA dB =
  Tree.node (Theory.pi , Pi.formation Γ m k A B)
    (λ { fzero → dA ; (fsuc fzero) → dB
       ; (fsuc (fsuc ())) })

sigma-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (m k : ℕ)
  (A : Raw.Expression Theory.Constant n)
  (B : Raw.Expression Theory.Constant (suc n))
  → Theory.Derivation (type Γ m A)
  → Theory.Derivation (type (Γ ▸[ m ] A) k B)
  → Theory.Derivation (type Γ (m ⊔ℕ k) (sigma m k A B))
sigma-type Γ m k A B dA dB =
  Tree.node (Theory.sigma , Sigma.formation Γ m k A B)
    (λ { fzero → dA ; (fsuc fzero) → dB
       ; (fsuc (fsuc ())) })

tree-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (m k : ℕ)
  (A : Raw.Expression Theory.Constant n)
  (B : Raw.Expression Theory.Constant (suc n))
  → Theory.Derivation (type Γ m A)
  → Theory.Derivation (type (Γ ▸[ m ] A) k B)
  → Theory.Derivation (type Γ (m ⊔ℕ k) (tree m k A B))
tree-type Γ m k A B dA dB =
  Tree.node (Theory.well-founded , WellFounded.formation Γ m k A B)
    (λ { fzero → dA ; (fsuc fzero) → dB
       ; (fsuc (fsuc ())) })

identity-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (m : ℕ)
  (A a b : Raw.Expression Theory.Constant n)
  → Theory.Derivation (type Γ m A) → Theory.Derivation (term Γ m a A)
  → Theory.Derivation (term Γ m b A)
  → Theory.Derivation (type Γ m (identity m A a b))
identity-type Γ m A a b dA da db =
  Tree.node (Theory.identity , Identity.formation Γ m A a b)
    (λ { fzero → dA ; (fsuc fzero) → da
       ; (fsuc (fsuc fzero)) → db
       ; (fsuc (fsuc (fsuc ()))) })

empty-type :
  {n : ℕ} (Γ : Context Theory.Constant n) → Theory.Derivation (context Γ)
  → Theory.Derivation (type Γ 0 empty)
empty-type Γ v =
  Tree.node (Theory.empty , Empty.formation Γ)
    (λ { fzero → v ; (fsuc ()) })

unit-type :
  {n : ℕ} (Γ : Context Theory.Constant n) → Theory.Derivation (context Γ)
  → Theory.Derivation (type Γ 0 unit)
unit-type Γ v =
  Tree.node (Theory.unit , Unit.formation Γ)
    (λ { fzero → v ; (fsuc ()) })

natural-type :
  {n : ℕ} (Γ : Context Theory.Constant n) → Theory.Derivation (context Γ)
  → Theory.Derivation (type Γ 0 natural)
natural-type Γ v =
  Tree.node (Theory.natural , Natural.formation Γ)
    (λ { fzero → v ; (fsuc ()) })

sum-type :
  {n : ℕ} (Γ : Context Theory.Constant n) (m k : ℕ)
  (A B : Raw.Expression Theory.Constant n)
  → Theory.Derivation (type Γ m A) → Theory.Derivation (type Γ k B)
  → Theory.Derivation (type Γ (m ⊔ℕ k) (sum m k A B))
sum-type Γ m k A B dA dB =
  Tree.node (Theory.sum , Sum.formation Γ m k A B)
    (λ { fzero → dA ; (fsuc fzero) → dB
       ; (fsuc (fsuc ())) })

------------------------------------------------------------------------
-- Π

lambda-term :
  {n : ℕ} (Γ : Context Theory.Constant n) (m k : ℕ)
  (A : Raw.Expression Theory.Constant n)
  (B t : Raw.Expression Theory.Constant (suc n))
  → Theory.Derivation (type Γ m A)
  → Theory.Derivation (type (Γ ▸[ m ] A) k B)
  → Theory.Derivation (term (Γ ▸[ m ] A) k t B)
  → Theory.Derivation (term Γ (m ⊔ℕ k) (lambda m k A B t) (pi m k A B))
lambda-term Γ m k A B t dA dB dt =
  Tree.node (Theory.pi , Pi.introduction Γ m k A B t)
    (λ { fzero → dA ; (fsuc fzero) → dB
       ; (fsuc (fsuc fzero)) → dt
       ; (fsuc (fsuc (fsuc ()))) })

application-term :
  {n : ℕ} (Γ : Context Theory.Constant n) (m k : ℕ)
  (A : Raw.Expression Theory.Constant n)
  (B : Raw.Expression Theory.Constant (suc n))
  (f a : Raw.Expression Theory.Constant n)
  → Theory.Derivation (type Γ m A)
  → Theory.Derivation (type (Γ ▸[ m ] A) k B)
  → Theory.Derivation (term Γ (m ⊔ℕ k) f (pi m k A B))
  → Theory.Derivation (term Γ m a A)
  → Theory.Derivation (term Γ k (application m k A B f a) (instantiate B a))
application-term Γ m k A B f a dA dB df da =
  Tree.node (Theory.pi , Pi.elimination Γ m k A B f a)
    (λ { fzero → dA ; (fsuc fzero) → dB
       ; (fsuc (fsuc fzero)) → df
       ; (fsuc (fsuc (fsuc fzero))) → da
       ; (fsuc (fsuc (fsuc (fsuc ())))) })

beta :
  {n : ℕ} (Γ : Context Theory.Constant n) (m k : ℕ)
  (A : Raw.Expression Theory.Constant n)
  (B t : Raw.Expression Theory.Constant (suc n))
  (a : Raw.Expression Theory.Constant n)
  → Theory.Derivation (type Γ m A)
  → Theory.Derivation (type (Γ ▸[ m ] A) k B)
  → Theory.Derivation (term (Γ ▸[ m ] A) k t B)
  → Theory.Derivation (term Γ m a A)
  → Theory.Derivation
      (term-equal Γ k (application m k A B (lambda m k A B t) a)
        (instantiate t a) (instantiate B a))
beta Γ m k A B t a dA dB dt da =
  Tree.node (Theory.pi , Pi.computation Γ m k A B t a)
    (λ { fzero → dA ; (fsuc fzero) → dB
       ; (fsuc (fsuc fzero)) → dt
       ; (fsuc (fsuc (fsuc fzero))) → da
       ; (fsuc (fsuc (fsuc (fsuc ())))) })

application-equal :
  {n : ℕ} (Γ : Context Theory.Constant n) (m k : ℕ)
  (A A′ : Raw.Expression Theory.Constant n)
  (B B′ : Raw.Expression Theory.Constant (suc n))
  (f f′ a a′ : Raw.Expression Theory.Constant n)
  → Theory.Derivation (type-equal Γ m A A′)
  → Theory.Derivation (type-equal (Γ ▸[ m ] A) k B B′)
  → Theory.Derivation (term-equal Γ (m ⊔ℕ k) f f′ (pi m k A B))
  → Theory.Derivation (term-equal Γ m a a′ A)
  → Theory.Derivation
      (term-equal Γ k (application m k A B f a)
        (application m k A′ B′ f′ a′) (instantiate B a))
application-equal Γ m k A A′ B B′ f f′ a a′ dA dB df da =
  Tree.node (Theory.pi , Pi.elimination-equal Γ m k A A′ B B′ f f′ a a′)
    (λ { fzero → dA ; (fsuc fzero) → dB
       ; (fsuc (fsuc fzero)) → df
       ; (fsuc (fsuc (fsuc fzero))) → da
       ; (fsuc (fsuc (fsuc (fsuc ())))) })

------------------------------------------------------------------------
-- Σ

pair-term :
  {n : ℕ} (Γ : Context Theory.Constant n) (m k : ℕ)
  (A : Raw.Expression Theory.Constant n)
  (B : Raw.Expression Theory.Constant (suc n))
  (a b : Raw.Expression Theory.Constant n)
  → Theory.Derivation (type Γ m A)
  → Theory.Derivation (type (Γ ▸[ m ] A) k B)
  → Theory.Derivation (term Γ m a A)
  → Theory.Derivation (term Γ k b (instantiate B a))
  → Theory.Derivation (term Γ (m ⊔ℕ k) (pair m k A B a b) (sigma m k A B))
pair-term Γ m k A B a b dA dB da db =
  Tree.node (Theory.sigma , Sigma.introduction Γ m k A B a b)
    (λ { fzero → dA ; (fsuc fzero) → dB
       ; (fsuc (fsuc fzero)) → da
       ; (fsuc (fsuc (fsuc fzero))) → db
       ; (fsuc (fsuc (fsuc (fsuc ())))) })

first-term :
  {n : ℕ} (Γ : Context Theory.Constant n) (m k : ℕ)
  (A : Raw.Expression Theory.Constant n)
  (B : Raw.Expression Theory.Constant (suc n))
  (p : Raw.Expression Theory.Constant n)
  → Theory.Derivation (type Γ m A)
  → Theory.Derivation (type (Γ ▸[ m ] A) k B)
  → Theory.Derivation (term Γ (m ⊔ℕ k) p (sigma m k A B))
  → Theory.Derivation (term Γ m (first m k A B p) A)
first-term Γ m k A B p dA dB dp =
  Tree.node (Theory.sigma , Sigma.first-projection Γ m k A B p)
    (λ { fzero → dA ; (fsuc fzero) → dB
       ; (fsuc (fsuc fzero)) → dp
       ; (fsuc (fsuc (fsuc ()))) })

second-term :
  {n : ℕ} (Γ : Context Theory.Constant n) (m k : ℕ)
  (A : Raw.Expression Theory.Constant n)
  (B : Raw.Expression Theory.Constant (suc n))
  (p : Raw.Expression Theory.Constant n)
  → Theory.Derivation (type Γ m A)
  → Theory.Derivation (type (Γ ▸[ m ] A) k B)
  → Theory.Derivation (term Γ (m ⊔ℕ k) p (sigma m k A B))
  → Theory.Derivation
      (term Γ k (second m k A B p) (instantiate B (first m k A B p)))
second-term Γ m k A B p dA dB dp =
  Tree.node (Theory.sigma , Sigma.second-projection Γ m k A B p)
    (λ { fzero → dA ; (fsuc fzero) → dB
       ; (fsuc (fsuc fzero)) → dp
       ; (fsuc (fsuc (fsuc ()))) })

------------------------------------------------------------------------
-- Identity types

reflexivity-term :
  {n : ℕ} (Γ : Context Theory.Constant n) (m : ℕ)
  (A a : Raw.Expression Theory.Constant n)
  → Theory.Derivation (type Γ m A) → Theory.Derivation (term Γ m a A)
  → Theory.Derivation (term Γ m (reflexivity m A a) (identity m A a a))
reflexivity-term Γ m A a dA da =
  Tree.node (Theory.identity , Identity.introduction Γ m A a)
    (λ { fzero → dA ; (fsuc fzero) → da
       ; (fsuc (fsuc ())) })

path-induction-term :
  {n : ℕ} (Γ : Context Theory.Constant n) (m k : ℕ)
  (A : Raw.Expression Theory.Constant n)
  (M : Raw.Expression Theory.Constant (suc (suc n)))
  (a d b p : Raw.Expression Theory.Constant n)
  → Theory.Derivation (type Γ m A) → Theory.Derivation (term Γ m a A)
  → Theory.Derivation (type (Identity.paths Γ m A a) k M)
  → Theory.Derivation (term Γ k d (instantiate₂ M a (reflexivity m A a)))
  → Theory.Derivation (term Γ m b A)
  → Theory.Derivation (term Γ m p (identity m A a b))
  → Theory.Derivation
      (term Γ k (path-induction m k A M a d b p) (instantiate₂ M b p))
path-induction-term Γ m k A M a d b p dA da dM dd db dp =
  Tree.node (Theory.identity , Identity.elimination Γ m k A M a d b p)
    (λ { fzero → dA ; (fsuc fzero) → da
       ; (fsuc (fsuc fzero)) → dM
       ; (fsuc (fsuc (fsuc fzero))) → dd
       ; (fsuc (fsuc (fsuc (fsuc fzero)))) → db
       ; (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) → dp
       ; (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))) })

identity-equal :
  {n : ℕ} (Γ : Context Theory.Constant n) (m : ℕ)
  (A A′ a a′ b b′ : Raw.Expression Theory.Constant n)
  → Theory.Derivation (type-equal Γ m A A′)
  → Theory.Derivation (term-equal Γ m a a′ A)
  → Theory.Derivation (term-equal Γ m b b′ A)
  → Theory.Derivation
      (type-equal Γ m (identity m A a b) (identity m A′ a′ b′))
identity-equal Γ m A A′ a a′ b b′ dA da db =
  Tree.node
    (Theory.identity , Identity.formation-equal Γ m A A′ a a′ b b′)
    (λ { fzero → dA ; (fsuc fzero) → da
       ; (fsuc (fsuc fzero)) → db
       ; (fsuc (fsuc (fsuc ()))) })

------------------------------------------------------------------------
-- Equality and conversion

reflexive :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ)
  (t A : Raw.Expression Theory.Constant n)
  → Theory.Derivation (term Γ l t A)
  → Theory.Derivation (term-equal Γ l t t A)
reflexive Γ l t A dt =
  Tree.node (Theory.structural , Structural.reflexive Γ l t A)
    (λ { fzero → dt ; (fsuc ()) })

symmetric :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ)
  (t u A : Raw.Expression Theory.Constant n)
  → Theory.Derivation (term-equal Γ l t u A)
  → Theory.Derivation (term-equal Γ l u t A)
symmetric Γ l t u A d =
  Tree.node (Theory.structural , Structural.symmetric Γ l t u A)
    (λ { fzero → d ; (fsuc ()) })

transitive :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ)
  (t u v A : Raw.Expression Theory.Constant n)
  → Theory.Derivation (term-equal Γ l t u A)
  → Theory.Derivation (term-equal Γ l u v A)
  → Theory.Derivation (term-equal Γ l t v A)
transitive Γ l t u v A d e =
  Tree.node (Theory.structural , Structural.transitive Γ l t u v A)
    (λ { fzero → d ; (fsuc fzero) → e ; (fsuc (fsuc ())) })

conversion :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ)
  (t A B : Raw.Expression Theory.Constant n)
  → Theory.Derivation (term Γ l t A)
  → Theory.Derivation (type-equal Γ l A B)
  → Theory.Derivation (term Γ l t B)
conversion Γ l t A B dt dAB =
  Tree.node (Theory.structural , Structural.conversion Γ l t A B)
    (λ { fzero → dt ; (fsuc fzero) → dAB
       ; (fsuc (fsuc ())) })

-- An equation of terms with its sides and type replaced by trees with
-- the same skeletons.
equal-reshaped :
  {n : ℕ} (Γ : Context Theory.Constant n) (l : ℕ)
  (t t′ u u′ A A′ : Raw.Expression Theory.Constant n)
  → skeleton t ＝ skeleton t′ → skeleton u ＝ skeleton u′
  → skeleton A ＝ skeleton A′
  → Theory.Derivation (term-equal Γ l t u A)
  → Theory.Derivation (term-equal Γ l t′ u′ A′)
equal-reshaped Γ l t t′ u u′ A A′ et eu eA d =
  extensional (term-equal Γ l t u A) (term-equal Γ l t′ u′ A′)
    (term-equal-rel (context-refl Γ) (related t t′ et)
      (related u u′ eu) (related A A′ eA))
    d
