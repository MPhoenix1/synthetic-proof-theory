{-# OPTIONS --safe --without-K --no-projection-like #-}

module SPT.MartinLof.Soundness.Transport where

-- Values of raw expressions under changes of their environment.
--
-- A transformation sends the environments of the children of one node to
-- those of another, at every number of extra bound variables, where it is
-- good, and commutes with extension (`Transformation`). If the children of
-- two nodes of the same former agree up to it, so do the nodes
-- (`node-transport`, one clause per former; `bind₁`, `bind₂`, `bind₃` for
-- children under one, two or three binders). This is the only induction
-- over formers. Each lemma below is a theorem of folds at the
-- relation a transformation gives, with `node-transport` as its node case:
-- - trees related by TreeRel _＝_ have equal values (`meaning-rel`,
--   by `fold-rel` of Tree.Fold.Relation at `identity-related`), and every
--   homomorphic valuation agrees with the interpretation (`meaning-unique`,
--   by `fold-unique-rel` of Tree.Fold.Initiality);
-- - a tree moved by e depths by lax translation, with a hole map
--   commuting with extension, has the value of the tree at the reindexed
--   environment (`shift-meaning`, `reindex`, by `lax-tree-fold-natural`
--   of Tree.Fold.Relation.Heterogeneous.LaxTranslation at
--   `shift-algebra`);
--   so do Binding's `bound` and `under` (`bound-meaning`, `under-meaning`);
-- - a substituted tree has the value of the tree at the environment of
--   the values of what is substituted, when those are stable
--   (`substitution-meaning`, `σ-env`, `substitute-meaning`, by
--   `bind-fold-rel` of Tree.Fold.Substitution at `Substituted`).

open import SPT.Base hiding (Lift; _∘_; id; lift; lower; zero)
import SPT.Base.Universes as Universes
open import SPT.Foundation.Vectors.Tabulation using
  (lookup-tabulate; tabulate; tabulate-cong; tabulate-lookup; tabulate-∘)
import SPT.Foundation.Tree.Fold.Relation.Heterogeneous as Heterogeneous
import SPT.Foundation.Tree.Fold.Relation.Heterogeneous.LaxTranslation as LaxFold
import SPT.Foundation.Tree.Fold.Relation as Relational
import SPT.Foundation.Tree.Fold.Substitution as RelationalSubstitution
import SPT.Foundation.Signature.Sum as Sig
import SPT.Foundation.Tree as Tree
import SPT.Foundation.Tree.Fold as Fold
import SPT.Foundation.Tree.Fold.Initiality as Initiality
import SPT.Foundation.Tree.LaxTranslation as LaxTree
import SPT.Foundation.Tree.Relation as Relation
import SPT.Foundation.Tree.Substitution as Substitution
import SPT.Foundation.Tree.Binding as Binding
import SPT.Foundation.Tree.Binding.Shift as Shift
import SPT.MartinLof.Raw as Raw
open import SPT.MartinLof.Model.Empty using (Empty)
open import SPT.MartinLof.Model.Identity using (Identity)
open import SPT.MartinLof.Model.Lift using (Lift)
open import SPT.MartinLof.Model.Natural using (Natural)
open import SPT.MartinLof.Model.Subuniverse using
  (Operations; Subuniverse)
open import SPT.MartinLof.Model.Pi using (Pi)
open import SPT.MartinLof.Model.Russell using (Russell)
open import SPT.MartinLof.Model.Sigma using (Sigma)
open import SPT.MartinLof.Model.Sum using (Sum)
open import SPT.MartinLof.Model.Unit using (Unit)
open import SPT.MartinLof.Model.WellFounded using
  (WellFounded; children-type; hypotheses-type)
import SPT.MartinLof.Soundness.Environment as Environment
import SPT.MartinLof.Soundness.Interpretation as Interpretation

------------------------------------------------------------------------
-- Equalities and the arithmetic of moving variables

ap₃ :
  {a b c d : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
  (f : A → B → C → D) {x x′ : A} {y y′ : B} {z z′ : C}
  → x ＝ x′ → y ＝ y′ → z ＝ z′ → f x y z ＝ f x′ y′ z′
ap₃ f refl refl refl = refl

ap₄ :
  {a b c d e : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
  {E : Set e} (f : A → B → C → D → E) {x x′ : A} {y y′ : B} {z z′ : C}
  {u u′ : D}
  → x ＝ x′ → y ＝ y′ → z ＝ z′ → u ＝ u′ → f x y z u ＝ f x′ y′ z′ u′
ap₄ f refl refl refl refl = refl

ap₅ :
  {a : Level} {A : Set a} (f : A → A → A → A → A → A)
  {x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ x₅ y₅ : A}
  → x₁ ＝ y₁ → x₂ ＝ y₂ → x₃ ＝ y₃ → x₄ ＝ y₄ → x₅ ＝ y₅
  → f x₁ x₂ x₃ x₄ x₅ ＝ f y₁ y₂ y₃ y₄ y₅
ap₅ f refl refl refl refl refl = refl

ap₆ :
  {a : Level} {A : Set a} (f : A → A → A → A → A → A → A)
  {x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ x₅ y₅ x₆ y₆ : A}
  → x₁ ＝ y₁ → x₂ ＝ y₂ → x₃ ＝ y₃ → x₄ ＝ y₄ → x₅ ＝ y₅ → x₆ ＝ y₆
  → f x₁ x₂ x₃ x₄ x₅ x₆ ＝ f y₁ y₂ y₃ y₄ y₅ y₆
ap₆ f refl refl refl refl refl refl = refl

ap₇ :
  {a : Level} {A : Set a} (f : A → A → A → A → A → A → A → A)
  {x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ x₅ y₅ x₆ y₆ x₇ y₇ : A}
  → x₁ ＝ y₁ → x₂ ＝ y₂ → x₃ ＝ y₃ → x₄ ＝ y₄ → x₅ ＝ y₅ → x₆ ＝ y₆ → x₇ ＝ y₇
  → f x₁ x₂ x₃ x₄ x₅ x₆ x₇ ＝ f y₁ y₂ y₃ y₄ y₅ y₆ y₇
ap₇ f refl refl refl refl refl refl refl = refl

ap₈ :
  {a : Level} {A : Set a} (f : A → A → A → A → A → A → A → A → A)
  {x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ x₅ y₅ x₆ y₆ x₇ y₇ x₈ y₈ : A}
  → x₁ ＝ y₁ → x₂ ＝ y₂ → x₃ ＝ y₃ → x₄ ＝ y₄ → x₅ ＝ y₅ → x₆ ＝ y₆ → x₇ ＝ y₇
  → x₈ ＝ y₈ → f x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ ＝ f y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈
ap₈ f refl refl refl refl refl refl refl refl = refl

-- A successor path transported at zero and at a successor.
transport-zero :
  {i j : ℕ} (eq : i ＝ j) → transport Fin (ap suc eq ⁻¹) fzero ＝ fzero
transport-zero refl = refl

transport-suc :
  {i j : ℕ} (eq : i ＝ j) (x : Fin j)
  → transport Fin (ap suc eq ⁻¹) (fsuc x) ＝ fsuc (transport Fin (eq ⁻¹) x)
transport-suc refl x = refl

-- Moving a number under d binders, one bound variable deeper.
shifted-suc-cases :
  (c d n : ℕ) → (n <ℕˢ c) ⊎ (c ≤ℕˢ n)
  → Shift.shifted (suc c) d (suc n) ＝ suc (Shift.shifted c d n)
shifted-suc-cases c d n (inl below) =
  Shift.shifted-below d (s≤s below) ∙
    ap suc (Shift.shifted-below d below ⁻¹)
shifted-suc-cases c d n (inr above) =
  Shift.shifted-above d (s≤s above) ∙
    (+-suc-right d n ∙ ap suc (Shift.shifted-above d above ⁻¹))

shifted-suc :
  (c d n : ℕ) → Shift.shifted (suc c) d (suc n) ＝ suc (Shift.shifted c d n)
shifted-suc c d n = shifted-suc-cases c d n (Shift.decide n c)

-- Shift's shifted-below, with the bound explicit.
shifted-below :
  (c n d : ℕ) → n <ℕˢ c → Shift.shifted c d n ＝ n
shifted-below c n d below = Shift.shifted-below d below

------------------------------------------------------------------------
-- In a model

module _ {ℓ : Level} {C : Set}
  (R : Russell ℓ) (let open Russell R)
  (lifting : Lift R) (let open Lift lifting)
  (products : Pi R) (let open Pi products)
  (pairs : Sigma R) (let open Sigma pairs)
  (paths : Identity R) (let open Identity paths)
  (trees : WellFounded R products) (let open WellFounded trees)
  (nothing : Empty R) (let open Empty nothing)
  (one : Unit R) (let open Unit one)
  (sums : Sum R) (let open Sum sums)
  (numbers : Natural R) (let open Natural numbers)
  (operations : Operations R) (let open Operations operations)
  (subuniverses : Subuniverse R products operations)
  (let open Subuniverse subuniverses)
  (constant : C → Tm ◇)
  (let ext = Environment.ext R)
  (let outer = Environment.outer R)
  (let Stable = Environment.Stable R)
  (let node = Interpretation.node R lifting products pairs paths trees
                nothing one sums numbers operations subuniverses constant)
  (let meaning = Interpretation.⟦_⟧ R lifting products pairs paths trees
                   nothing one sums numbers operations subuniverses constant)
  (let algebra = Interpretation.algebra R lifting products pairs paths
                   trees nothing one sums numbers operations subuniverses
                     constant)
  where

  ----------------------------------------------------------------------
  -- Transformations of environments

  -- For nodes at depths d and d′ in scopes n and n′: environments of k
  -- more bound variables, where good, sent to environments of k more.
  record Transformation (n n′ d d′ : ℕ) : Set (lsuc ℓ) where
    field
      Good : {X : Ob} (k : ℕ) → Vec (Tm X) ((k + d) + n) → Set ℓ
      transform :
        {X : Ob} (k : ℕ) → Vec (Tm X) ((k + d) + n)
        → Vec (Tm X) ((k + d′) + n′)
      good-ext :
        {X : Ob} (a : Tm X) (k : ℕ) (env : Vec (Tm X) ((k + d) + n))
        → Good k env → Good (suc k) (ext a env)
      transform-ext :
        {X : Ob} (a : Tm X) (k : ℕ) (env : Vec (Tm X) ((k + d) + n))
        → Good k env → transform (suc k) (ext a env) ＝ ext a (transform k env)

  module _ (n n′ d d′ : ℕ) (tr : Transformation n n′ d d′)
    (let open Transformation tr) where

    -- A child under one binder, two, three.
    bind₁ :
      (vP : (X : Ob) → Vec (Tm X) ((1 + d) + n) → Tm X)
      (wP : (X : Ob) → Vec (Tm X) ((1 + d′) + n′) → Tm X)
      → ((X : Ob) (env : Vec (Tm X) ((1 + d) + n)) → Good 1 env
         → vP X env ＝ wP X (transform 1 env))
      → {X : Ob} (a : Tm X) (env : Vec (Tm X) (d + n)) → Good 0 env
      → vP (X ▸ a) (ext a env) ＝ wP (X ▸ a) (ext a (transform 0 env))
    bind₁ vP wP hP {X} a env g =
      hP (X ▸ a) (ext a env) (good-ext a 0 env g) ∙
        ap (wP (X ▸ a)) (transform-ext a 0 env g)

    bind₂ :
      (vP : (X : Ob) → Vec (Tm X) ((2 + d) + n) → Tm X)
      (wP : (X : Ob) → Vec (Tm X) ((2 + d′) + n′) → Tm X)
      → ((X : Ob) (env : Vec (Tm X) ((2 + d) + n)) → Good 2 env
         → vP X env ＝ wP X (transform 2 env))
      → {X : Ob} (a : Tm X) (b : Tm (X ▸ a)) (env : Vec (Tm X) (d + n))
      → Good 0 env
      → vP (X ▸ a ▸ b) (ext b (ext a env))
        ＝ wP (X ▸ a ▸ b) (ext b (ext a (transform 0 env)))
    bind₂ vP wP hP {X} a b env g =
      let g₁ = good-ext a 0 env g
      in hP (X ▸ a ▸ b) (ext b (ext a env)) (good-ext b 1 (ext a env) g₁) ∙
           ap (wP (X ▸ a ▸ b))
             (transform-ext b 1 (ext a env) g₁ ∙
               ap (ext b) (transform-ext a 0 env g))

    bind₃ :
      (vP : (X : Ob) → Vec (Tm X) ((3 + d) + n) → Tm X)
      (wP : (X : Ob) → Vec (Tm X) ((3 + d′) + n′) → Tm X)
      → ((X : Ob) (env : Vec (Tm X) ((3 + d) + n)) → Good 3 env
         → vP X env ＝ wP X (transform 3 env))
      → {X : Ob} (a : Tm X) (b : Tm (X ▸ a)) (c : Tm (X ▸ a ▸ b))
      (env : Vec (Tm X) (d + n)) → Good 0 env
      → vP (X ▸ a ▸ b ▸ c) (ext c (ext b (ext a env)))
        ＝ wP (X ▸ a ▸ b ▸ c) (ext c (ext b (ext a (transform 0 env))))
    bind₃ vP wP hP {X} a b c env g =
      let g₁ = good-ext a 0 env g
          g₂ = good-ext b 1 (ext a env) g₁
      in hP (X ▸ a ▸ b ▸ c) (ext c (ext b (ext a env)))
             (good-ext c 2 (ext b (ext a env)) g₂) ∙
           ap (wP (X ▸ a ▸ b ▸ c))
             (transform-ext c 2 (ext b (ext a env)) g₂ ∙
               ap (ext c)
                 (transform-ext b 1 (ext a env) g₁ ∙
                   ap (ext b) (transform-ext a 0 env g)))

    -- Nodes whose children agree up to the transformation agree.
    node-transport :
      (o : Raw.Former C)
      (v : (p : Raw.Premise o) (X : Ob)
           → Vec (Tm X) ((Raw.depth o p + d) + n) → Tm X)
      (w : (p : Raw.Premise o) (X : Ob)
           → Vec (Tm X) ((Raw.depth o p + d′) + n′) → Tm X)
      → ((p : Raw.Premise o) (X : Ob)
         (env : Vec (Tm X) ((Raw.depth o p + d) + n))
         → Good (Raw.depth o p) env
         → v p X env ＝ w p X (transform (Raw.depth o p) env))
      → (X : Ob) (env : Vec (Tm X) (d + n)) → Good 0 env
      → node n d o v X env ＝ node n′ d′ o w X (transform 0 env)
    node-transport (Raw.universe l) v w h X env g = refl
    node-transport (Raw.lifted m k) v w h X env g =
      ap (lifted m k) (h Raw.lifted-type X env g)
    node-transport (Raw.lift m k) v w h X env g =
      ap₂ (lift m k) (h Raw.lift-type X env g) (h Raw.lift-term X env g)
    node-transport (Raw.lower m k) v w h X env g =
      ap₂ (lower m k) (h Raw.lower-type X env g) (h Raw.lower-term X env g)
    node-transport (Raw.pi m k) v w h X env g =
      let a = v Raw.pi-domain X env
          T = transform 0 env
      in ap (pi m k a)
             (bind₁ (v Raw.pi-codomain) (w Raw.pi-codomain)
               (h Raw.pi-codomain) a env g) ∙
           ap (λ x → pi m k x (w Raw.pi-codomain (X ▸ x) (ext x T)))
             (h Raw.pi-domain X env g)
    node-transport (Raw.lambda m k) v w h X env g =
      let a = v Raw.lambda-domain X env
          T = transform 0 env
      in ap₂ (lambda m k a)
             (bind₁ (v Raw.lambda-codomain) (w Raw.lambda-codomain)
               (h Raw.lambda-codomain) a env g)
             (bind₁ (v Raw.lambda-body) (w Raw.lambda-body)
               (h Raw.lambda-body) a env g) ∙
           ap
             (λ x → lambda m k x (w Raw.lambda-codomain (X ▸ x) (ext x T))
                      (w Raw.lambda-body (X ▸ x) (ext x T)))
             (h Raw.lambda-domain X env g)
    node-transport (Raw.application m k) v w h X env g =
      let a = v Raw.application-domain X env
          T = transform 0 env
      in ap₃ (application m k a)
             (bind₁ (v Raw.application-codomain) (w Raw.application-codomain)
               (h Raw.application-codomain) a env g)
             (h Raw.application-function X env g)
             (h Raw.application-argument X env g) ∙
           ap
             (λ x → application m k x
                      (w Raw.application-codomain (X ▸ x) (ext x T))
                      (w Raw.application-function X T)
                      (w Raw.application-argument X T))
             (h Raw.application-domain X env g)
    node-transport (Raw.sigma m k) v w h X env g =
      let a = v Raw.sigma-first X env
          T = transform 0 env
      in ap (sigma m k a)
             (bind₁ (v Raw.sigma-second) (w Raw.sigma-second)
               (h Raw.sigma-second) a env g) ∙
           ap (λ x → sigma m k x (w Raw.sigma-second (X ▸ x) (ext x T)))
             (h Raw.sigma-first X env g)
    node-transport (Raw.pair m k) v w h X env g =
      let a = v Raw.pair-first-type X env
          T = transform 0 env
      in ap₃ (pair m k a)
             (bind₁ (v Raw.pair-second-type) (w Raw.pair-second-type)
               (h Raw.pair-second-type) a env g)
             (h Raw.pair-first X env g) (h Raw.pair-second X env g) ∙
           ap
             (λ x → pair m k x (w Raw.pair-second-type (X ▸ x) (ext x T))
                      (w Raw.pair-first X T) (w Raw.pair-second X T))
             (h Raw.pair-first-type X env g)
    node-transport (Raw.first m k) v w h X env g =
      let a = v Raw.first-first-type X env
          T = transform 0 env
      in ap₂ (first m k a)
             (bind₁ (v Raw.first-second-type) (w Raw.first-second-type)
               (h Raw.first-second-type) a env g)
             (h Raw.first-pair X env g) ∙
           ap
             (λ x → first m k x (w Raw.first-second-type (X ▸ x) (ext x T))
                      (w Raw.first-pair X T))
             (h Raw.first-first-type X env g)
    node-transport (Raw.second m k) v w h X env g =
      let a = v Raw.second-first-type X env
          T = transform 0 env
      in ap₂ (second m k a)
             (bind₁ (v Raw.second-second-type) (w Raw.second-second-type)
               (h Raw.second-second-type) a env g)
             (h Raw.second-pair X env g) ∙
           ap
             (λ x → second m k x (w Raw.second-second-type (X ▸ x) (ext x T))
                      (w Raw.second-pair X T))
             (h Raw.second-first-type X env g)
    node-transport (Raw.identity m) v w h X env g =
      ap₃ (identity m) (h Raw.identity-type X env g)
        (h Raw.identity-left X env g) (h Raw.identity-right X env g)
    node-transport (Raw.reflexivity m) v w h X env g =
      ap₂ (reflexivity m) (h Raw.reflexivity-type X env g)
        (h Raw.reflexivity-point X env g)
    node-transport (Raw.path-induction m k) v w h X env g =
      let a = v Raw.induction-type X env
          x = v Raw.induction-base X env
          I = identity m (a [ p ]) (x [ p ]) (q a)
          T = transform 0 env
      in ap
             (λ M → path-induction m k a x M (v Raw.induction-method X env)
                      (v Raw.induction-end X env) (v Raw.induction-path X env))
             (bind₂ (v Raw.induction-motive) (w Raw.induction-motive)
               (h Raw.induction-motive) a I env g) ∙
           (ap₃
               (path-induction m k a x
                 (w Raw.induction-motive (X ▸ a ▸ I) (ext I (ext a T))))
               (h Raw.induction-method X env g) (h Raw.induction-end X env g)
               (h Raw.induction-path X env g) ∙
             ap₂
               (λ a′ x′ →
                  let I′ = identity m (a′ [ p ]) (x′ [ p ]) (q a′)
                  in path-induction m k a′ x′
                       (w Raw.induction-motive (X ▸ a′ ▸ I′)
                         (ext I′ (ext a′ T)))
                       (w Raw.induction-method X T) (w Raw.induction-end X T)
                       (w Raw.induction-path X T))
               (h Raw.induction-type X env g) (h Raw.induction-base X env g))
    node-transport (Raw.tree m k) v w h X env g =
      let a = v Raw.tree-shape X env
          T = transform 0 env
      in ap (tree m k a)
             (bind₁ (v Raw.tree-position) (w Raw.tree-position)
               (h Raw.tree-position) a env g) ∙
           ap (λ x → tree m k x (w Raw.tree-position (X ▸ x) (ext x T)))
             (h Raw.tree-shape X env g)
    node-transport (Raw.supremum m k) v w h X env g =
      let a = v Raw.supremum-shape-type X env
          T = transform 0 env
      in ap₃ (supremum m k a)
             (bind₁ (v Raw.supremum-position-type)
               (w Raw.supremum-position-type)
               (h Raw.supremum-position-type) a env g)
             (h Raw.supremum-shape X env g)
             (h Raw.supremum-children X env g) ∙
           ap
             (λ x → supremum m k x
                      (w Raw.supremum-position-type (X ▸ x) (ext x T))
                      (w Raw.supremum-shape X T)
                      (w Raw.supremum-children X T))
             (h Raw.supremum-shape-type X env g)
    node-transport (Raw.tree-induction m k l) v w h X env g =
      let a = v Raw.recursion-shape-type X env
          b = v Raw.recursion-position-type (X ▸ a) (ext a env)
          W = tree m k a b
          M = v Raw.recursion-motive (X ▸ W) (ext W env)
          F = children-type R products m k a b W
          H = hypotheses-type R products m k l a b W M
          T = transform 0 env
      in ap₂ (λ c t → tree-induction m k l a b M c [ id ⨾ t ])
             (bind₃ (v Raw.recursion-method) (w Raw.recursion-method)
               (h Raw.recursion-method) a F H env g)
             (h Raw.recursion-tree X env g) ∙
           (ap
               (λ M′ →
                  let H′ = hypotheses-type R products m k l a b W M′
                  in tree-induction m k l a b M′
                       (w Raw.recursion-method (X ▸ a ▸ F ▸ H′)
                         (ext H′ (ext F (ext a T))))
                       [ id ⨾ w Raw.recursion-tree X T ])
               (bind₁ (v Raw.recursion-motive) (w Raw.recursion-motive)
                 (h Raw.recursion-motive) W env g) ∙
             (ap
                 (λ b′ →
                    let W′ = tree m k a b′
                        M′ = w Raw.recursion-motive (X ▸ W′) (ext W′ T)
                        F′ = children-type R products m k a b′ W′
                        H′ = hypotheses-type R products m k l a b′ W′ M′
                    in tree-induction m k l a b′ M′
                         (w Raw.recursion-method (X ▸ a ▸ F′ ▸ H′)
                           (ext H′ (ext F′ (ext a T))))
                         [ id ⨾ w Raw.recursion-tree X T ])
                 (bind₁ (v Raw.recursion-position-type)
                   (w Raw.recursion-position-type)
                   (h Raw.recursion-position-type) a env g) ∙
               ap
                 (λ a′ →
                    let b′ = w Raw.recursion-position-type (X ▸ a′) (ext a′ T)
                        W′ = tree m k a′ b′
                        M′ = w Raw.recursion-motive (X ▸ W′) (ext W′ T)
                        F′ = children-type R products m k a′ b′ W′
                        H′ = hypotheses-type R products m k l a′ b′ W′ M′
                    in tree-induction m k l a′ b′ M′
                         (w Raw.recursion-method (X ▸ a′ ▸ F′ ▸ H′)
                           (ext H′ (ext F′ (ext a′ T))))
                         [ id ⨾ w Raw.recursion-tree X T ])
                 (h Raw.recursion-shape-type X env g)))
    node-transport Raw.empty v w h X env g = refl
    node-transport (Raw.absurd k) v w h X env g =
      ap₂ (absurd k)
        (bind₁ (v Raw.absurd-motive) (w Raw.absurd-motive) (h Raw.absurd-motive)
          (empty [ ε X ]) env g)
        (h Raw.absurd-term X env g)
    node-transport Raw.unit v w h X env g = refl
    node-transport Raw.star v w h X env g = refl
    node-transport (Raw.sum m k) v w h X env g =
      ap₂ (sum m k) (h Raw.sum-left X env g) (h Raw.sum-right X env g)
    node-transport (Raw.left m k) v w h X env g =
      ap₃ (left m k) (h Raw.left-left-type X env g)
        (h Raw.left-right-type X env g) (h Raw.left-term X env g)
    node-transport (Raw.right m k) v w h X env g =
      ap₃ (right m k) (h Raw.right-left-type X env g)
        (h Raw.right-right-type X env g) (h Raw.right-term X env g)
    node-transport (Raw.case m k l) v w h X env g =
      let a = v Raw.case-left-type X env
          b = v Raw.case-right-type X env
          s = sum m k a b
          T = transform 0 env
      in ap₃ (λ M c d → case m k l a b M c d (v Raw.case-term X env))
             (bind₁ (v Raw.case-motive) (w Raw.case-motive) (h Raw.case-motive)
               s env g)
             (bind₁ (v Raw.case-left-method) (w Raw.case-left-method)
               (h Raw.case-left-method) a env g)
             (bind₁ (v Raw.case-right-method) (w Raw.case-right-method)
               (h Raw.case-right-method) b env g) ∙
           (ap
               (case m k l a b (w Raw.case-motive (X ▸ s) (ext s T))
                 (w Raw.case-left-method (X ▸ a) (ext a T))
                 (w Raw.case-right-method (X ▸ b) (ext b T)))
               (h Raw.case-term X env g) ∙
             ap₂
               (λ a′ b′ →
                  let s′ = sum m k a′ b′
                  in case m k l a′ b′ (w Raw.case-motive (X ▸ s′) (ext s′ T))
                       (w Raw.case-left-method (X ▸ a′) (ext a′ T))
                       (w Raw.case-right-method (X ▸ b′) (ext b′ T))
                       (w Raw.case-term X T))
               (h Raw.case-left-type X env g) (h Raw.case-right-type X env g))
    node-transport Raw.natural v w h X env g = refl
    node-transport Raw.zero v w h X env g = refl
    node-transport Raw.successor v w h X env g =
      ap successor (h Raw.successor-term X env g)
    node-transport (Raw.natural-induction l) v w h X env g =
      let N = natural [ ε X ]
          M = v Raw.natural-motive (X ▸ N) (ext N env)
          T = transform 0 env
      in ap₃ (λ z s t → natural-induction l M z s t)
             (h Raw.natural-base X env g)
             (bind₂ (v Raw.natural-step) (w Raw.natural-step)
               (h Raw.natural-step) N M env g)
             (h Raw.natural-term X env g) ∙
           ap
             (λ M′ → natural-induction l M′ (w Raw.natural-base X T)
                       (w Raw.natural-step (X ▸ N ▸ M′) (ext M′ (ext N T)))
                       (w Raw.natural-term X T))
             (bind₁ (v Raw.natural-motive) (w Raw.natural-motive)
               (h Raw.natural-motive) N env g)
    node-transport (Raw.constant c) v w h X env g = refl
    node-transport (Raw.subuniverse i) v w h X env g =
      ap₄ (subuniverse i)
        (h Raw.subuniverse-base X env g)
        (h Raw.subuniverse-base-decoding X env g)
        (h Raw.subuniverse-step X env g)
        (h Raw.subuniverse-step-decoding X env g)
    node-transport (Raw.inclusion i) v w h X env g =
      ap₅ (inclusion i)
        (h Raw.inclusion-base X env g) (h Raw.inclusion-base-decoding X env g)
        (h Raw.inclusion-step X env g) (h Raw.inclusion-step-decoding X env g)
        (h Raw.inclusion-point X env g)
    node-transport (Raw.closure i) v w h X env g =
      ap₇ (closure i)
        (h Raw.closure-base X env g) (h Raw.closure-base-decoding X env g)
        (h Raw.closure-step X env g) (h Raw.closure-step-decoding X env g)
        (h Raw.closure-code X env g) (h Raw.closure-family X env g)
        (h Raw.closure-point X env g)
    node-transport (Raw.decoding i) v w h X env g =
      ap₅ (decoding i)
        (h Raw.decoding-base X env g) (h Raw.decoding-base-decoding X env g)
        (h Raw.decoding-step X env g) (h Raw.decoding-step-decoding X env g)
        (h Raw.decoding-code X env g)
    node-transport (Raw.subuniverse-induction i j) v w h X env g =
      ap₈ (induction i j)
        (h Raw.subinduction-base X env g)
        (h Raw.subinduction-base-decoding X env g)
        (h Raw.subinduction-step X env g)
        (h Raw.subinduction-step-decoding X env g)
        (h Raw.subinduction-motive X env g)
        (h Raw.subinduction-inclusion X env g)
        (h Raw.subinduction-closure X env g) (h Raw.subinduction-code X env g)

  ----------------------------------------------------------------------
  -- Trees related by TreeRel _＝_

  identity-transformation : (n d : ℕ) → Transformation n n d d
  identity-transformation n d = record
    { Good = λ k env → Universes.Lift ℓ 𝟙
    ; transform = λ k env → env
    ; good-ext = λ a k env g → Universes.lift ⋆
    ; transform-ext = λ a k env g → refl
    }

  -- Values equal at every model context and environment.
  Pointwise :
    (n : ℕ) {d : ℕ}
    → ((X : Ob) → Vec (Tm X) (d + n) → Tm X)
    → ((X : Ob) → Vec (Tm X) (d + n) → Tm X) → Set ℓ
  Pointwise n {d} v w = (X : Ob) (env : Vec (Tm X) (d + n)) → v X env ＝ w X env

  -- The interpretation's algebra preserves pointwise equality: equal
  -- variables are looked up alike, and nodes by `node-transport` at the
  -- identity transformation.
  identity-related :
    (n : ℕ)
    → Relational.Relational-Algebra _＝_ (Pointwise n) (algebra n) (algebra n)
  identity-related n = record
    { on-hole-rel = λ {d} {x} {y} eq X env → ap (vector-lookup env) eq
    ; on-node-rel = λ {d} o {v} {w} h X env →
        node-transport n n d d (identity-transformation n d) o v w
          (λ p X′ env′ g → h p X′ env′) X env (Universes.lift ⋆)
    }

  meaning-rel :
    {n d : ℕ}
      {t u : Tree.Tree (Sig.to-signature (Binding.over (Raw.binding C)))
        (Binding.Variable n) d}
    → Relation.TreeRel _＝_ t u
    → (X : Ob) (env : Vec (Tm X) (d + n)) → meaning t X env ＝ meaning u X env
  meaning-rel {n} r = Relational.fold-rel (identity-related n) r

  -- Every valuation with the hole and node laws of the interpretation
  -- agrees with it at every model context and environment.
  meaning-unique :
    {n : ℕ}
    {value :
      {d : ℕ} → Tree.Tree (Sig.to-signature (Binding.over (Raw.binding C)))
        (Binding.Variable n) d
      → (X : Ob) → Vec (Tm X) (d + n) → Tm X}
    → Initiality.Homomorphic
        (λ d t → (X : Ob) → Vec (Tm X) (d + n) → Tm X) value
        (Fold.on-hole (algebra n)) (Fold.node-method (algebra n))
    → {d : ℕ}
      (t : Tree.Tree (Sig.to-signature (Binding.over (Raw.binding C)))
        (Binding.Variable n) d)
    → (X : Ob) (env : Vec (Tm X) (d + n)) → value t X env ＝ meaning t X env
  meaning-unique {n} {value} laws t =
    Initiality.fold-unique-rel (algebra n) (identity-related n) value laws t

  ----------------------------------------------------------------------
  -- Trees moved by a lax translation

  -- A tree at depth j transported along j ＝ j′.
  meaning-transport :
    {n j j′ : ℕ} (eq : j ＝ j′)
      (t : Tree.Tree (Sig.to-signature (Binding.over (Raw.binding C)))
        (Binding.Variable n) j)
    (X : Ob) (env : Vec (Tm X) (j′ + n))
    → meaning
        (transport
          (Tree.Tree (Sig.to-signature (Binding.over (Raw.binding C)))
            (Binding.Variable n))
          eq t)
        X env
      ＝ meaning t X (transport (λ i → Vec (Tm X) (i + n)) (eq ⁻¹) env)
  meaning-transport refl t X env = refl

  -- The environment read through a hole map.
  reindex :
    {X : Ob} (m m′ e : ℕ) (h : (c : ℕ) → Fin (c + m) → Fin ((c + e) + m′))
    (c : ℕ) → Vec (Tm X) ((c + e) + m′) → Vec (Tm X) (c + m)
  reindex m m′ e h c env = tabulate (λ x → vector-lookup env (h c x))

  reindex-ext :
    {X : Ob} (m m′ e : ℕ) (h : (c : ℕ) → Fin (c + m) → Fin ((c + e) + m′))
    → ((c : ℕ) → h (suc c) fzero ＝ fzero)
    → ((c : ℕ) (x : Fin (c + m)) → h (suc c) (fsuc x) ＝ fsuc (h c x))
    → (a : Tm X) (c : ℕ) (env : Vec (Tm X) ((c + e) + m′))
    → reindex m m′ e h (suc c) (ext a env) ＝ ext a (reindex m m′ e h c env)
  reindex-ext m m′ e h h-zero h-suc a c env =
    ap₂ _∷_ (ap (vector-lookup (ext a env)) (h-zero c))
      (tabulate-cong
          (λ x → ap (vector-lookup (ext a env)) (h-suc c x) ∙
                   Environment.lookup-[]ᵉ R env p (h c x)) ∙
        tabulate-∘ (λ t → t [ p ]) (λ x → vector-lookup env (h c x)))

  -- Extension, transported along a successor path.
  transport-ext :
    {X : Ob} (a : Tm X) (L : ℕ) {i j : ℕ} (eq : i ＝ j)
    (env : Vec (Tm X) (j + L))
    → transport (λ y → Vec (Tm (X ▸ a)) (y + L)) (ap suc eq ⁻¹) (ext a env)
      ＝ ext a (transport (λ y → Vec (Tm X) (y + L)) (eq ⁻¹) env)
  transport-ext a L refl env = refl

  shift-transformation :
    (m m′ e : ℕ) (h : (c : ℕ) → Fin (c + m) → Fin ((c + e) + m′))
    → ((c : ℕ) → h (suc c) fzero ＝ fzero)
    → ((c : ℕ) (x : Fin (c + m)) → h (suc c) (fsuc x) ＝ fsuc (h c x))
    → (c : ℕ) → Transformation m′ m (c + e) c
  shift-transformation m m′ e h h-zero h-suc c = record
    { Good = λ k env → Universes.Lift ℓ 𝟙
    ; transform = λ {X} k env →
        reindex m m′ e h (k + c)
          (transport (λ y → Vec (Tm X) (y + m′)) (+-assoc k c e ⁻¹) env)
    ; good-ext = λ a k env g → Universes.lift ⋆
    ; transform-ext = λ {X} a k env g →
        ap (reindex m m′ e h (suc (k + c)))
            (transport-ext a m′ (+-assoc k c e) env) ∙
          reindex-ext m m′ e h h-zero h-suc a (k + c)
            (transport (λ y → Vec (Tm X) (y + m′)) (+-assoc k c e ⁻¹) env)
    }

  -- The value of a tree at depth j, scope m′, against one at depth c,
  -- scope m, along a path c + e ＝ j of depths: equal at every environment
  -- read through the hole map after transport along the path.
  shift-cell :
    (m m′ e : ℕ) (h : (c : ℕ) → Fin (c + m) → Fin ((c + e) + m′))
    {c j : ℕ} → c + e ＝ j
    → ((X : Ob) → Vec (Tm X) (c + m) → Tm X)
    → ((X : Ob) → Vec (Tm X) (j + m′) → Tm X) → Set ℓ
  shift-cell m m′ e h {c} {j} graph v w =
    (X : Ob) (env : Vec (Tm X) (j + m′))
    → w X env
      ＝ v X
          (reindex m m′ e h c
            (transport (λ y → Vec (Tm X) (y + m′)) (graph ⁻¹) env))

  -- The interpretation's algebras at scopes m and m′ along the shift by e:
  -- a hole is read through the hole map, and nodes by `node-transport` at
  -- the shift transformation. Both cells are matched at refl, where the
  -- shift's boundary path is +-assoc.
  shift-algebra :
    (m m′ e : ℕ) (h : (c : ℕ) → Fin (c + m) → Fin ((c + e) + m′))
    → (h-zero : (c : ℕ) → h (suc c) fzero ＝ fzero)
    → (h-suc : (c : ℕ) (x : Fin (c + m))
               → h (suc c) (fsuc x) ＝ fsuc (h c x))
    → Heterogeneous.Heterogeneous-Relational-Algebra
        (LaxTree.lax-translation-signature-relation
          (Binding.shift (Raw.binding C) e))
        (LaxTree.Lax-Hole-Action-Cell (λ c → c + e) (Binding.Variable m)
          (Binding.Variable m′) h)
        (shift-cell m m′ e h) (algebra m) (algebra m′)
  Heterogeneous.on-heterogeneous-hole-rel
    (shift-algebra m m′ e h h-zero h-suc)
    {source-judgment = c} {judgment-cell = refl} {source-payload = x}
    refl X env =
    lookup-tabulate (λ y → vector-lookup env (h c y)) x ⁻¹
  Heterogeneous.on-heterogeneous-node-rel
    (shift-algebra m m′ e h h-zero h-suc)
    {source-judgment = c} {judgment-cell = refl} {source-operation = o}
    refl {source-values = v} {target-values = w} cells X env =
    node-transport m′ m (c + e) c
      (shift-transformation m m′ e h h-zero h-suc c) o w v
      (λ p X′ env′ g → cells p X′ env′) X env (Universes.lift ⋆)

  shift-meaning :
    (m m′ e : ℕ) (h : (c : ℕ) → Fin (c + m) → Fin ((c + e) + m′))
    → (h-zero : (c : ℕ) → h (suc c) fzero ＝ fzero)
    → (h-suc : (c : ℕ) (x : Fin (c + m))
               → h (suc c) (fsuc x) ＝ fsuc (h c x))
    → {c : ℕ}
      (t : Tree.Tree (Sig.to-signature (Binding.over (Raw.binding C)))
        (Binding.Variable m) c)
    → (X : Ob) (env : Vec (Tm X) ((c + e) + m′))
    → meaning
        (LaxTree.map-lax-tree (Binding.shift (Raw.binding C) e)
          (Binding.Variable m′) h t)
        X env
      ＝ meaning t X (reindex m m′ e h c env)
  shift-meaning m m′ e h h-zero h-suc t =
    LaxFold.lax-tree-fold-natural (Binding.shift (Raw.binding C) e)
      (Binding.Variable m′) h (shift-algebra m m′ e h h-zero h-suc) t

  -- Binding's hole maps commute with extension.
  rebound-zero :
    (n e c : ℕ)
    → Binding.rebound (Raw.binding C) n e (suc c) fzero ＝ fzero
  rebound-zero n e c = transport-zero (+-assoc c e n)

  rebound-suc :
    (n e c : ℕ) (x : Fin (c + (e + n)))
    → Binding.rebound (Raw.binding C) n e (suc c) (fsuc x)
      ＝ fsuc (Binding.rebound (Raw.binding C) n e c x)
  rebound-suc n e c x = transport-suc (+-assoc c e n) x

  -- Shift's to-ℕ-moved, with the scope explicit.
  to-ℕ-moved :
    (m d c : ℕ) (x : Fin (c + m))
    → to-ℕ (Binding.moved (Raw.binding C) m d c x) ＝ Shift.shifted c d (to-ℕ x)
  to-ℕ-moved m d c x = Shift.to-ℕ-moved (Raw.binding C) d c x

  moved-zero :
    (m d c : ℕ) → Binding.moved (Raw.binding C) m d (suc c) fzero ＝ fzero
  moved-zero m d c =
    to-ℕ-is-injective
      (to-ℕ-moved m d (suc c) fzero ∙
        shifted-below (suc c) 0 d (s≤s z≤n))

  moved-suc :
    (m d c : ℕ) (x : Fin (c + m))
    → Binding.moved (Raw.binding C) m d (suc c) (fsuc x)
      ＝ fsuc (Binding.moved (Raw.binding C) m d c x)
  moved-suc m d c x =
    to-ℕ-is-injective
      (to-ℕ-moved m d (suc c) (fsuc x) ∙
        (shifted-suc c d (to-ℕ x) ∙
          ap suc (to-ℕ-moved m d c x ⁻¹)))

  -- An expression of scope e + n, read as a binder premise of depth e.
  bound-meaning :
    {n : ℕ} (e : ℕ) (B : Raw.Expression C (e + n)) (X : Ob)
    (env : Vec (Tm X) (e + n))
    → meaning (Binding.bound (Raw.binding C) n e B) X env ＝ meaning B X env
  bound-meaning {n} e B X env =
    shift-meaning (e + n) n e (Binding.rebound (Raw.binding C) n e)
        (rebound-zero n e) (rebound-suc n e) B X env ∙
      ap (meaning B X) (tabulate-lookup env)

  -- An expression of scope m, moved under c binders.
  under-meaning :
    {m : ℕ} (c : ℕ) (e : Raw.Expression C m) (X : Ob)
    (env : Vec (Tm X) (c + m))
    → meaning (Binding.under (Raw.binding C) m c e) X env
      ＝ meaning e X (outer c m env)
  under-meaning {m} c e X env =
    shift-meaning m m c (Binding.moved (Raw.binding C) m c)
      (moved-zero m c) (moved-suc m c) e X env

  ----------------------------------------------------------------------
  -- Substitution

  -- The values of the replacements of the variables at depth c.
  σ-env :
    {n m : ℕ} (σ : Fin n → Raw.Expression C m) (c : ℕ) {X : Ob}
    → Vec (Tm X) (c + m) → Vec (Tm X) (c + n)
  σ-env {m = m} σ c {X} env =
    tabulate (λ i → meaning (Binding.replacement (Raw.binding C) m σ c i) X env)

  replacement-cases :
    {n m : ℕ} (σ : Fin n → Raw.Expression C m) (c : ℕ) {X : Ob} (a : Tm X)
    (env : Vec (Tm X) (c + m))
    → ((k : Fin n) → Stable (meaning (σ k)) X (outer c m env))
    → (s : Fin c ⊎ Fin n)
    → meaning
        (Binding.replacement (Raw.binding C) m σ (suc c) (fsuc (join-at c n s)))
        (X ▸ a) (ext a env)
      ＝ meaning
          (Binding.replacement (Raw.binding C) m σ c (join-at c n s)) X env
          [ p ]
  replacement-cases {n} {m} σ c {X} a env stable (inl j) =
    ap
        (λ s → meaning
          (cases (λ i → Tree.hole (i ↑ˡ m))
            (λ k → Binding.under (Raw.binding C) m (suc c) (σ k))
             (left-fsuc s))
          (X ▸ a) (ext a env))
        (split-at-↑ˡ c j n) ∙
      (Environment.lookup-[]ᵉ R env p (j ↑ˡ m) ∙
        ap
          (λ s → meaning
            (cases (λ i → Tree.hole (i ↑ˡ m))
              (λ k → Binding.under (Raw.binding C) m c (σ k)) s)
            X env [ p ])
          (split-at-↑ˡ c j n ⁻¹))
  replacement-cases {n} {m} σ c {X} a env stable (inr k) =
    ap
        (λ s → meaning
          (cases (λ i → Tree.hole (i ↑ˡ m))
            (λ k′ → Binding.under (Raw.binding C) m (suc c) (σ k′))
             (left-fsuc s))
          (X ▸ a) (ext a env))
        (split-at-↑ʳ c n k) ∙
      (under-meaning (suc c) (σ k) (X ▸ a) (ext a env) ∙
        (ap (meaning (σ k) (X ▸ a)) (Environment.outer-ext R a c m env) ∙
          (stable k (X ▸ a) p ∙
            ap (λ t → t [ p ])
              (under-meaning c (σ k) X env ⁻¹ ∙
                ap
                  (λ s → meaning
                    (cases (λ i → Tree.hole (i ↑ˡ m))
                      (λ k′ → Binding.under (Raw.binding C) m c (σ k′)) s)
                    X env)
                  (split-at-↑ʳ c n k ⁻¹)))))

  σ-env-ext :
    {n m : ℕ} (σ : Fin n → Raw.Expression C m) (c : ℕ) {X : Ob} (a : Tm X)
    (env : Vec (Tm X) (c + m))
    → ((k : Fin n) → Stable (meaning (σ k)) X (outer c m env))
    → σ-env σ (suc c) (ext a env) ＝ ext a (σ-env σ c env)
  σ-env-ext {n} {m} σ c {X} a env stable =
    ap (λ e → q a ∷ e)
      (tabulate-cong
          (λ i →
            transport
              (λ y → meaning
                       (Binding.replacement (Raw.binding C) m σ (suc c)
                         (fsuc y))
                       (X ▸ a) (ext a env)
                     ＝ meaning (Binding.replacement (Raw.binding C) m σ c y)
                         X env [ p ])
              (join-at-split-at c n i)
              (replacement-cases σ c a env stable (split-at c n i))) ∙
        tabulate-∘ (λ t → t [ p ])
          (λ i → meaning (Binding.replacement (Raw.binding C) m σ c i) X env))

  substitution-transformation :
    {n m : ℕ} (σ : Fin n → Raw.Expression C m) (c : ℕ)
    → Transformation m n c c
  substitution-transformation {n} {m} σ c = record
    { Good = λ {X} k env →
        (i : Fin n) → Stable (meaning (σ i)) X (outer (k + c) m env)
    ; transform = λ k env → σ-env σ (k + c) env
    ; good-ext = λ {X} a k env g i →
        transport (Stable (meaning (σ i)) (X ▸ a))
          (Environment.outer-ext R a (k + c) m env ⁻¹)
          (Environment.stable-[] R (meaning (σ i)) X (outer (k + c) m env)
            (g i) p)
    ; transform-ext = λ a k env g → σ-env-ext σ (k + c) a env g
    }

  -- The value of a substituted tree at depth c against that of the tree:
  -- equal at every environment where what is substituted is stable, the
  -- tree read at the environment of its values.
  Substituted :
    {n m : ℕ} (σ : Fin n → Raw.Expression C m) {c : ℕ}
    → ((X : Ob) → Vec (Tm X) (c + m) → Tm X)
    → ((X : Ob) → Vec (Tm X) (c + n) → Tm X) → Set ℓ
  Substituted {n} {m} σ {c} v w =
    (X : Ob) (env : Vec (Tm X) (c + m))
    → ((i : Fin n) → Stable (meaning (σ i)) X (outer c m env))
    → v X env ＝ w X (σ-env σ c env)

  substitution-meaning :
    {n m : ℕ} (σ : Fin n → Raw.Expression C m) {c : ℕ}
    (t : Tree.Tree (Sig.to-signature (Binding.over (Raw.binding C)))
      (Binding.Variable n) c) (X : Ob) (env : Vec (Tm X) (c + m))
    → ((i : Fin n) → Stable (meaning (σ i)) X (outer c m env))
    → meaning (Substitution.bind (Binding.replacement (Raw.binding C) m σ) t)
        X env
      ＝ meaning t X (σ-env σ c env)
  substitution-meaning {n} {m} σ t =
    RelationalSubstitution.bind-fold-rel (Substituted σ) (algebra m)
      (algebra n) (Binding.replacement (Raw.binding C) m σ)
      (λ {c} x X env g →
        lookup-tabulate
          (λ i → meaning (Binding.replacement (Raw.binding C) m σ c i) X env)
          x ⁻¹)
      (λ {c} o {v} {w} related X env g →
        node-transport m n c c (substitution-transformation σ c) o v w
          (λ p X′ env′ g′ → related p X′ env′ g′) X env g)
      t

  -- The substitution lemma for expressions.
  substitute-meaning :
    {n m : ℕ} (σ : Fin n → Raw.Expression C m) (e : Raw.Expression C n)
    (X : Ob) (env : Vec (Tm X) m)
    → ((i : Fin n) → Stable (meaning (σ i)) X env)
    → meaning (Binding.substitute (Raw.binding C) m σ e) X env
      ＝ meaning e X (tabulate (λ i → meaning (σ i) X env))
  substitute-meaning {n} {m} σ e X env stable =
    substitution-meaning σ e X env
        (λ i → transport (Stable (meaning (σ i)) X) (tabulate-lookup env ⁻¹)
                 (stable i)) ∙
      ap (meaning e X)
        (tabulate-cong
          (λ i → under-meaning 0 (σ i) X env ∙
                   ap (meaning (σ i) X) (tabulate-lookup env)))
