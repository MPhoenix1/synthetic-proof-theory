{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Formers.Substitution where

-- Substitution into the formers of the core theory, as structural
-- relation TreeRel _＝_. A substituted former is the former of its
-- substituted parts, a premise under d binders taking the substitution
-- lifted over them (Binding.Lifting's `lifted`): one law per former, by
-- `node-rel`, with Lifting's `bound-substituted` at each premise
-- under binders (`universe-substituted`, …, `constant-substituted`). Each
-- law takes the relations of the substituted parts to given expressions,
-- so the laws compose along the parts of a larger expression and no
-- expression is compared whole. Weakening: it is the substitution of the
-- shifted variables (`weakening`, from Laws' `rename-substitute-rel`;
-- both ways, `shifted-from`, `weakened-as`) and keeps the relation
-- (`weaken-related`); the lifted substitution takes a weakened part to the
-- weakened substituted part (`weakened-substituted`, from Lifting's
-- `weaken-substituted`); and a weakened expression instantiated is the
-- expression (`instantiate-weakened`).

open import SPT.Base hiding (lift; lower; zero)
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Tree as Tree
import SPT.Foundation.Tree.Relation as Relation
import SPT.Foundation.Tree.Binding as Binding
import SPT.Foundation.Tree.Binding.Composition as Composition
import SPT.Foundation.Tree.Binding.Laws as Laws
import SPT.Foundation.Tree.Binding.Lifting as Lifting
open import SPT.MartinLof.Formers using
  (universe; lifted; lift; lower; pi; lambda; application; sigma; pair; first
  ; second; identity; reflexivity; path-induction; tree; supremum
  ; tree-induction; empty; absurd; unit; star; sum; left; right; case; natural
  ; zero; successor; natural-induction; constant; weaken; extended; instantiate)
import SPT.MartinLof.Raw as Raw

------------------------------------------------------------------------
-- Universes and Lift

universe-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ : ℕ)
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ (universe l₁)) (universe l₁)
universe-substituted m σ l₁ = Relation.node-rel (λ ())

lifted-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ l₂ : ℕ)
  (A : Raw.Expression C n) (A′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ A) A′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ (lifted l₁ l₂ A))
      (lifted l₁ l₂ A′)
lifted-substituted m σ l₁ l₂ A A′ rA =
  Relation.node-rel (λ { Raw.lifted-type → rA })

lift-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ l₂ : ℕ)
  (A a : Raw.Expression C n) (A′ a′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ A) A′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ a) a′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ (lift l₁ l₂ A a))
      (lift l₁ l₂ A′ a′)
lift-substituted m σ l₁ l₂ A a A′ a′ rA ra =
  Relation.node-rel (λ { Raw.lift-type → rA ; Raw.lift-term → ra })

lower-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ l₂ : ℕ)
  (A x : Raw.Expression C n) (A′ x′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ A) A′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ x) x′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ (lower l₁ l₂ A x))
      (lower l₁ l₂ A′ x′)
lower-substituted m σ l₁ l₂ A x A′ x′ rA rx =
  Relation.node-rel (λ { Raw.lower-type → rA ; Raw.lower-term → rx })

------------------------------------------------------------------------
-- Π

pi-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ l₂ : ℕ)
  (A : Raw.Expression C n) (B : Raw.Expression C (suc n))
  (A′ : Raw.Expression C m) (B′ : Raw.Expression C (suc m))
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ A) A′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) (suc m)
        (Lifting.lifted (Raw.binding C) m 1 σ) B)
      B′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ (pi l₁ l₂ A B))
      (pi l₁ l₂ A′ B′)
pi-substituted {C} m σ l₁ l₂ A B A′ B′ rA rB =
  Relation.node-rel
    (λ { Raw.pi-domain → rA
       ; Raw.pi-codomain →
           Lifting.bound-substituted (Raw.binding C) m σ 1 B B′ rB })

lambda-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ l₂ : ℕ)
  (A : Raw.Expression C n) (B t : Raw.Expression C (suc n))
  (A′ : Raw.Expression C m) (B′ t′ : Raw.Expression C (suc m))
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ A) A′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) (suc m)
        (Lifting.lifted (Raw.binding C) m 1 σ) B)
      B′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) (suc m)
        (Lifting.lifted (Raw.binding C) m 1 σ) t)
      t′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ (lambda l₁ l₂ A B t))
      (lambda l₁ l₂ A′ B′ t′)
lambda-substituted {C} m σ l₁ l₂ A B t A′ B′ t′ rA rB rt =
  Relation.node-rel
    (λ { Raw.lambda-domain → rA
       ; Raw.lambda-codomain →
           Lifting.bound-substituted (Raw.binding C) m σ 1 B B′ rB
       ; Raw.lambda-body →
           Lifting.bound-substituted (Raw.binding C) m σ 1 t t′ rt })

application-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ l₂ : ℕ)
  (A : Raw.Expression C n) (B : Raw.Expression C (suc n))
  (f a : Raw.Expression C n)
  (A′ : Raw.Expression C m) (B′ : Raw.Expression C (suc m))
  (f′ a′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ A) A′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) (suc m)
        (Lifting.lifted (Raw.binding C) m 1 σ) B)
      B′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ f) f′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ a) a′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ (application l₁ l₂ A B f a))
      (application l₁ l₂ A′ B′ f′ a′)
application-substituted {C} m σ l₁ l₂ A B f a A′ B′ f′ a′ rA rB rf ra =
  Relation.node-rel
    (λ { Raw.application-domain → rA
       ; Raw.application-codomain →
           Lifting.bound-substituted (Raw.binding C) m σ 1 B B′ rB
       ; Raw.application-function → rf
       ; Raw.application-argument → ra })

------------------------------------------------------------------------
-- Σ

sigma-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ l₂ : ℕ)
  (A : Raw.Expression C n) (B : Raw.Expression C (suc n))
  (A′ : Raw.Expression C m) (B′ : Raw.Expression C (suc m))
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ A) A′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) (suc m)
        (Lifting.lifted (Raw.binding C) m 1 σ) B)
      B′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ (sigma l₁ l₂ A B))
      (sigma l₁ l₂ A′ B′)
sigma-substituted {C} m σ l₁ l₂ A B A′ B′ rA rB =
  Relation.node-rel
    (λ { Raw.sigma-first → rA
       ; Raw.sigma-second →
           Lifting.bound-substituted (Raw.binding C) m σ 1 B B′ rB })

pair-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ l₂ : ℕ)
  (A : Raw.Expression C n) (B : Raw.Expression C (suc n))
  (a b : Raw.Expression C n)
  (A′ : Raw.Expression C m) (B′ : Raw.Expression C (suc m))
  (a′ b′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ A) A′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) (suc m)
        (Lifting.lifted (Raw.binding C) m 1 σ) B)
      B′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ a) a′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ b) b′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ (pair l₁ l₂ A B a b))
      (pair l₁ l₂ A′ B′ a′ b′)
pair-substituted {C} m σ l₁ l₂ A B a b A′ B′ a′ b′ rA rB ra rb =
  Relation.node-rel
    (λ { Raw.pair-first-type → rA
       ; Raw.pair-second-type →
           Lifting.bound-substituted (Raw.binding C) m σ 1 B B′ rB
       ; Raw.pair-first → ra
       ; Raw.pair-second → rb })

first-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ l₂ : ℕ)
  (A : Raw.Expression C n) (B : Raw.Expression C (suc n))
  (p : Raw.Expression C n)
  (A′ : Raw.Expression C m) (B′ : Raw.Expression C (suc m))
  (p′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ A) A′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) (suc m)
        (Lifting.lifted (Raw.binding C) m 1 σ) B)
      B′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ p) p′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ (first l₁ l₂ A B p))
      (first l₁ l₂ A′ B′ p′)
first-substituted {C} m σ l₁ l₂ A B p A′ B′ p′ rA rB rp =
  Relation.node-rel
    (λ { Raw.first-first-type → rA
       ; Raw.first-second-type →
           Lifting.bound-substituted (Raw.binding C) m σ 1 B B′ rB
       ; Raw.first-pair → rp })

second-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ l₂ : ℕ)
  (A : Raw.Expression C n) (B : Raw.Expression C (suc n))
  (p : Raw.Expression C n)
  (A′ : Raw.Expression C m) (B′ : Raw.Expression C (suc m))
  (p′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ A) A′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) (suc m)
        (Lifting.lifted (Raw.binding C) m 1 σ) B)
      B′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ p) p′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ (second l₁ l₂ A B p))
      (second l₁ l₂ A′ B′ p′)
second-substituted {C} m σ l₁ l₂ A B p A′ B′ p′ rA rB rp =
  Relation.node-rel
    (λ { Raw.second-first-type → rA
       ; Raw.second-second-type →
           Lifting.bound-substituted (Raw.binding C) m σ 1 B B′ rB
       ; Raw.second-pair → rp })

------------------------------------------------------------------------
-- Identity types

identity-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ : ℕ)
  (A a b : Raw.Expression C n) (A′ a′ b′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ A) A′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ a) a′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ b) b′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ (identity l₁ A a b))
      (identity l₁ A′ a′ b′)
identity-substituted m σ l₁ A a b A′ a′ b′ rA ra rb =
  Relation.node-rel
    (λ { Raw.identity-type → rA
       ; Raw.identity-left → ra
       ; Raw.identity-right → rb })

reflexivity-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ : ℕ)
  (A a : Raw.Expression C n) (A′ a′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ A) A′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ a) a′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ (reflexivity l₁ A a))
      (reflexivity l₁ A′ a′)
reflexivity-substituted m σ l₁ A a A′ a′ rA ra =
  Relation.node-rel
    (λ { Raw.reflexivity-type → rA ; Raw.reflexivity-point → ra })

path-induction-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ l₂ : ℕ)
  (A : Raw.Expression C n) (M : Raw.Expression C (suc (suc n)))
  (a d b p : Raw.Expression C n)
  (A′ : Raw.Expression C m) (M′ : Raw.Expression C (suc (suc m)))
  (a′ d′ b′ p′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ A) A′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) (suc (suc m))
        (Lifting.lifted (Raw.binding C) m 2 σ) M)
      M′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ a) a′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ d) d′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ b) b′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ p) p′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ
        (path-induction l₁ l₂ A M a d b p))
      (path-induction l₁ l₂ A′ M′ a′ d′ b′ p′)
path-induction-substituted
  {C} m σ l₁ l₂ A M a d b p A′ M′ a′ d′ b′ p′ rA rM ra rd rb rp =
  Relation.node-rel
    (λ { Raw.induction-type → rA
       ; Raw.induction-motive →
           Lifting.bound-substituted (Raw.binding C) m σ 2 M M′ rM
       ; Raw.induction-base → ra
       ; Raw.induction-method → rd
       ; Raw.induction-end → rb
       ; Raw.induction-path → rp })

------------------------------------------------------------------------
-- W

tree-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ l₂ : ℕ)
  (A : Raw.Expression C n) (B : Raw.Expression C (suc n))
  (A′ : Raw.Expression C m) (B′ : Raw.Expression C (suc m))
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ A) A′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) (suc m)
        (Lifting.lifted (Raw.binding C) m 1 σ) B)
      B′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ (tree l₁ l₂ A B))
      (tree l₁ l₂ A′ B′)
tree-substituted {C} m σ l₁ l₂ A B A′ B′ rA rB =
  Relation.node-rel
    (λ { Raw.tree-shape → rA
       ; Raw.tree-position →
           Lifting.bound-substituted (Raw.binding C) m σ 1 B B′ rB })

supremum-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ l₂ : ℕ)
  (A : Raw.Expression C n) (B : Raw.Expression C (suc n))
  (a f : Raw.Expression C n)
  (A′ : Raw.Expression C m) (B′ : Raw.Expression C (suc m))
  (a′ f′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ A) A′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) (suc m)
        (Lifting.lifted (Raw.binding C) m 1 σ) B)
      B′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ a) a′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ f) f′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ (supremum l₁ l₂ A B a f))
      (supremum l₁ l₂ A′ B′ a′ f′)
supremum-substituted {C} m σ l₁ l₂ A B a f A′ B′ a′ f′ rA rB ra rf =
  Relation.node-rel
    (λ { Raw.supremum-shape-type → rA
       ; Raw.supremum-position-type →
           Lifting.bound-substituted (Raw.binding C) m σ 1 B B′ rB
       ; Raw.supremum-shape → ra
       ; Raw.supremum-children → rf })

tree-induction-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m)
  (l₁ l₂ l₃ : ℕ)
  (A : Raw.Expression C n) (B M : Raw.Expression C (suc n))
  (c : Raw.Expression C (suc (suc (suc n)))) (w : Raw.Expression C n)
  (A′ : Raw.Expression C m) (B′ M′ : Raw.Expression C (suc m))
  (c′ : Raw.Expression C (suc (suc (suc m)))) (w′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ A) A′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) (suc m)
        (Lifting.lifted (Raw.binding C) m 1 σ) B)
      B′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) (suc m)
        (Lifting.lifted (Raw.binding C) m 1 σ) M)
      M′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) (suc (suc (suc m)))
        (Lifting.lifted (Raw.binding C) m 3 σ) c)
      c′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ w) w′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ
        (tree-induction l₁ l₂ l₃ A B M c w))
      (tree-induction l₁ l₂ l₃ A′ B′ M′ c′ w′)
tree-induction-substituted
  {C} m σ l₁ l₂ l₃ A B M c w A′ B′ M′ c′ w′ rA rB rM rc rw =
  Relation.node-rel
    (λ { Raw.recursion-shape-type → rA
       ; Raw.recursion-position-type →
           Lifting.bound-substituted (Raw.binding C) m σ 1 B B′ rB
       ; Raw.recursion-motive →
           Lifting.bound-substituted (Raw.binding C) m σ 1 M M′ rM
       ; Raw.recursion-method →
           Lifting.bound-substituted (Raw.binding C) m σ 3 c c′ rc
       ; Raw.recursion-tree → rw })

------------------------------------------------------------------------
-- 0 and 1

empty-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m)
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ empty) empty
empty-substituted m σ = Relation.node-rel (λ ())

absurd-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ : ℕ)
  (M : Raw.Expression C (suc n)) (t : Raw.Expression C n)
  (M′ : Raw.Expression C (suc m)) (t′ : Raw.Expression C m)
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) (suc m)
        (Lifting.lifted (Raw.binding C) m 1 σ) M)
      M′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ t) t′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ (absurd l₁ M t))
      (absurd l₁ M′ t′)
absurd-substituted {C} m σ l₁ M t M′ t′ rM rt =
  Relation.node-rel
    (λ { Raw.absurd-motive →
           Lifting.bound-substituted (Raw.binding C) m σ 1 M M′ rM
       ; Raw.absurd-term → rt })

unit-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m)
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ unit) unit
unit-substituted m σ = Relation.node-rel (λ ())

star-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m)
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ star) star
star-substituted m σ = Relation.node-rel (λ ())

------------------------------------------------------------------------
-- Sums

sum-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ l₂ : ℕ)
  (A B : Raw.Expression C n) (A′ B′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ A) A′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ B) B′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ (sum l₁ l₂ A B))
      (sum l₁ l₂ A′ B′)
sum-substituted m σ l₁ l₂ A B A′ B′ rA rB =
  Relation.node-rel (λ { Raw.sum-left → rA ; Raw.sum-right → rB })

left-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ l₂ : ℕ)
  (A B a : Raw.Expression C n) (A′ B′ a′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ A) A′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ B) B′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ a) a′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ (left l₁ l₂ A B a))
      (left l₁ l₂ A′ B′ a′)
left-substituted m σ l₁ l₂ A B a A′ B′ a′ rA rB ra =
  Relation.node-rel
    (λ { Raw.left-left-type → rA
       ; Raw.left-right-type → rB
       ; Raw.left-term → ra })

right-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ l₂ : ℕ)
  (A B b : Raw.Expression C n) (A′ B′ b′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ A) A′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ B) B′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ b) b′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ (right l₁ l₂ A B b))
      (right l₁ l₂ A′ B′ b′)
right-substituted m σ l₁ l₂ A B b A′ B′ b′ rA rB rb =
  Relation.node-rel
    (λ { Raw.right-left-type → rA
       ; Raw.right-right-type → rB
       ; Raw.right-term → rb })

case-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m)
  (l₁ l₂ l₃ : ℕ)
  (A B : Raw.Expression C n) (M c d : Raw.Expression C (suc n))
  (s : Raw.Expression C n)
  (A′ B′ : Raw.Expression C m) (M′ c′ d′ : Raw.Expression C (suc m))
  (s′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ A) A′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ B) B′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) (suc m)
        (Lifting.lifted (Raw.binding C) m 1 σ) M)
      M′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) (suc m)
        (Lifting.lifted (Raw.binding C) m 1 σ) c)
      c′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) (suc m)
        (Lifting.lifted (Raw.binding C) m 1 σ) d)
      d′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ s) s′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ (case l₁ l₂ l₃ A B M c d s))
      (case l₁ l₂ l₃ A′ B′ M′ c′ d′ s′)
case-substituted
  {C} m σ l₁ l₂ l₃ A B M c d s A′ B′ M′ c′ d′ s′ rA rB rM rc rd rs =
  Relation.node-rel
    (λ { Raw.case-left-type → rA
       ; Raw.case-right-type → rB
       ; Raw.case-motive →
           Lifting.bound-substituted (Raw.binding C) m σ 1 M M′ rM
       ; Raw.case-left-method →
           Lifting.bound-substituted (Raw.binding C) m σ 1 c c′ rc
       ; Raw.case-right-method →
           Lifting.bound-substituted (Raw.binding C) m σ 1 d d′ rd
       ; Raw.case-term → rs })

------------------------------------------------------------------------
-- ℕ

natural-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m)
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ natural) natural
natural-substituted m σ = Relation.node-rel (λ ())

zero-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m)
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ zero) zero
zero-substituted m σ = Relation.node-rel (λ ())

successor-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m)
  (t : Raw.Expression C n) (t′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ t) t′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ (successor t)) (successor t′)
successor-substituted m σ t t′ rt =
  Relation.node-rel (λ { Raw.successor-term → rt })

natural-induction-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (l₁ : ℕ)
  (M : Raw.Expression C (suc n)) (z : Raw.Expression C n)
  (s : Raw.Expression C (suc (suc n))) (t : Raw.Expression C n)
  (M′ : Raw.Expression C (suc m)) (z′ : Raw.Expression C m)
  (s′ : Raw.Expression C (suc (suc m))) (t′ : Raw.Expression C m)
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) (suc m)
        (Lifting.lifted (Raw.binding C) m 1 σ) M)
      M′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ z) z′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) (suc (suc m))
        (Lifting.lifted (Raw.binding C) m 2 σ) s)
      s′
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ t) t′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ (natural-induction l₁ M z s t))
      (natural-induction l₁ M′ z′ s′ t′)
natural-induction-substituted {C} m σ l₁ M z s t M′ z′ s′ t′ rM rz rs rt =
  Relation.node-rel
    (λ { Raw.natural-motive →
           Lifting.bound-substituted (Raw.binding C) m σ 1 M M′ rM
       ; Raw.natural-base → rz
       ; Raw.natural-step →
           Lifting.bound-substituted (Raw.binding C) m σ 2 s s′ rs
       ; Raw.natural-term → rt })

------------------------------------------------------------------------
-- Constants

constant-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m) (c : C)
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) m σ (constant c)) (constant c)
constant-substituted m σ c = Relation.node-rel (λ ())

------------------------------------------------------------------------
-- Weakening

-- Weakening is the substitution of the shifted variables.
weakening :
  {C : Set} {n : ℕ} (e : Raw.Expression C n)
  → Relation.TreeRel _＝_ (weaken e)
      (Binding.substitute (Raw.binding C) (suc n)
        (λ i → Tree.hole (fsuc i)) e)
weakening {C} e = Laws.rename-substitute-rel (Raw.binding C) fsuc e

-- The substitution of the shifted variables, from weakening.
shifted-from :
  {C : Set} {n : ℕ} (e : Raw.Expression C n) (e′ : Raw.Expression C (suc n))
  → Relation.TreeRel _＝_ (weaken e) e′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) (suc n)
        (λ i → Tree.hole (fsuc i)) e)
      e′
shifted-from e e′ related =
  Relation.rel-compose _∙_ (Relation.rel-sym _⁻¹ (weakening e))
    related

-- Weakening, from the substitution of the shifted variables.
weakened-as :
  {C : Set} {n : ℕ} (e : Raw.Expression C n) (e′ : Raw.Expression C (suc n))
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) (suc n)
        (λ i → Tree.hole (fsuc i)) e)
      e′
  → Relation.TreeRel _＝_ (weaken e) e′
weakened-as e e′ related =
  Relation.rel-compose _∙_ (weakening e) related

-- Weakening keeps the structural relation.
weaken-related :
  {C : Set} {n : ℕ} (e e′ : Raw.Expression C n)
  → Relation.TreeRel _＝_ e e′
  → Relation.TreeRel _＝_ (weaken e) (weaken e′)
weaken-related {C} e e′ related =
  Lifting.rename-related (Raw.binding C) fsuc related

-- The lifted substitution on a weakened part, from the substituted part.
weakened-substituted :
  {C : Set} {n : ℕ} (m : ℕ) (σ : Fin n → Raw.Expression C m)
  (e : Raw.Expression C n) (e′ : Raw.Expression C m)
  → Relation.TreeRel _＝_ (Binding.substitute (Raw.binding C) m σ e) e′
  → Relation.TreeRel _＝_
      (Binding.substitute (Raw.binding C) (suc m)
        (Lifting.lifted (Raw.binding C) m 1 σ) (weaken e))
      (weaken e′)
weakened-substituted {C} m σ e e′ related =
  Relation.rel-compose _∙_
    (Lifting.weaken-substituted (Raw.binding C) m σ e)
    (weaken-related (Binding.substitute (Raw.binding C) m σ e) e′ related)

-- A weakened expression instantiated is the expression.
instantiate-weakened :
  {C : Set} {n : ℕ} (e a : Raw.Expression C n)
  → Relation.TreeRel _＝_ (instantiate (weaken e) a) e
instantiate-weakened {C} {n} e a =
  Relation.rel-compose _∙_
    (Lifting.substitute-related (Raw.binding C) n
      (extended (λ (i : Fin n) → Tree.hole i) a)
      (Laws.rename-substitute-rel (Raw.binding C) fsuc e))
    (Relation.rel-compose _∙_
      (Composition.substitute-compose-rel (Raw.binding C)
        (λ i → Tree.hole (fsuc i))
        (extended (λ (i : Fin n) → Tree.hole i) a) e)
      (Laws.substitute-identity-rel (Raw.binding C) e))
