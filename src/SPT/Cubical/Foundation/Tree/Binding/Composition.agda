{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Tree.Binding.Composition where

-- Substitution of binding-signature expressions composes. Moving under
-- binders commutes with substitution (`under-substitute-rel`), by
-- induction: at nodes through LaxTranslation.Functoriality's
-- `bind-transport` and `tree-rel-equality-transport`; at a bound variable
-- both sides are the same variable (`bound-case`); at a free one the
-- substituted expression is moved under the binders at once or in two
-- steps, which agree (Moving's `moving-compose-rel`, `free-case`).
-- Variables are split by `split-at` and rejoined (`hole-cases`). Hence
-- substituting by σ and then τ is substituting by σ followed by τ
-- (`composite-split`, `composite-cases`, `substitute-compose-rel`), from
-- `bind-assoc-rel` and `bind-cong`. Both laws hold as TreeRel _＝_, with no
-- extensionality.

open import SPT.Cubical.Base
import SPT.Cubical.Foundation.Signature.Sum as Sig
import SPT.Cubical.Foundation.Tree as Tree
import SPT.Cubical.Foundation.Tree.LaxTranslation as LaxTree
import SPT.Cubical.Foundation.Tree.LaxTranslation.Functoriality as Functoriality
import SPT.Cubical.Foundation.Tree.Relation as Relation
import SPT.Cubical.Foundation.Tree.Substitution as Substitution
import SPT.Cubical.Foundation.Tree.Binding as Binding
import SPT.Cubical.Foundation.Tree.Binding.Laws as Laws
import SPT.Cubical.Foundation.Tree.Binding.Moving as Moving
import SPT.Cubical.Foundation.Tree.Binding.Shift as Shift

module _ {ℓo ℓp : Level} (B : Binding.Binding ℓo ℓp) where

  open Binding.Binding B

  ----------------------------------------------------------------------
  -- Moving under binders commutes with substitution

  -- A bound variable: both sides are the same variable.
  bound-case :
    {m l : ℕ} (τ : Fin m → Binding.Expression B l) (c d : ℕ) (j : Fin c)
    → Binding.replacement B l τ (c + d) (Binding.moved B m d c (j ↑ˡ m))
      ＝ LaxTree.map-lax-tree (Binding.shift B d) (Binding.Variable l)
        (Binding.moved B l d)
          (Binding.replacement B l τ c (j ↑ˡ m))
  bound-case {m} {l} τ c d j =
    ap (Binding.replacement B l τ (c + d)) (Shift.moved-bound B c d j) ∙
      (ap
          (cases (λ i → Tree.hole (i ↑ˡ l))
            (λ k → Binding.under B l (c + d) (τ k)))
          (split-at-↑ˡ (c + d) (j ↑ˡ d) m) ∙
        (ap Tree.hole (Shift.moved-bound B c d j ⁻¹) ∙
          ap
            (LaxTree.map-lax-tree (Binding.shift B d) (Binding.Variable l)
              (Binding.moved B l d))
            (ap
                (cases (λ i → Tree.hole (i ↑ˡ l))
                  (λ k → Binding.under B l c (τ k)))
                (split-at-↑ˡ c j m) ⁻¹)))

  -- A free variable: moving its expression under c + d binders at once
  -- or in two steps.
  free-case :
    {m l : ℕ} (τ : Fin m → Binding.Expression B l) (c d : ℕ) (k : Fin m)
    → Relation.TreeRel _＝_
        (Binding.replacement B l τ (c + d) (Binding.moved B m d c (c ↑ʳ k)))
        (LaxTree.map-lax-tree (Binding.shift B d) (Binding.Variable l)
          (Binding.moved B l d)
          (Binding.replacement B l τ c (c ↑ʳ k)))
  free-case {m} {l} τ c d k =
    Laws.related-by
      (ap (Binding.replacement B l τ (c + d))
          (Shift.moved-free B c d k) ∙
        ap
          (cases (λ i → Tree.hole (i ↑ˡ l))
            (λ k′ → Binding.under B l (c + d) (τ k′)))
          (split-at-↑ʳ (c + d) m k))
      (Laws.related-to
        (ap
          (LaxTree.map-lax-tree (Binding.shift B d) (Binding.Variable l)
            (Binding.moved B l d))
          (ap
            (cases (λ i → Tree.hole (i ↑ˡ l))
              (λ k′ → Binding.under B l c (τ k′)))
            (split-at-↑ʳ c m k)))
        (Relation.rel-sym _⁻¹ (Moving.moving-compose-rel B c d (τ k))))

  hole-cases :
    {m l : ℕ} (τ : Fin m → Binding.Expression B l) (c d : ℕ)
    (s : Fin c ⊎ Fin m)
    → Relation.TreeRel _＝_
        (Binding.replacement B l τ (c + d)
          (Binding.moved B m d c (join-at c m s)))
        (LaxTree.map-lax-tree (Binding.shift B d) (Binding.Variable l)
          (Binding.moved B l d)
          (Binding.replacement B l τ c (join-at c m s)))
  hole-cases τ c d (inl j) = Laws.equal-related (bound-case τ c d j)
  hole-cases τ c d (inr k) = free-case τ c d k

  under-substitute-rel :
    {m l : ℕ} (τ : Fin m → Binding.Expression B l) (d : ℕ) {c : ℕ}
    (t : Tree.Tree (Sig.to-signature (Binding.over B)) (Binding.Variable m) c)
    → Relation.TreeRel _＝_
        (Substitution.bind (Binding.replacement B l τ)
          (LaxTree.map-lax-tree (Binding.shift B d) (Binding.Variable m)
            (Binding.moved B m d) t))
        (LaxTree.map-lax-tree (Binding.shift B d) (Binding.Variable l)
          (Binding.moved B l d)
          (Substitution.bind (Binding.replacement B l τ) t))
  under-substitute-rel {m} {l} τ d {c} (Tree.hole x) =
    transport
      (λ y →
        Relation.TreeRel _＝_
          (Binding.replacement B l τ (c + d) (Binding.moved B m d c y))
          (LaxTree.map-lax-tree (Binding.shift B d) (Binding.Variable l)
            (Binding.moved B l d)
            (Binding.replacement B l τ c y)))
      (join-at-split-at c m x)
      (hole-cases τ c d (split-at c m x))
  under-substitute-rel {m} {l} τ d {c} (Tree.node o child) =
    Relation.node-rel
      (λ p →
        Laws.related-by
          (Functoriality.bind-transport (Binding.replacement B l τ)
            (+-assoc (depth o p) c d)
            (LaxTree.map-lax-tree (Binding.shift B d) (Binding.Variable m)
              (Binding.moved B m d)
              (child p)))
          (Functoriality.tree-rel-equality-transport (+-assoc (depth o p) c d)
            (under-substitute-rel τ d (child p))))

  ----------------------------------------------------------------------
  -- Substitutions compose

  composite-split :
    {n m l : ℕ} (σ : Fin n → Binding.Expression B m)
    (τ : Fin m → Binding.Expression B l) (c : ℕ) (s : Fin c ⊎ Fin n)
    → Relation.TreeRel _＝_
        (Substitution.bind (Binding.replacement B l τ)
          (Binding.replacement B m σ c (join-at c n s)))
        (Binding.replacement B l
          (λ i → Binding.substitute B l τ (σ i)) c (join-at c n s))
  composite-split {n} {m} {l} σ τ c (inl j) =
    Laws.equal-related
      (ap (Substitution.bind (Binding.replacement B l τ))
          (ap
            (cases (λ i → Tree.hole (i ↑ˡ m)) (λ k → Binding.under B m c (σ k)))
            (split-at-↑ˡ c j n)) ∙
        (ap
            (cases (λ i → Tree.hole (i ↑ˡ l)) (λ k → Binding.under B l c (τ k)))
            (split-at-↑ˡ c j m) ∙
          ap
              (cases (λ i → Tree.hole (i ↑ˡ l)) (λ k →
                  Binding.under B l c (Binding.substitute B l τ (σ k))))
              (split-at-↑ˡ c j n) ⁻¹))
  composite-split {n} {m} {l} σ τ c (inr k) =
    Laws.related-by
      (ap (Substitution.bind (Binding.replacement B l τ))
        (ap
          (cases (λ i → Tree.hole (i ↑ˡ m)) (λ k′ → Binding.under B m c (σ k′)))
          (split-at-↑ʳ c n k)))
      (Laws.related-to
        (ap
          (cases (λ i → Tree.hole (i ↑ˡ l)) (λ k′ →
              Binding.under B l c (Binding.substitute B l τ (σ k′))))
          (split-at-↑ʳ c n k))
        (under-substitute-rel τ c (σ k)))

  composite-cases :
    {n m l : ℕ} (σ : Fin n → Binding.Expression B m)
    (τ : Fin m → Binding.Expression B l) (c : ℕ) (x : Fin (c + n))
    → Relation.TreeRel _＝_
        (Substitution.bind (Binding.replacement B l τ)
          (Binding.replacement B m σ c x))
        (Binding.replacement B l (λ i → Binding.substitute B l τ (σ i)) c x)
  composite-cases {n} {m} {l} σ τ c x =
    transport
      (λ y →
        Relation.TreeRel _＝_
          (Substitution.bind (Binding.replacement B l τ)
            (Binding.replacement B m σ c y))
          (Binding.replacement B l
            (λ i → Binding.substitute B l τ (σ i)) c y))
      (join-at-split-at c n x)
      (composite-split σ τ c (split-at c n x))

  substitute-compose-rel :
    {n m l : ℕ} (σ : Fin n → Binding.Expression B m)
    (τ : Fin m → Binding.Expression B l) (e : Binding.Expression B n)
    → Relation.TreeRel _＝_
        (Binding.substitute B l τ (Binding.substitute B m σ e))
        (Binding.substitute B l (λ i → Binding.substitute B l τ (σ i)) e)
  substitute-compose-rel {n} {m} {l} σ τ e =
    Relation.rel-compose (λ p q → p ∙ q)
      (Substitution.bind-assoc-rel
        (Binding.replacement B m σ) (Binding.replacement B l τ) e)
      (Substitution.bind-cong
        (λ c x →
          Substitution.bind (Binding.replacement B l τ)
            (Binding.replacement B m σ c x))
        (Binding.replacement B l (λ i → Binding.substitute B l τ (σ i)))
        (λ {c} {x} {y} p →
          transport
            (λ z →
              Relation.TreeRel _＝_
                (Substitution.bind (Binding.replacement B l τ)
                  (Binding.replacement B m σ c x))
                (Binding.replacement B l
                  (λ i → Binding.substitute B l τ (σ i)) c z))
            p
            (composite-cases σ τ c x))
        (Relation.rel-refl (λ x → refl) e))
