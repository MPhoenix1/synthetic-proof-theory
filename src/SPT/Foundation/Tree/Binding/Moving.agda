{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Tree.Binding.Moving where

-- Moving expressions under binders composes: moving a tree under e and
-- then d binders is moving it under e + d, after transport of its depth
-- along associativity (`moving-compose-rel`), as the structural relation
-- of trees. At holes this is Shift's `moved-compose`. At nodes, lax
-- translation transports each child along its boundary coherence; the
-- transports compose (`transport-∙`, Transport's
-- `map-lax-tree-transport`), and any two identifications of natural
-- numbers agree (`ℕ-identifications-agree`).

open import SPT.Base
open import SPT.Foundation.Nat.Identifications using
  (ℕ-identifications-agree)
import SPT.Foundation.Signature.Sum as Sig
import SPT.Foundation.Tree as Tree
import SPT.Foundation.Tree.LaxTranslation as LaxTree
import SPT.Foundation.Tree.LaxTranslation.Functoriality as Functoriality
import SPT.Foundation.Tree.Relation as Relation
import SPT.Foundation.Tree.Binding as Binding
import SPT.Foundation.Tree.Binding.Laws as Laws
import SPT.Foundation.Tree.Binding.Shift as Shift
import SPT.Foundation.Tree.Binding.Transport as Transport

module _ {ℓo ℓp : Level} (B : Binding.Binding ℓo ℓp) where

  open Binding.Binding B

  moving-compose-rel :
    {l : ℕ} (e d : ℕ) {c : ℕ}
    (u : Tree.Tree (Sig.to-signature (Binding.over B)) (Binding.Variable l) c)
    → Relation.TreeRel _＝_
        (transport
          (Tree.Tree (Sig.to-signature (Binding.over B)) (Binding.Variable l))
          (+-assoc c e d)
          (LaxTree.map-lax-tree (Binding.shift B d) (Binding.Variable l)
            (Binding.moved B l d)
            (LaxTree.map-lax-tree (Binding.shift B e) (Binding.Variable l)
              (Binding.moved B l e) u)))
        (LaxTree.map-lax-tree (Binding.shift B (e + d)) (Binding.Variable l)
          (Binding.moved B l (e + d)) u)
  moving-compose-rel {l} e d {c} (Tree.hole x) =
    Laws.equal-related
      (Transport.transport-hole B (+-assoc c e d)
          (Binding.moved B l d (c + e) (Binding.moved B l e c x)) ∙
        ap Tree.hole (Shift.moved-compose B c e d x))
  moving-compose-rel {l} e d {c} (Tree.node o child) =
    let T = Tree.Tree (Sig.to-signature (Binding.over B)) (Binding.Variable l)
    in
    Laws.related-by
      (Transport.transport-node B (+-assoc c e d) o
        (λ p →
          transport T (+-assoc (depth o p) (c + e) d)
            (LaxTree.map-lax-tree (Binding.shift B d) (Binding.Variable l)
              (Binding.moved B l d)
              (transport T (+-assoc (depth o p) c e)
                (LaxTree.map-lax-tree (Binding.shift B e)
                  (Binding.Variable l) (Binding.moved B l e) (child p))))))
      (Relation.node-rel
        (λ p →
          let q₁ = ap (λ i → depth o p + i) (+-assoc c e d)
              q₂ = +-assoc (depth o p) (c + e) d
              q₃ = +-assoc (depth o p) c e
              q₄ = +-assoc (depth o p) c (e + d)
              q₅ = +-assoc (depth o p + c) e d
              shifted₃ = ap (λ i → i + d) q₃
              Y = LaxTree.map-lax-tree (Binding.shift B d)
                    (Binding.Variable l) (Binding.moved B l d)
                    (LaxTree.map-lax-tree (Binding.shift B e)
                      (Binding.Variable l) (Binding.moved B l e) (child p))
          in
          Laws.related-by
            (ap (λ v → transport T q₁ (transport T q₂ v))
                (Functoriality.map-lax-tree-transport (Binding.shift B d)
                  (Binding.Variable l) (Binding.moved B l d) q₃
                  (LaxTree.map-lax-tree (Binding.shift B e)
                    (Binding.Variable l) (Binding.moved B l e) (child p))) ∙
              (ap (transport T q₁) (transport-∙ T shifted₃ q₂ Y ⁻¹) ∙
                (transport-∙ T (shifted₃ ∙ q₂) q₁ Y ⁻¹ ∙
                  (ap (λ r → transport T r Y)
                      (ℕ-identifications-agree (shifted₃ ∙ q₂ ∙ q₁)
                        (q₅ ∙ q₄)) ∙
                    transport-∙ T q₅ q₄ Y))))
            (Functoriality.tree-rel-equality-transport q₄
              (moving-compose-rel e d (child p)))))
