{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Tree.Binding.Transport where

-- Transport of binding-signature trees along identifications of depths,
-- for the composition of substitutions of expressions: it passes through
-- holes and nodes, each child along the identification shifted by its
-- premise's depth (`transport-hole`, `transport-node`). For every
-- signature, transport along judgments commutes with bind and with lax
-- translation and keeps the structural relation: those are
-- LaxTranslation.Functoriality's `bind-transport`,
-- `map-lax-tree-transport` and `tree-rel-equality-transport`.

open import SPT.Cubical.Base
import SPT.Cubical.Foundation.Signature.Sum as Sig
import SPT.Cubical.Foundation.Tree as Tree
import SPT.Cubical.Foundation.Tree.Binding as Binding

------------------------------------------------------------------------
-- Binding signatures: through holes and nodes

module _ {ℓo ℓp : Level} (B : Binding.Binding ℓo ℓp) where

  open Binding.Binding B

  transport-hole :
    {n j k : ℕ} (q : j ＝ k) (y : Binding.Variable n j)
    → transport
        (Tree.Tree (Sig.to-signature (Binding.over B)) (Binding.Variable n))
        q (Tree.hole y)
      ＝ Tree.hole (transport (Binding.Variable n) q y)
  transport-hole refl y = refl

  transport-node :
    {n j k : ℕ} (q : j ＝ k) (o : Operation)
    (child :
      (p : Premise o)
      → Tree.Tree (Sig.to-signature (Binding.over B)) (Binding.Variable n)
          (depth o p + j))
    → transport
        (Tree.Tree (Sig.to-signature (Binding.over B)) (Binding.Variable n))
        q (Tree.node o child)
      ＝ Tree.node o
          (λ p →
            transport
              (Tree.Tree (Sig.to-signature (Binding.over B))
                (Binding.Variable n))
              (ap (λ i → depth o p + i) q) (child p))
  transport-node refl o child = refl
