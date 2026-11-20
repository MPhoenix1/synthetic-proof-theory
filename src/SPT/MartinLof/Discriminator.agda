{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Discriminator where

-- A derivation in the core theory (Theory): the identity function on ℕ,
-- λ x. x : Π ℕ ℕ in the empty context (`identity-function`), from the
-- formation of ℕ in the empty and the extended context
-- (`empty-context`, `natural-type`, `extended-context`,
-- `natural-extended`) and the variable (`assumed`). It tests that the rule
-- blocks combine into derivations, and that the extensional rule carries
-- weight: the assumption rule gives x the weakened ℕ, a tree whose
-- children agree with ℕ's only pointwise, and the extensional rule turns
-- it into ℕ (`weakened`).

open import SPT.Base
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Tree as Tree
import SPT.Foundation.Tree.Relation as Relation
open import SPT.MartinLof.Formers using (natural; pi; lambda; weaken)
open import SPT.MartinLof.Judgment using
  (Context; ∅; _▸[_]_; context; term; type; Judgment-Rel; term-rel
  ; context-refl)
import SPT.MartinLof.Rules.Natural as Natural
import SPT.MartinLof.Rules.Pi as Pi
import SPT.MartinLof.Structural as Structural
import SPT.MartinLof.Theory as Theory

empty-context : Theory.Derivation (context ∅)
empty-context = Tree.node (Theory.structural , Structural.empty) (λ ())

natural-type : Theory.Derivation (type ∅ 0 natural)
natural-type =
  Tree.node (Theory.natural , Natural.formation ∅)
    (λ { fzero → empty-context ; (fsuc ()) })

extended-context :
  Theory.Derivation (context (∅ ▸[ 0 ] natural))
extended-context =
  Tree.node (Theory.structural , Structural.extend ∅ 0 natural)
    (λ { fzero → natural-type ; (fsuc ()) })

natural-extended :
  Theory.Derivation (type (∅ ▸[ 0 ] natural) 0 natural)
natural-extended =
  Tree.node (Theory.natural , Natural.formation (∅ ▸[ 0 ] natural))
    (λ { fzero → extended-context ; (fsuc ()) })

-- In every context, the weakened ℕ and ℕ: the same former, children
-- agreeing at every premise (there are none).
weakened :
  {n : ℕ} (Γ : Context Theory.Constant n)
  → Judgment-Rel
      (term (Γ ▸[ 0 ] natural) 0 (Tree.hole fzero) (weaken natural))
      (term (Γ ▸[ 0 ] natural) 0 (Tree.hole fzero) natural)
weakened Γ =
  term-rel (context-refl (Γ ▸[ 0 ] natural)) (Relation.hole-rel refl)
    (Relation.node-rel (λ ()))

-- x : ℕ ⊢ x : ℕ, by the assumption rule and the extensional rule.
assumed :
  Theory.Derivation
    (term (∅ ▸[ 0 ] natural) 0 (Tree.hole fzero) natural)
assumed =
  Tree.node
    (Theory.structural
    , Structural.extensional
        (term (∅ ▸[ 0 ] natural) 0 (Tree.hole fzero) (weaken natural))
        (weakened ∅))
    (λ { fzero →
           Tree.node
             (Theory.structural
             , Structural.assumption (∅ ▸[ 0 ] natural) fzero)
             (λ { fzero → extended-context ; (fsuc ()) })
       ; (fsuc ()) })

identity-function :
  Theory.Derivation
    (term ∅ 0 (lambda 0 0 natural natural (Tree.hole fzero))
      (pi 0 0 natural natural))
identity-function =
  Tree.node
    (Theory.pi , Pi.introduction ∅ 0 0 natural natural (Tree.hole fzero))
    (λ { fzero → natural-type
       ; (fsuc fzero) → natural-extended
       ; (fsuc (fsuc fzero)) → assumed
       ; (fsuc (fsuc (fsuc ()))) })
