Results that need Agda's two-level type theory (`--two-level`): strict identification `_≐_`, the outer types (`SSet`) it lives in, and the strict Mahlo rule, whose decoding laws are strict identifications in context. SPT's Foundation and its other shared owners are one-level; every module outside LCTT that uses `--two-level` is in this folder, and the index [TwoLevel.agda](../TwoLevel.agda) lists them.

Every module is `--safe` and `--without-K`. The strict rule's records are hypotheses: nothing here asserts that a model has them.

## Strict identification

| Module | Contents |
| --- | --- |
| [Coherence](Coherence.agda) | Classes of identifications closed under path induction with coherent data (the record `Class`), which contain inverses, composites and applications (`coherent-⁻¹`, `coherent-∙`, `coherent-ap`); the class `every` of all identifications, and the class `strict` of those induced by strict identifications (`Strictly`), any two of which agree, coherently (`strictly-agree`, `strictly-agree-coherent`). Strict identification `_≐_` has application, transport, composition and passage to identity (`apˢ`, `transportˢ`, `_∙ˢ_`, `fibrant`); the outer unit type is `𝟙ˢ`. |
| [Empty](Empty.agda) | The fibrant empty type eliminates into every outer type (`𝟘-elimˢ`). |

## The strict Mahlo rule

| Module | Contents |
| --- | --- |
| [Mahlo](Mahlo.agda) | The strict Mahlo rule for a Tarski family (`Strict-Mahlo`, a record): a parent code at each operator, an interpretation of its decoding, and points naming every former and the operator's value, each decoding law a strict identification between functions of all its arguments, as `inner-β : (λ Ψ F → map (inner Ψ F)) ≐ (λ Ψ F → Ψ (map F))`. The laws hold in the context of the operator without function extensionality. The record is a hypothesis. |
| [Mahlo/Branches](Mahlo/Branches.agda) | Branches respect strict identification of families in context: the first family's branches, read along the inverse identification of codes, are identified with the second's (`branches-along`). |
| [Mahlo/StepAlgebra](Mahlo/StepAlgebra.agda) | A labelled algebra of the Mahlo step (`Labelled`: carriers with readouts, operations for the formers, operator results and branches, and their strict laws in context) with a classification of its carriers by parent codes (`Classification`, to after from strictly the identity) gives the strict rule (`inner-law`, `strict-mahlo`). For the ambient family the classification is the identity (`ambient`, `ambient-mahlo`). |
| [Mahlo/StepAlgebra/Discriminator](Mahlo/StepAlgebra/Discriminator.agda) | Induction–recursion gives a labelled algebra of the ambient formers, each label law by computation (`universe`), and hence the strict ambient Mahlo rule (`mahlo`). |
| [Mahlo/Displayed](Mahlo/Displayed.agda) | The strict Mahlo rule for displayed families (`Strict-Display-Mahlo`, a record): base codes at each ambient operator and fiber codes over them at each fiber operator, its nine decoding laws identifying entire pairs of base and fiber functions in their dependent contexts. The fibers of sums, products, trees and identities are the glued formers of Incidence.Displayed.Glued. The projection `ambient` gives `Strict-Mahlo` for the base codes. The record is a hypothesis. |
| [Mahlo/Displayed/Branches](Mahlo/Displayed/Branches.agda) | Strictly identified split families carry base points back (`back`) and fiber points over those same points (`carry`); the entire dependent pair of branch sets and branch fibers is identified after this transport (`branches-along`). |
| [Mahlo/Displayed/StepAlgebra](Mahlo/Displayed/StepAlgebra.agda) | A labelled display algebra (`Labelled-Display`: codes for each former and for an operator's result and branches, with fiber codes over them, and their laws base and fiber together, in context) gives the strict displayed rule: pairing results with branches gives `inner` and `inner-fiber`, whose `inner-law` constructs `strict-display-mahlo`. |
| [Mahlo/Displayed/StepAlgebra/Discriminator](Mahlo/Displayed/StepAlgebra/Discriminator.agda) | Induction–recursion gives fiber codes over each ambient step code (`Fiber-Code`, `read-fiber`): the glued fibers of the formers and the operator's fiber family and branches. All ten strict laws of displays hold by `same`, giving the labelled display algebra and the strict displayed rule. |

## Uses and paper proofs

LCTT's formal theory reads judgmental equality as strict identification: its soundness, lawfulness and consistency theorems take the classes of [Coherence](Coherence.agda), and its consistency theorems with the Mahlo rule take `Strict-Mahlo` or `Strict-Display-Mahlo` as hypotheses (LCTT, not in this release).

The paper proofs [StrictMahlo.md](../--drafts--/StrictMahlo.md) and [StrictDisplayMahlo.md](../--drafts--/StrictDisplayMahlo.md) place the strict rule, and its form for the universe of displays, in simplicial sets, every decoding law an equality of maps.
