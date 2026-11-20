# Martin-Löf type theory with univalence and the Mahlo rule: syntax and soundness

**Main theorem.** Every derivation of the core theory is valid in every
model of it ([Soundness](Soundness.agda), `soundness`, by
`fold` over derivations), and in a model where 0 has no closed term the
theory derives no closed term of 0 (`consistency`).

The core theory ([Theory](Theory.agda)) is Martin-Löf type theory with:
- Russell universes at closed levels and Lift;
- Π, Σ, identity types and W;
- 0, 1, + and ℕ;
- Kubánek's Mahlo subuniverses (Canonicity of the Mahlo Universe, MSc
  thesis, Chalmers 2025, §3.3);
- univalence and the ambient Mahlo rule of the universe at every level, its
  only constants.

## The two constants

Each is a constant whose type is a closed statement at level $l+1$, written
in the theory's own syntax.
- `univalence l` ([Univalence](Univalence.agda)) is TypeTopology's
  `is-univalent`:
  $$\prod_{X, Y : U_l} \mathsf{is\text{-}equiv}(\mathsf{idtoeq}_{X,Y}),$$
  - $\mathsf{is\text{-}equiv}\, f$ is `has-section f × is-section f`;
  - $\mathsf{idtoeq}_{X,Y}\, p = \mathsf{transport}^{X \simeq -}(p,
    \simeq\text{-}\mathsf{refl}_X)$, transport being J at the identity
    function.
- `mahlo l` ([Mahlo](Mahlo.agda)) is SPT's `Mahlo (Ambient.formers ℓ)`
  ([Specification](../Mahlo/Specification.agda),
  [Ambient](../Mahlo/Ambient.agda)):
  $$\prod_{\Psi : \mathrm{Fam} \to \mathrm{Fam}} \ \sum_{A : U_l}
  \mathrm{Closure}(\Psi, A), \qquad \mathrm{Fam} = \sum_{a : U_l} (a \to
  U_l).$$
  Closure's fields form an iterated Σ: an interpretation $I : A \to U_l$,
  names in $A$ of $\mathrm{Lift}\,0$, $\mathrm{Lift}\,1$,
  $\mathrm{Lift}(1+1)$ and $\mathrm{Lift}\,\mathbb{N}$, of the Π, Σ and W
  of every family of $A$, and of every identity type, then `inner` and
  `inner-β`; 𝟚 is written $1+1$.

Both statements are types at level $l+1$ (`univalence-type`,
`mahlo-type`), so each constant is a term of its statement in every valid
context (`univalence-term`, `mahlo-term`;
[Univalence/Formation](Univalence/Formation.agda),
[Mahlo/Formation](Mahlo/Formation.agda)). A model of the theory supplies
closed terms whose types are the values of these statements (`univalent`,
`reflecting` in [Soundness](Soundness.agda)).

## Consistency

- **The intended model** is the simplicial one (Kapulkin–Lumsdaine;
  [Simplicial.md](../--drafts--/Simplicial.md)): its universes are
  univalent, and each satisfies the ambient Mahlo rule when its level is
  read at a Mahlo cardinal. It needs Mahlo cardinals κ₀ < κ₁ < ⋯ and an
  inaccessible above them. It is cited, not built here.
- **The subuniverses** are Dybjer–Setzer induction–recursion; the model
  carries Dybjer–Setzer's rules as equalities of maps, as the structure's
  strict laws need ([UniversalIR.md](../--drafts--/UniversalIR.md),
  Corollary V; on paper, like the rest of the model input).
- **Built here:** only the terminal model
  ([Model/Terminal](Model/Terminal.agda)), in which every type, 0 included,
  has a closed term.
- **Code models cannot replace it.** In a model whose universes are codes,
  two different codes with equivalent decodings refute univalence; and
  `Model` keeps every level in one Agda level.

## Design

- **Expressions:** trees over a binding signature whose judgments are
  binder depths, with variables as holes
  ([Foundation.Tree.Binding](../Foundation/Tree/Binding.agda)). Renaming
  is `map`; moving under binders is `map-lax-tree` along a shift of depths;
  a binder's premise is read under its binders by the same translation
  (`bound`); substitution is `bind`.
- **Universes:** Russell style at closed levels. Every former records the
  levels of the types it carries, contexts the level of each entry, term
  judgments the level of their type, so the interpretation reads every
  universe off the expression.
- **Equality of expressions:** children of trees are functions, so an
  expression and its substituted instances agree only up to `TreeRel _＝_`
  (no function extensionality). One structural rule moves a judgment along
  this relation (`extensional`); the interpretation respects it
  (`meaning-rel` in [Soundness/Transport](Soundness/Transport.agda)).
- **Comparing expressions in derivations:** shallow trees by their
  first-order skeletons, by `refl` ([Skeleton](Skeleton.agda)); otherwise by
  structural laws: reading a premise under its binders commutes with
  substitution ([Binding.Lifting](../Foundation/Tree/Binding/Lifting.agda)),
  with one law per former ([Formers/Substitution](Formers/Substitution.agda))
  and per part of the univalence statement
  ([Univalence/Substitution](Univalence/Substitution.agda)).
- **Rules:** one block per former, each a signature over the judgments,
  combined by the choice-retaining coproduct (`Signature.Coproduct`). Typing
  is a signature generation (`typing`, a ∂-Space with trivial fillers), and
  the derivations of a judgment are the closed histories of the rules at it,
  which are the histories its filled cell generates
  (`derivation-is-generated`, [Judgment](Judgment.agda)).
- **Models:** natural models whose types are the terms of a tower of
  Russell universes, so contexts extend by terms and no decoding is needed
  ([Model/Russell](Model/Russell.agda)). Operations are total and their laws
  hold where the arguments are typed; only extending a substitution takes a
  typing proof. W's eliminator is given at the generic tree. The
  subuniverses' laws are a record over their operations.
- **Interpretation:** the fold of one tree algebra with one node action per
  former (`algebra`, `⟦_⟧` in
  [Soundness/Interpretation](Soundness/Interpretation.agda)). Every
  valuation with its hole and node laws agrees with it (`meaning-unique`, by
  `fold-unique-rel`).
- **Values under the syntactic operations:** one lemma per former relates
  two nodes whose children agree up to a change of environment
  (`node-transport`); every value lemma is a theorem of folds at the
  relation that change gives: along `TreeRel _＝_` by `fold-rel`; along lax
  translation, for `bound` and `under`, by `lax-tree-fold-natural`; under
  `bind` by `bind-fold-rel`.
- **Validity:** a judgment is valid when its context is valid and its terms
  have stable values whose types are the values of their types (`Typed`,
  `Valid`); stability is naturality in the context.
- **Soundness:** `fold` over derivations, the node action being each block's
  soundness at the validity of the premises.

## Modules (all checked)

| Area | Modules |
| --- | --- |
| Raw syntax | [Raw](Raw.agda), [Formers](Formers.agda), [Formers/Substitution](Formers/Substitution.agda), [Skeleton](Skeleton.agda), [Subuniverse](Subuniverse.agda) |
| Judgments and rules | [Judgment](Judgment.agda), [Structural](Structural.agda), [Rules/](Rules) (universes, Lift, Π, Σ, identity, W, 0, 1, +, ℕ, subuniverses, constants) |
| The constants | [Univalence](Univalence.agda), [Univalence/Substitution](Univalence/Substitution.agda), [Univalence/Formation](Univalence/Formation.agda), [Mahlo](Mahlo.agda), [Mahlo/Formation](Mahlo/Formation.agda) |
| The theory | [Theory](Theory.agda), [Derived](Derived.agda) (the rules as functions on derivations), [Discriminator](Discriminator.agda) (λx. x : Π ℕ ℕ needs the extensional rule) |
| Models | [Model](Model.agda), [Model/](Model) (Russell base, one structure per former, the terminal model) |
| Soundness | [Soundness/](Soundness) (Environment, Interpretation, Transport, Instances, Typing, one module per block, WellFounded/ for W via the generic tree), [Soundness](Soundness.agda) |

The binding-signature machinery is general and lives in
[Foundation/Tree/Binding](../Foundation/Tree/Binding.agda) with Laws,
Shift, Transport, Moving, Composition and Lifting.

## Open

- The Russell model record and the categories with families of SPT/CwF are
  two notions of model; one notion, or a comparison between them, is not
  yet decided.
