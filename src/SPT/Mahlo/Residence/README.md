# Residence

Internal Mahlo reflection for a Tarski family (C , D , Q) asks, for every operator Ψ, for a closure under the formers and Ψ whose carrier is the decoding of a name c : C. This folder separates the two parts of that demand: the closure, which is free, and residence, the closure being small and named. It calibrates residence against Mahlo reflection, shows that no least closure is Mahlo, and reads the obstructions to residence off the pullback square of a resident family. It also generates a Tarski universe of names over a small family and a family of adjoined types, and shows when that universe has no Mahlo reflector.

## Resident families and constructors

| Module | Contents |
| --- | --- |
| [Families](Families.agda) | A family interpreted in a parent is its pullback along the interpretation: `pullback` identifies its total with the identity-witness pullback, and `image` maps complete families, with identity and composition laws. `Map` retains a triangle identity, while literal composite sources need no transport. `Resident` retains a parent name for the returned carrier, and `compose` composes resident families without independently naming a type. |
| [Constructors](Constructors.agda) | One layer of constructors over a family interpreted in a fixed parent (`Code`, `interpret`). Ψ's family on the new layer needs no transport, since the result code's label is Ψ's output itself, so its square with Ψ under `image` holds by refl (`inner`, `inner-square`). `map h k` has source interpretation literally λ a → k (h a), and its interpretation, identity and composition laws hold by refl in each constructor case (`interpret-map`, `map-id`, `map-compose`). |
| [Constructors/Comparison](Constructors/Comparison.agda) | A map between interpreted families acts on one layer: `change` moves a layer along an identity of its interpretation map, `map` then uses the literal composite source, and `compare` obtains that identity from a retained pointwise triangle under local extensionality (`interpret-map`, `interpret-compare`). Each construction preserves the selected parent interpretation by an identity; the pointwise triangle alone supplies no conversion law. |
| [Constructors/Discriminator](Constructors/Discriminator.agda) | A constant operator's result and members are kept literally, even when those outputs are variables (`result-β`, `branch-β`). Child maps may identify distinct constructor arguments (`distinct`, `coalesced`). Changing the parent is different: preserving its decoded types alone need not commute with the chosen operator (`decoding-preserved`, `not-commutes`). |
| [Reflection](Reflection.agda) | A reflection retains a resident carrier and its interpretation (`resident`). A reflection of a child's own operator, read in the parent, is a reflection there (`compose`, through Subclosure's `through`), and the resident family of the composite is Families' `compose` of the two, by computation (`resident-compose`). The operator square is the whole-family identity `inner-β` expressed through `image`, without a stronger law (`operator-square`). |
| [Names](Names.agda) | Names, in a closure, of the families and codes formed from named codes. Along an identification of families the branches agree at corresponding points (`branch-along`). A family whose head and branches are named is the image of a family of names (`family-join`, `realized-family`), under function extensionality for the maps into the codes. So the formers of named codes, the operator's result and branch codes at them, and identity codes over a named code are named (`former-name`, `result-name`, `branch-name`, `identity-name`). |

## Closure, leastness and residence

| Module | Contents |
| --- | --- |
| [Absorption](Absorption.agda) | Least closures: every motive with methods at a closure's codes has a section computing at each code (`Methods`, `Induction`). Small least closures (`Small-Least`), absorbed reflections, whose closure is least (`Absorbed`), and absorption, one for every operator (`Absorption`), hence a reflector (`mahlo`). Absorption factors exactly into a small least closure and a name for its carrier (`absorbed-small`, `absorbed-named`, `carried`, `named`). |
| [Membership](Membership.agda) | Generated membership: the closure of a Tarski family under the formers and an operator, as an inductive family of witnesses over its names (`Form`), with no induction–recursion, for names at any level κ; the total Σ C Form lies at κ ⊔ ℓ. For a small family (κ = ℓ) the total is a closure (`generated`) and the least one (`least`), every law by refl, so closure is free; what remains is that the total be named (`Residence`), and residence gives absorption (`residence-absorbs`). |
| [Inductive](Inductive.agda) | What induction–recursion contributes. The induction–recursive closure of [Relative](../Relative.agda) has its codes at the level of the decodings, for names at any level, and it is least (`inductive-least`): a small least closure for every family and operator (`inductive-small`). Where every small type is already the decoding of a name (`Naming`), naming is free and the small closure is absorbed (`naming-absorbs`); the ambient family of all types of a level is such a family (`ambient-naming`, `ambient-absorbs`). |
| [Presentation](Presentation.agda) | Small presentations of generated totals: a small type with a map to the names, a witness that each of its points names a generated member, and a point naming each generated member (`Generated-Presentation`). Every closure names the generated members (`name-in`), and the codes of a least closure are generated members (`members`), so a small least closure is a presentation (`least-presentation`). A presentation carries a closure (`presented-closure`), and a named one a reflection; hence absorption gives named presentations (`absorption-presentations`), and named presentations give Mahlo (`presented-mahlo`). Induction–recursion presents the generated total for names at any level (`inductive-presentation`); for the ambient family this is a weak presentation of a raised type that preserves names (`inductive-resizes`, `inductive-resizes-names`). Function extensionality is taken for the maps into the names only. |
| [Discriminator](Discriminator.agda) | Closure without residence. A small family with one name decoding to the empty type, every former selecting that name, has the generated closure of every operator, and its total is inhabited (`generated-inhabited`). The total is therefore not the decoding of any name (`no-residence`), and the family has no reflection at all (`no-mahlo`): its only carrier is empty and cannot name the empty former. So the closure being free does not make the family Mahlo; residence is the content. |
| [Subclosure](Subclosure.agda) | The least subclosure of a closure. A closure L on a small carrier A makes A a small family in its own right, with L's codes as its formers ([Decoding](../Decoding.agda)'s `child-formers`) and L's inner family as its operator. A closure K of that family, read through L, is a closure of the original one: each of K's names is followed by L's name of its code (`onward`), the interpretation is the composite (`through`), and it is least whenever K is (`through-least`). Generated membership over A is such a closure and is least, with no induction–recursion (`subclosure`, `subclosure-least`). So one small closure for an operator gives a small least closure for it (`subclosure-small`), and Mahlo gives one for every operator (`mahlo-small`). In a least closure every code is reached by exactly one witness (`reach`, `reach-unique`), so a least closure is isomorphic to its least subclosure (`reached`), by extensionality at the branches. |
| [Calibration](Calibration.agda) | Absorption calibrated against Mahlo. The least subclosure makes leastness free once a small closure exists, so absorption asks of a Mahlo family only a name for a small least closure. For a family naming every small type (Inductive's `Naming`) that name is free: small least closures for every operator give absorption (`small-absorbs`), Mahlo gives absorption (`mahlo-absorbs`), and so do small presentations of the generated totals (`presented-small`, `presentations-absorb`). For the ambient family of all types of level ℓ, absorption, Mahlo, small least closures for every operator and presentations of every generated total are therefore interderivable (`ambient-mahlo-absorbs`). None of these derivations uses induction–recursion; it enters only to inhabit them (Inductive's `ambient-absorbs`). |
| [Comparison](Comparison.agda) | Residence up to isomorphism. For a small family whose names form a set, the carrier of any least closure is isomorphic to the generated total (`resides`): a code goes to the generated member it codes (`coded`), a generated member to the code naming it (`naming`), and the two returns hold by the closure's induction (`recovers`) and by recursion on the witnesses (`returns`). So absorption gives, for every operator, a name whose decoding is isomorphic to the generated total (`absorbed-resides`, `absorption-resides`), and literal residence wherever isomorphic types of level ℓ are identified (`residence`). Function extensionality at one level joins the branches. |
| [Containment](Containment.agda), [Containment/Discriminator](Containment/Discriminator.agda) | An absorbed reflection lies inside every reflection of the same operator: each code has a name in the other reflection (`inside`), with extensionality only for maps from decoded domains into the parent codes. Generation obstructs absorption (`unabsorbed`), while the ambient universe is generated by no operator (`ungenerated`); existing small least closures supply its absorption. Leastness is necessary for containment: every closure is a closure of the identity operator (`identity-closure`); in the ambient universe `beyond` names the least identity closure, and `wider` is the resulting larger reflection of the identity, so the least reflection lies inside `wider` (`contained`) but not conversely (`not-inside`): `wider` names the least carrier, which cannot name itself. |

## Obstructions

| Module | Contents |
| --- | --- |
| [Unreflected](Unreflected.agda) | A least closure is not Mahlo. Let L be a least closure on a small carrier A, so its own codes form a family (`child-formers L`) with L's inner operator. A reflection of that family for its own operator is a closure K on the decoding of one of its codes; since L is least, K names every code of L (`covering`, `covers`), so the codes are a retract of one of their decodings. When trees decode to trees up to similarity this is impossible: the tree code over the retraction has a tree of all its trees, similar to one of its own branches (`no-retract`, by `unfounded`). Hence no least closure reflects its own operator (`unreflected`), none is Mahlo (`not-mahlo`), and no absorbed reflection's child is (`absorbed-not-mahlo`). Function extensionality at the level of the codes joins the branches. |
| [Fibered](Fibered.agda) | Residence read off the pullback square. A resident family omits the code of its own W-type, `tree (r , j)`, which the parent names (`own-tree`; `no-retract` is the case of a section, `from-own-tree`). Hence the square's top map misses the fiber over that code (`total-omits`), restore has no section (`restore-unsplit`), no resident family receives the constant family at every code (`no-collection`), the parent's families and operators are read off no fiber (`families-unresident`, `operators-unresident`), and a tower of resident composites never returns onto its first carrier (`no-return`). A resident family's own families and operators are read off parent fibers (`state-resident`, `actions-resident`); with `operators-unresident` this is the size form of Dybjer and Setzer's Corollary 5.6. No function extensionality is used. |

## A generated universe of names

[Adjoined](Adjoined.agda) generates a Tarski universe by the formers over a small family (L , D) and a family (I , E) whose index type may lie one level higher. `Form`, an inductive family over the types of level ℓ, retains the formation of each type, and a name is a type with its formation.

| Module | Contents |
| --- | --- |
| [Adjoined](Adjoined.agda) | The formation of types by the formers, by the lower types D l, by L itself and by the adjoined types E i (`Form`, with `liftedᶠ`, `belowᶠ`, `adjoinedᶠ`), names as types with their formation (`Name`, `decode`), and the names of the formers, of D l, of L and of E i (`lifted`, `below`, `adjoined`). The formers decode by computation (`name-formers`, `name-decoding`). |
| [Adjoined/Children](Adjoined/Children.agda) | Codes of families, children and closure under an operator in an adjoined universe (`family`, `child`, `closed-under`); `included` maps a child's decoded families into its parent's. Transport of function and sum codes and closure congruence retain the given paths of codes (`transport-sum-back`, `transport-arrow-back`, `closure-congruence`). |
| [Adjoined/Connectives](Adjoined/Connectives.agda) | Negation and disjunction of names, by products with empty values and sums over two (`negation`, `disjunction`). `decided` names the disjunction of a lower name with its negation, and `excluded-middle` their product over every lower name. These are names, with no inhabitance hypothesis. |
| [Adjoined/Discrimination](Adjoined/Discrimination.agda) | A lifted lower name differs from the generated empty name: `is-lifted` distinguishes their formation constructors, and `lifted-is-not-empty` applies that distinction to an identification. |
| [Adjoined/Generation](Adjoined/Generation.agda) | The names admit no Mahlo reflector when a decoded name retracts onto the adjoined index. The seed operator names the lower family and every adjoined type (`seed`); by induction on `Form` every closure of it names every name (`reach`, `generated`), and the tree decoding law then rules out a reflection (`unmahlo`, through [Generation](../Generation.agda)'s `unreflected`), under function extensionality. |
| [Adjoined/Sets](Adjoined/Sets.agda) | The names and their decodings are sets when the starting and adjoined families are sets, under function extensionality. `Shape` and `Fields` unfold each name into its constructor and arguments, and the retraction `fold-unfold` gives uniqueness of identifications by recursion on formation (`form-unique`, `name-is-set`, `decode-is-set`). |
| [Adjoined/Realizability](Adjoined/Realizability.agda) | Realizers of the points of the names, over a partial combinatory algebra, by recursion on their formation (`Realized`, `realized`). Products act uniformly on realizers, sums pair them, and trees pair the label's realizer with a function on the realizers of the branches (`Realized-Tree`). A given predicate of atoms realizes the lower family; identities, the lower names and adjoined points are realized uniformly. |
| [Adjoined/Realizability/ExcludedMiddle](Adjoined/Realizability/ExcludedMiddle.agda) | Uniform realizers of sums over two have one tag (`tag-left`, `tag-right`, `one-tag`). If one lower name has an empty left summand and another an empty right summand, a realizer of the product over the lower names of their sums over two identifies the combinators `k` and `second`, so where these differ no tracker of a closed term of that product exists (`refuted`). |
| [Adjoined/Realizability/Reflection](Adjoined/Realizability/Reflection.agda) | `Uniform-Mahlo`, a record: Mahlo reflection of the names whose reflected carriers are realized by every element of the given combinatory algebra, retaining the reflection and its uniformity witness, with no assumption on the realizers of the lower family. It is declared here, not inhabited. |

## Resident families and pullbacks

For a parent family `D : C → Set ℓ` and interpretation `j : A → C`, the returned decoder is literally `λ a → D (j a)`. Its total fits the square

    Σ(a : A). D(j a)  →  Σ(c : C). D c
           ↓                   ↓
           A         →         C
                     j

`Families.pullback` proves the comparison with the identity-type pullback is an isomorphism. Both pointwise inverse laws retain the commuting path; no uniqueness of paths or function extensionality is assumed. `total` and `image` act on decoded points and complete families respectively, with identity and composition laws by `refl` at pairs. A general `Map j k` retains its arrow and triangle identity; `map-total` acts on points using that identity, and `total-triangle` proves its commutation with the parent.

`Resident D` retains `name : C` and `interpret : D name → C`. These are the data of a resident family, without a closure assertion. `compose` uses the first interpretation of the second carrier name. For actual reflections, `Reflection.resident` exposes these data and `Reflection.compose` reuses `Subclosure.through`; `resident-compose` is `refl`. Continuing with operations still uses the full reflection record. `operator-square` is its existing complete-family identity, expressed through `Families.image`.

Stationary reflection ([DS/Stationary](../DS/Stationary.agda)) reads the universes of a child in the parent by this composition, at the identity operator, and Unreflected's `not-mahlo` shows that its witnesses at the unit predicate are never least closures ([DS/Stationary/Discriminator](../DS/Stationary/Discriminator.agda)'s `not-least`). Through `no-retract`, no reflection names its own carrier from below, so a universe naming only derivable names is not of degree one ([DS/Stationary/Derivable](../DS/Stationary/Derivable.agda)).

On the square itself ([Fibered](Fibered.agda)) these obstructions are one fact: residence lets the parent name the W-type of a resident family's pullback, as the code `tree (r , j)`, and the family omits that code (`own-tree`). The child's decoder is the parent's pulled back, so [Retraction](../Retraction.agda)'s `inherited-retracts` gives every child the same fact, which is how the obstructions pass down a tower. The two rows of the operator square differ in residence: a resident family's own families and operators are read off parent fibers, and the parent's are read off none.

`Constructors.Code Ψ A j` is one layer with all four constants, product, sum, tree, identity, operator result and operator branch constructors. It is not recursive. Its sort is `ℓ ⊔ α` when `A : Set α`, independently of the level of the parent names. The selected formers are needed only by `interpret`.

`Constructors.inner Q Ψ j` sends a family `(a , b)` over A, read through j, to `(result a b , branch a b)`, a family over the new layer, read through `interpret Q`. No transport occurs: the label of the result code is Ψ's output itself, so its branches take that output's decoding as it is. The square

    image (interpret Q) ∘ inner  =  Ψ ∘ image j

is `inner-square`, by `refl` at each family. It is the one-layer form of the last law in Theorem 7.2 of the paper proof [StrictMahlo.md](../../--drafts--/StrictMahlo.md), which rests on the same fact. A reflection's square, `Reflection.operator-square`, is still derived from its `inner-β` identity.

For `h : A → B` and `k : B → C`, `Constructors.map h k` acts from the literal composite interpretation `λ a → k (h a)` to `k`. The complete parent input to Ψ is unchanged. No monotonicity, action on parent maps, or injectivity of h is assumed. `interpret-map`, `map-id`, and `map-compose` hold pointwise, by `refl` in each constructor case. They do not claim conversion at a neutral constructor variable.

`Constructors.Comparison` extends this to a supplied identity between the whole interpretation maps (`map`, `interpret-map`). A pointwise `Families.Map` supplies that identity under local function extensionality for maps from A into C (`compare`, `interpret-compare`). This separates identity-mediated comparison from the literal composite case.

The constructor discriminator keeps a constant operator's variable result and branches literally (`result-β`, `branch-β`), permits a noninjective child map (`distinct`, `coalesced`), and refutes commutation for a parent map that preserves decoded types but changes the operator's output (`decoding-preserved`, `not-commutes`).

These results formalize the pullback, constructor-map and one-layer operator part of resident operator closure. They construct no new reflector, and assert no simplicial fibrancy or cardinal bound. The external construction, with fibrancy, cardinal bounds and strict contextual decoding, is in drafts of paper proofs: [StrictMahlo.md](../../--drafts--/StrictMahlo.md), for the strict rule, and [UniversalIR.md](../../--drafts--/UniversalIR.md), for universal induction–recursion, which contains it.

## The decomposition

    Absorption Q  ⇒  Π Ψ. a named small presentation of Ψ's generated total  ⇒  Mahlo Q
    Mahlo Q       ⇒  Π Ψ. a small least closure (its least subclosure)

- For a **small family** (names at the decodings' level) the generated total is already small; the content is naming it (`Residence`). Absorption gives `Residence` up to isomorphism when the names form a set (`Comparison`).
- For a **family naming every small type** (the ambient family) naming is free, and the four conditions are interderivable:

        Absorption  ⇔  Mahlo  ⇔  Π Ψ. small least closure  ⇔  Π Ψ. presentation

  Presentations take function extensionality at the branches.

In both cases what is asked beyond the free closure is the same: the generated total is small and named. Leastness costs nothing further. Any small closure contains a least one, built from an ordinary inductive family over its own codes. So of induction–recursion, internal Mahlo uses exactly one thing: a small closure for every operator. In Agda, the induction–recursive code type is small for two separate reasons: its decoding is simultaneous, so the codes store no names, and the operator is a parameter, which does not raise the sort.

## Strength

Checked here and in the library:

- For a family naming every small type, absorption ⇔ Mahlo (`Calibration`).
- Induction–recursion inhabits absorption (Inductive's `ambient-absorbs`).
- The smallness principle of induction–recursion, every description with outputs in `Set ℓ` having a small algebra ([IR/Smallness](../../IR/Smallness.agda)), is Mahlo for the ambient family: smallness ⇒ Mahlo under extensionality, and Mahlo ⇒ smallness with no hypothesis ([DS/Ambient](../DS/Ambient.agda): `mahlo`, `smallness`). Every rule of induction–recursion follows from smallness by ordinary inductive families, so Mahlo for the ambient family realizes every small-arity Dybjer–Setzer description with outputs in `Set ℓ`, and, through the two-sorted family, with outputs in any type ([DS/Naming](../DS/Naming.agda)'s `outputs`).
- A reflection whose closure is least has no universe of degree one ([DS/Stationary/Discriminator](../DS/Stationary/Discriminator.agda)'s `not-least`, from Unreflected), and the closures of Relative are least (Inductive's `inductive-least`).

From the literature (read, not formalized):

- Dybjer–Setzer, *Induction–recursion and initial algebras*, §6. Two versions of the Mahlo universe:
  - The **external** one: the type of all sets is Mahlo, with a universe U_fg for every f : Fam(set) → Fam(set). It is an induction–recursive definition, of strength at least KPM even without elimination rules for U_fg (Theorem 6.4.1). So the theory IR is at least KPM (Corollary 6.4.2).
  - The **internal** one: a universe V that is itself a set, with subuniverses for every f : Fam(V) → Fam(V). It goes beyond IR, since V's constructor for U_fg is not positive. Its strength is at least KPM⁺ (KPM with ω admissibles above a recursively Mahlo ordinal; Setzer 2000), and Setzer's model shows that bound is sharp.
- Dybjer–Setzer, *The extended predicative Mahlo universe* (2024), footnote 2:
  - no upper bound for IR has been worked out;
  - the conjectured bound is KP with one recursively Mahlo ordinal and finitely many admissibles above it;
  - universes added above a Mahlo universe go beyond that.
- |MLM| = ψ_Ω₁(Ω_{M+ω}) (Setzer 2000), and |KPM⁺| ≤ ψ_Ω₁(Ω_{M+ω}) (Setzer's 1996 draft, Lemma 6.1).

Reading:

- The ambient family at level ℓ is Setzer's internal V, with V = Set ℓ and Set (ℓ+1) as the type of sets. `Mahlo (Ambient.formers ℓ)` is his rule there.
  - So "every generated total is small and named", at one level with a universe above it, carries MLM's lower bound KPM⁺. That bound is transferred, with one caveat: the decoding equations here are identities, not judgmental.
  - With Set ℓ as the top type of sets only the external form remains, of strength at least KPM.
- The step from external to internal is not made by induction–recursion. The same per-operator code type (`Relative.Generated`) serves in both. What makes the rule internal is the universe Set (ℓ+1) containing Set ℓ, over which families of level-ℓ types form W-types (Dybjer–Setzer 2003, proof of Theorem 6.4.1: the external version cannot form W(W)).
- For IR's upper bound:
  - Its one-level part with outputs in types reduces here to the reflection rule: Mahlo for the ambient family ⇒ a small algebra of every description ⇒ every rule of induction–recursion for it, and IR ⇒ absorption. The first two steps are [DS/Ambient](../DS/Ambient.agda) and [IR/Smallness](../../IR/Smallness.agda), with no induction–recursion in their cone.
  - Outputs in any type O, at one level, reduce to the same rule. It gives small algebras of every description with outputs in O, under extensionality for families of names ([DS/Naming](../DS/Naming.agda)'s `outputs`, through the two-sorted family).
  - Not reduced here: the hierarchy as a whole, in which every Set ℓ is Mahlo inside Set (ℓ+1). That is a tower of internal Mahlo universes, beyond MLM; no bound for it is known here.

## Nonclaims

- Residence is shown only up to isomorphism, and only for names forming a set (`Comparison`). That the names form a set is used only to identify the paths between names that the two returns produce.
- A presentation's own carrier is not shown least; its least subclosure is (`presented-small`).
- For a small family that does not name every small type, Mahlo gives small least closures (`mahlo-small`) but not their names. Whether Mahlo gives absorption there is not decided.
- No ordinal is computed here. Every strength above is transferred from the cited sources. No upper bound is checked.
