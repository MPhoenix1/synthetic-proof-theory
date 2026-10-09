# Ordinal Geometry: a guide

*Synthetic Proof Theory, Part I*

This guide explains the mathematics checked in this directory and says where
each result is proved. It is written for two audiences: type theorists
interested in ordinals in intensional and univalent type theory, and proof
theorists interested in ordinal analysis carried out inside type theory.
§1.3 gives a reading path for each.

**Evidence.** A result called *checked* is a declaration in the module named
next to it. The whole directory checks with `--safe` and contains no
postulates; see the [README](README.md) for how to check it. Results marked
**†**, all in §8, are checked in the main development from which this
release was extracted, but their modules are not part of this release; they
are named without links. LPO, WLPO, excluded middle, countable choice and
propositional resizing occur only as explicit hypotheses of the theorems
that name them, or as conclusions of discriminators.

## Contents

1. [Overview](#1-overview)
2. [Presentations](#2-presentations)
3. [The countable diagonal](#3-the-countable-diagonal)
4. [Reflection and ω₁](#4-reflection-and-ω₁)
5. [The KNFX table by boundary](#5-the-knfx-table-by-boundary)
6. [TypeTopology, and what reflection forgets](#6-typetopology-and-what-reflection-forgets)
7. [Relation dictionary](#7-relation-dictionary)
8. [Toward ordinal analysis: ID₁](#8-toward-ordinal-analysis-id₁)
9. [Scope and nonclaims](#9-scope-and-nonclaims)
10. [Related work](#10-related-work)

## 1. Overview

### 1.1 The idea

Kraus, Nordvall Forsberg and Xu compare Cantor normal forms, Brouwer trees
and extensional well-orders against eighteen properties one wants of
ordinals: comparison, decidability, zero, successors, limits, suprema,
classification and arithmetic (their Table 1, cited here as the KNFX table).
Each notion gives up some rows. For example, zero, successors, limits of
increasing sequences and decidable equality on one carrier already imply
WLPO (their Theorem 17).

This development asks the rows of different objects. Its basic object is a
*presentation*: a countable well-founded strict order together with its
equivalence relation, a comparison function and a partial enumeration, all
kept as data (§2). A presentation is never quotiented. A point x of a
presentation P is read as its predecessor domain

```text
∂ₚ x  =  Σ (y : X_P), y <ₚ x
```

and ordinals are compared by maps of presentations that keep their
witnesses. Order types are recovered afterwards, by an explicit reflection
into Cubical well-orders (§4). At the reflected level ∂ₚx is exactly the
initial segment that the HoTT book writes `A_{/x}` (§10.3); this guide
claims nothing new there.

The difference lies before that level. In the HoTT book y < x is a
proposition, so `A_{/x}` is a subset of the carrier, and extensionality
says that a point is determined by that subset. Here y <ₚ x is a type and
≈ₚ is part of the structure, so ∂ₚx is a total space whose fibers are data.
`A_{/x}` is what the reflection makes of it (§4.1), and §6.2 measures what
that step forgets.

What the retained data provides is that every row of the KNFX table holds
where its datum lives:

- comparison, decisions and joins hold for the points of one common
  presentation, an *ambient*;
- zero, successors, limits of chains and the arithmetic hold for
  presentations, compared by initial maps and segments;
- suprema of small families, and the classical properties of ω₁, hold for
  the reflected order types.

Asked of all presentations at once, without its datum, each of the rows
2, 5, 6, 8, 13 and 15–18 is equivalent to LPO, and rows 9 and 14 give LPO
(§5). The datum is exactly what the row costs.

The same approach works one level up (§4.7, §4.8). The ordinal of
ordinals of a universe is itself a geometric object: a height whose
children are all the heights of the universe. Its rank is Cubical's
ordinal of ordinals. Reflections of the universe, given by the Mahlo rule,
give its inaccessible points. They are compared with the classical notions
as ω₁ is compared with the ℕ-Hartogs well-order. Under excluded middle and
choice they are inaccessible cardinals, and the ordinal of ordinals is a
Mahlo cardinal.

### 1.2 Synthetic Proof Theory

*Synthetic Proof Theory* is the program of carrying out ordinal analysis as
a type-theoretic discipline. Ordinals are presentations with their retained
data, heights of infinitary derivations are trees read into presentations,
and every bound is a construction in type theory. This release is Part I,
the ordinal geometry. Part II, the analyses, is forthcoming. It contains an
analysis of Peano arithmetic with both halves at the geometric ε₀, and an
upper bound for ID₁ obtained with no ordinal notation for Ω and no
collapsing function. §8 states the ID₁ result as it stands.

### 1.3 Reading paths

- **Type theorists:** §2, §4, §6, then §5.
- **Proof theorists:** §2, §3, §4.3, §4.8, §5, then §8.

§7 collects the relations used throughout; most misreadings come from
conflating two of them.

## 2. Presentations

### 2.1 The record

A presentation at universe level ℓ
([Presentation/CountableOrdinal](src/SPT/Cubical/OrdinalGeometry/Presentation/CountableOrdinal.agda),
record `CountableOrdinal𝒫`) has the data shape

```text
Σ (X : 𝒰ℓ) Σ (≈ < : X → X → 𝒰ℓ)
    Equivalence(≈) × Transitive(<) × Respects₂(<, ≈) × WellFounded(<)
  × Π x y. x < y + (x ≈ y + y < x)                              -- compare
  × Σ (e : ℕ → Maybe X) Π x. Σ n. Σ r. (e n ≡ just r) × (r ≈ x)  -- enum
```

Four features matter throughout.

- **Relations are type-valued.** Neither ≈ nor < is required to be
  proposition-valued, and distinct witnesses at the same endpoints remain
  distinct.
- **Comparison is a field.** `compare` returns one of x < y, x ≈ y, y < x,
  with its witness. Comparison inside one presentation is part of the data,
  not derived from the other fields.
- **Enumeration is partial.** `enum : ℕ → Maybe X` lets empty and finite
  presentations exist without a default point. Coverage (`covers`) returns
  an actual index and representative, up to ≈.
- **Extensionality is derived.** Irreflexivity, asymmetry, and
  incompatibility of ≈ with < follow from the fields. So does
  extensionality modulo ≈: if x and y have the same strict predecessors,
  then x ≈ y (`Presentation.≈↓→≈`, by `compare`). This is what makes the
  reflection of §4 extensional.

A presentation is not required to be a set. Its carrier is any small type,
and §6.2 measures the consequences.

### 2.2 Points as predecessor domains

- [Presentation/Principal](src/SPT/Cubical/OrdinalGeometry/Presentation/Principal.agda): the
  principal presentation with literal carrier Σ y. y < x. Nested restriction
  keeps the endpoint and the inner strict witness.
- [CountablyPresented/LowerCone](src/SPT/Cubical/OrdinalGeometry/Presentation/CountablyPresented/LowerCone.agda):
  the lower cone Σ y. y < x, for every countably presented geometry; at a
  presentation P it is the principal presentation above.
- [Presentation/LowerCone](src/SPT/Cubical/OrdinalGeometry/Presentation/LowerCone.agda):
  a second lower cone of a point of P, whose points are the occurrences of
  the enumeration filtered below x; the reflection of §4 uses it. The two
  cones are equivalent presentations
  ([LowerCone/Comparison](src/SPT/Cubical/OrdinalGeometry/Presentation/LowerCone/Comparison.agda):
  `equivalence`).
- [Presentation/Successor](src/SPT/Cubical/OrdinalGeometry/Presentation/Successor.agda),
  [Presentation/Sum](src/SPT/Cubical/OrdinalGeometry/Presentation/Sum.agda) and
  [Sum/Indexed](src/SPT/Cubical/OrdinalGeometry/Presentation/Sum/Indexed.agda): P + 1,
  P + Q, and ordered sums over the points of an exact countable ordinal.
- [Presentation/Normalization](src/SPT/Cubical/OrdinalGeometry/Presentation/Normalization.agda):
  classes represented by their least enumeration indices, so equivalent
  points become equal codes.
- [ExactOrder/Base](src/SPT/Cubical/OrdinalGeometry/ExactOrder/Base.agda): exact orders,
  whose comparison returns actual identity, so a dependent family can stay
  in its exact fiber.

### 2.3 Maps of presentations

[Presentation/Map](src/SPT/Cubical/OrdinalGeometry/Presentation/Map.agda) defines:

- **embeddings**: maps preserving ≈ and <;
- **initial maps** (P ≤ Q): embeddings whose image is closed downward;
- **segments** (P < Q): bounded strict embeddings (below) whose image covers
  the whole cone below the ceiling, so that P is the principal segment of Q
  below it.

[Presentation/CountableOrdinal](src/SPT/Cubical/OrdinalGeometry/Presentation/CountableOrdinal.agda)
adds:

- **bounded strict embeddings** P ≺𝒫 Q: embeddings with a selected ceiling
  above the whole image, which need not be a segment;
- **presentation equivalence** P ≃𝒫 Q: maps both ways with inverse laws
  modulo ≈.

Here *embedding* means order embedding modulo ≈. It is not an embedding in
the HoTT sense: the projection ∂ₚx → X_P has fibers that are not
propositions in general.

[Arithmetic/Ambient](src/SPT/Cubical/OrdinalGeometry/Arithmetic/Ambient.agda) fixes one
presentation W and reads each point x as the ordinal ∂x, with x < y read as
the principal cone ∂x ⊂ ∂y. This is the *ambient* reading used in §5.

## 3. The countable diagonal

All in [Presentation/CountableOrdinal](src/SPT/Cubical/OrdinalGeometry/Presentation/CountableOrdinal.agda).

- **Well-foundedness of ≺𝒫.** The bounded-embedding relation is well
  founded on the type of all small presentations (`Embedding.wf`). The
  proof recurses along the selected ceilings, so the ceiling is the datum
  that makes the comparison of whole presentations well founded.
- **The diagonal.** For every literal family f : ℕ → Pres, the ordered sum
  of successors D = Σₙ (f n + 1) satisfies f n ≺𝒫 D for every n
  (`Diagonal.upper`). No choice is used: every f n is already a complete
  presentation with its enumeration and coverage.
- **Noncoverage.** No family covers all presentations literally
  (`Exact.noEnumeration`), none covers them up to ≃𝒫
  (`Equivalent.noEnumeration`), and none is cofinal for P ≼𝒫 Q, defined as
  (P = Q) + (P ≺𝒫 Q) (`Cofinality.noFamily`). Each time, the alleged family
  applied to its own diagonal produces a strict cycle.
- **The retained ω₁ geometry.** `Boundary.Point` is the type of
  presentations with one more point, `boundary`, and every presentation
  lies immediately below it. A geometry `𝒫ω₁𝒢` is a point u_G above every
  presentation whose strict predecessors are exactly the presentations,
  together with the diagonal and the noncoverage theorem. A position is a
  presentation with its route below that point, Pos(G) = Σ P. ι(P) < u_G.
  The canonical inhabitant is `ω₁.Geometry.canonical`, with u_G =
  `boundary`.

The diagonal is an upper bound, not a least one. Least bounds need either a
chain or a common ambient (§5).

[Presentation/Limit](src/SPT/Cubical/OrdinalGeometry/Presentation/Limit.agda) builds the
least boundary of a countable chain of initial maps: every initial map into
a presented bound extends uniquely. Its
[Discriminator](src/SPT/Cubical/OrdinalGeometry/Presentation/Limit/Discriminator.agda)
defines `possible s`, which has a point exactly when the Boolean stream s
hits true. Every LPO discriminator in §5 goes through it.

## 4. Reflection and ω₁

The modules of this section and of §6 are Cubical (`--cubical`) and live
in [OrdinalGeometry/Cubical](src/SPT/Cubical/OrdinalGeometry/Cubical/); everything else is
`--cubical-compatible` and uses no univalence.

### 4.1 Order types

[Cubical/Reflection/OrderType](src/SPT/Cubical/OrdinalGeometry/Cubical/Reflection/OrderType.agda)
assigns to each presentation a Cubical well-order (`orderType`):

```text
ord(P)  =  (X_P / ≈ₚ ,  [x] < [y] := ‖x <ₚ y‖)
```

The carrier is a set quotient and strictness is truncated. The relation
descends, stays transitive and well founded, and is extensional (by
`≈↓→≈`). A presentation equivalence induces an equivalence of
well-orders, and so a path.

- Lower cones and successors commute with reflection:
  [Reflection/LowerCone](src/SPT/Cubical/OrdinalGeometry/Cubical/Reflection/LowerCone.agda),
  [Reflection/Successor](src/SPT/Cubical/OrdinalGeometry/Cubical/Reflection/Successor.agda).
- Initial maps are exactly simulations, and segments exactly bounded
  simulations:
  [Reflection/Simulation](src/SPT/Cubical/OrdinalGeometry/Cubical/Reflection/Simulation.agda)
  and its [Converse](src/SPT/Cubical/OrdinalGeometry/Cubical/Reflection/Simulation/Converse.agda),
  through canonical representatives
  ([Reflection/Representative](src/SPT/Cubical/OrdinalGeometry/Cubical/Reflection/Representative.agda)).
  Reflection also reflects equivalence (`Converse.equivalence`).

### 4.2 The construction of ω₁

For every retained geometry G,
[Cubical/OmegaOne/Base](src/SPT/Cubical/OrdinalGeometry/Cubical/OmegaOne/Base.agda)
forms the supremum indexed by the complete positions:

```text
ω₁^G  =  sup (q : Pos(G)), ord(π₁ q)   :   Woset(ℓ+1, ℓ)
```

The carrier lies one universe up and the relation stays at ℓ. Every
reflected presentation lies strictly below it:
ord(P) ≺ ord(P + 1) ≺ ω₁^G.

### 4.3 Cut, leastness and uniqueness

Write Presented(α) = ‖Σ P. ord(P) ≃ α‖, the proposition that α is merely
presented. The following are constructive, with no choice and no excluded
middle.

- **Cut.** (α ≺ ω₁^G) ≃ Presented(α), for well-orders α at any carrier
  universe with relation at ℓ
  ([OmegaOne/Cut](src/SPT/Cubical/OrdinalGeometry/Cubical/OmegaOne/Cut.agda):
  `strict-cut`;
  [Specification](src/SPT/Cubical/OrdinalGeometry/Cubical/OmegaOne/Specification.agda):
  `cut-strict-equivalence`).
- **Leastness.** Any K with ord(P) ≺ K for every presentation P satisfies
  ω₁^G ≼ K (`large-least`).
- **Unpresentability.** ¬ Presented(ω₁^G)
  (`not-presented`).
- **Uniqueness.** The cut specification determines ω₁: Cut(H) ≃ (H = ω₁^G),
  and the type of well-orders satisfying it is contractible
  (`isOmegaOneCut≃path`,
  `ω₁-cutObject-isContr`). Any two geometries give path-equal
  well-orders (`pathᴳ`).

Uniqueness concerns the well-orders, not the geometries that produce them;
§6.2 shows that distinct geometries remain distinct.

### 4.4 Countability and the Hartogs comparison

[Reflection/Woset](src/SPT/Cubical/OrdinalGeometry/Cubical/Reflection/Woset.agda) gives a
presentation to every small well-order with a partial enumeration and
strict trichotomy, with an equivalent order type. For such α,
(α ≺ ω₁) ≃ Countable(|α|), constructively.

[Hartogs/Base](src/SPT/Cubical/OrdinalGeometry/Cubical/Hartogs/Base.agda) builds an independent
well-order H_ℕ = Σ α. ‖|α| ↪ ℕ‖, with its own cut theorem
(`strict-cut`). Its comparison with ω₁
([OmegaOne/Hartogs](src/SPT/Cubical/OrdinalGeometry/Cubical/OmegaOne/Hartogs.agda),
[Hartogs/Uncountability](src/SPT/Cubical/OrdinalGeometry/Cubical/Hartogs/Uncountability.agda))
has explicit hypotheses:

| Hypotheses | Conclusion |
|---|---|
| none | the cut, leastness, uniqueness and unpresentability of ω₁; the cut of H_ℕ |
| excluded middle at ℓ | for small well-orders, lying below ω₁, being countable and merely embedding in ℕ coincide; ω₁^G ≃ H_ℕ, and the two are path-equal |
| propositional resizing from ℓ+1 to ℓ | the large carrier of H_ℕ does not merely embed in ℕ, which gives its full Hartogs specification |
| both of the above | the same nonembedding and Hartogs specification for every ω₁^G |
| excluded middle at ℓ+1 | the decisions and the resizing above, hence all of the above |

No countable choice is used in these comparisons.

### 4.5 Regularity

[OmegaOne/Regularity](src/SPT/Cubical/OrdinalGeometry/Cubical/OmegaOne/Regularity.agda)
states regularity (every ℕ-sequence of points has a strict upper bound) for
every H meeting the cut specification, so for ω₁^G.

- Regularity gives LPO (`lpo`). The points of possible s + 1 and of 1
  already need a common strict bound. No choice is used, because these
  points come with their presentations.
- LPO, together with presentations of the segments below the points, gives
  the bound (`regular`).
- LPO and countable choice give regularity (`choice`, `omega-one-choice`).

Whether regularity needs choice beyond LPO is open. For sequences given by
presentations, bounding by ≺𝒫 is free (the diagonal), while bounding by
segments costs exactly LPO.

### 4.6 Size, and the ordinal of ordinals

The carrier of ω₁^G lies one universe above the presentations, because
ω₁^G is a supremum indexed by all of them. Up to equivalence ω₁ is small,
and it does not depend on the universe level
([OmegaOne/Small](src/SPT/Cubical/OrdinalGeometry/Cubical/OmegaOne/Small.agda)). This is a
statement about the well-order. The geometry stays large: its points are
presentations, structures on arbitrary carriers, and those of the single
order type 1 already contain the pointed universe (§6.2). What makes ω₁
small is that `ord` sees presentations only up to equivalence.

- **Boolean orders.** A Boolean order
  ([ExactOrder/Boolean](src/SPT/Cubical/OrdinalGeometry/ExactOrder/Boolean.agda)) is a
  decidable set of natural numbers with a Boolean strict order that is
  transitive, well founded and trichotomous. Boolean orders form a small
  type. Every presentation, at every level, is equivalent to the
  presentation of one, whose points are the least enumeration indices of
  its classes
  ([Presentation/Normalization/Boolean](src/SPT/Cubical/OrdinalGeometry/Presentation/Normalization/Boolean.agda):
  `normal`, `equivalence`).
- **ω₁ is small.** Let Ω be the supremum of the order types of all Boolean
  orders, a well-order in the lowest universe. Then ω₁(ℓ) ≃ Ω for every ℓ
  (`small`), so ω₁(ℓ) ≃ ω₁(ℓ′) (`level`). Raised to level ℓ, Ω lies above
  every presentation of that level and each of its principal segments is
  presented, so leastness and the cut place it on both sides of ω₁(ℓ).
- **The ordinal of ordinals.** Ord(ℓ) is the well-order of the
  well-orders of level ℓ under ≺: the cubical library's `isWoset≺`, the
  ordinal of ordinals of the HoTT book (§10.3) and OO of TypeTopology.
  Every W in Ord(ℓ) is equivalent to Ord(ℓ) ↓ W
  ([Reflection/Ordinals](src/SPT/Cubical/OrdinalGeometry/Cubical/Reflection/Ordinals.agda):
  `lowerset`). So ω₁(ℓ) is a principal segment of Ord(ℓ) (`principal`).
  The well-orders below its point are exactly the merely presented ones
  (`below`), and the type of points of Ord(ℓ) with that property is
  contractible (`cutPoint-isContr`).

Cubical's ordinal of ordinals is TypeTopology's OO
([TypeTopology/OrdinalOfOrdinals](src/SPT/Cubical/OrdinalGeometry/Cubical/TypeTopology/OrdinalOfOrdinals.agda)).
`Ordinals.OrdinalOfOrdinals` is instantiated with TypeTopology's
univalence, which holds in Cubical Agda (§6.1).

- **The same ordinal.** toOrdinal is an equivalence of types from the
  well-orders of level ℓ to TypeTopology's ordinals (`ordinals`). It sends
  ≺ to ⊲ and back (`preserves`, `reflects`), so it is an order equivalence
  Ord(ℓ) ≃ₒ OO ℓ (`equivalence`). Hence Ord(ℓ) = OO ℓ as TypeTopology
  ordinals (`identity`), and segments of Ord(ℓ) are segments of OO ℓ
  (`segment-OO`).
- **ω₁ in OO.** ω₁(ℓ) is the segment of OO ℓ below the ordinal of Ω′
  (`omega-one`), so ω₁(ℓ) ⊲ OO ℓ (`principal`). The TypeTopology ordinals
  below that point are exactly the merely presented ones (`below`).

### 4.7 Heights, and the rank of their ordinal of ordinals

The ω₁ geometry has an analogue one level up, built from heights instead
of presentations. A closed height of level ℓ is a closed Core tree whose
nodes are labelled by types of level ℓ and branch over their labels. These
closed heights are not the heights with stage nodes of §8.

- **Geometry.** [Height/Simulation](src/SPT/Cubical/OrdinalGeometry/Height/Simulation.agda)
  compares closed trees: ancestry ◃ and <, the simulation order ⊑ and ⊏,
  and the shape equivalence ≅. [Height/Ordinals](src/SPT/Cubical/OrdinalGeometry/Height/Ordinals.agda)
  defines Ord(ℓ), the height of level ℓ + 1 whose children are exactly
  the heights of level ℓ.
  - Every height is a child of Ord(ℓ) (`upper`), and Ord(ℓ) is least
    among heights above all of them (`least`).
  - No small family of heights is cofinal (`not-cofinal`), so Ord(ℓ) lies
    below no height of level ℓ (`not-small`). This is Burali-Forti for
    heights, and it is constructive.
  - Every small well-founded relation has a canonical height (`whole`).
- **Rank.** [Cubical/Height/Rank](src/SPT/Cubical/OrdinalGeometry/Cubical/Height/Rank.agda)
  sends a height to a well-order of its level,
  rank (node A f) = sup (a : A). rank (f a) + 1, using the supremum of
  [Reflection/Supremum/Family](src/SPT/Cubical/OrdinalGeometry/Cubical/Reflection/Supremum/Family.agda).
  - A child's rank lies below its parent's (`child`). The rank of a node
    lies below every well-order, of any level, that lies strictly above
    the ranks of its children (`least`).
  - Every well-order is the rank of its canonical height (`canonical`).
  - A height and its lift one level up have equivalent ranks (`lifted`).
  - Shape-equivalent heights have equivalent ranks (`rank-≅`).
- **The ordinal of ordinals.** The rank of the geometric Ord(ℓ) is
  Cubical's Ord(ℓ) of §4.6
  ([Cubical/Height/Ordinals](src/SPT/Cubical/OrdinalGeometry/Cubical/Height/Ordinals.agda):
  `ordinals`). Hence it is also TypeTopology's OO ℓ (`identity`).
  - The rank of each child is a small well-order, the point of Ord(ℓ) of
    which it is the segment.
  - Each small well-order is the rank of a child: its canonical height.
  - Both inequalities come from `segments→simulation`
    ([Reflection/Ordinals](src/SPT/Cubical/OrdinalGeometry/Cubical/Reflection/Ordinals.agda)),
    which builds a simulation between well-orders of any two levels from
    principal segments. Antisymmetry of ≼ gives the equivalence.

As for ω₁, the well-order of the geometry is reached only through
reflection. Unlike ω₁, both the geometry and its well-order are large.
No height of level ℓ bounds Ord(ℓ) (`not-small`). By the Burali-Forti
argument of the HoTT book (§10.3), which is not formalized here, Cubical's
Ord(ℓ) is not equivalent to a well-order of level ℓ. Rank forgets the
labels: its fibers over successors contain the merely inhabited types
(§6.2).

### 4.8 Inaccessible points, and the comparison with Mahlo cardinals

The universe of level ℓ is a parent whose codes are its own types
([Core/Mahlo/Ambient](src/SPT/Cubical/Core/Mahlo/Ambient.agda)). A *reflection* of an
operator Ψ on families of types is a type of codes with a decoding into
types. Its codes are closed under the type formers (empty, unit, 𝟐, ℕ, Σ,
Π, W, identity) and under Ψ
([Core/Mahlo/Specification](src/SPT/Cubical/Core/Mahlo/Specification.agda),
[Core/Mahlo/Decoding](src/SPT/Cubical/Core/Mahlo/Decoding.agda)). A *reflector* reflects
every operator; this is the Mahlo rule. Agda provides a reflector by
induction–recursion. This release takes it as a parameter and uses no
induction–recursion.

- **Geometry.** [Height/Reflection](src/SPT/Cubical/OrdinalGeometry/Height/Reflection.agda):
  the *child trees* of a reflection R are the trees whose nodes are
  labelled by child codes. Its boundary Ω_R is the node whose children
  are the child trees. Ω_R lies above every child tree, is regular for
  families indexed by child types, and is closed under Ψ.
  [Height/Ordinals/Mahlo](src/SPT/Cubical/OrdinalGeometry/Height/Ordinals/Mahlo.agda):
  reflecting Ψ paired with the labels of a height t gives a point closed
  under Ψ and above t, strictly below Ord(ℓ) (`mahlo`, `between`).
- **Ranks.** [Cubical/Height/Reflection](src/SPT/Cubical/OrdinalGeometry/Cubical/Height/Reflection.agda):
  λ_R, the rank of Ω_R, has a constructive cut: α ≺ λ_R exactly when α
  is, merely, the rank of a child tree (`cut`).
- **The classical side.**
  [Reflection/Ordinals/Lower](src/SPT/Cubical/OrdinalGeometry/Cubical/Reflection/Ordinals/Lower.agda)
  takes a property of small well-orders closed downward and gives the
  initial segment of Ord(ℓ) of its members, with its cut and uniqueness.
  [Hartogs/Universe](src/SPT/Cubical/OrdinalGeometry/Cubical/Hartogs/Universe.agda)
  applies it to a family of types D to obtain the Hartogs well-order
  H(D) = Σ α. ‖Σ c. |α| ↪ D c‖ (`Hartogs`, `cut`, `unique`). For the
  single type ℕ this is H_ℕ of §4.4.
  [Hartogs/Cardinal](src/SPT/Cubical/OrdinalGeometry/Cubical/Hartogs/Cardinal.agda) states
  the classical notions for small well-orders: cardinal, uncountable,
  regular, strong limit (with power sets |α| → 𝟐) and inaccessible. It
  also states Mahlo in the function form for Ord(ℓ) (`MahloOrdinals`).
- **The comparison.** [Cubical/Height/Hartogs](src/SPT/Cubical/OrdinalGeometry/Cubical/Height/Hartogs.agda):
  under excluded middle, α ≺ λ_R exactly when |α| merely embeds into a
  child type (`cut`). Hence λ_R ≃ H(U_R) for the child universe U_R
  (`equivalence`), as ω₁ ≃ H_ℕ in §4.4. The rank of a child tree embeds
  into a power code, by induction on the tree. Conversely, a well-order
  that embeds into a child type is the rank of a child tree labelled by
  subset codes. With choice λ_R is regular, and so inaccessible
  (`inaccessible`).
- **Mahlo.** [Cubical/Height/Mahlo](src/SPT/Cubical/OrdinalGeometry/Cubical/Height/Mahlo.agda):
  given a reflector, excluded middle and choice, every f : Ord ℓ → Ord ℓ
  has an inaccessible λ_R above every β with α ≺ λ_R → f α ≺ λ_R
  (`mahlo`). The reflected operator lists, for every member of its
  argument and every Boolean-coded well-order W on a subset of it
  ([Hartogs/Coded](src/SPT/Cubical/OrdinalGeometry/Cubical/Hartogs/Coded.agda)), the
  carrier of f W. Classically, inaccessible closure points of every f
  characterize the Mahlo cardinals among the regular ones.

| Hypotheses | Conclusion |
|---|---|
| none | the cut of λ_R by child trees; the cut and uniqueness of H(D) |
| a reflector | closed inaccessible points of the geometry above every height, strictly below Ord(ℓ) |
| excluded middle at ℓ | λ_R ≃ H(U_R), and λ_R is an uncountable strong limit cardinal |
| excluded middle and choice at ℓ | λ_R is regular, hence inaccessible |
| a reflector, excluded middle and choice at ℓ | Ord(ℓ) is Mahlo in the function form |

## 5. The KNFX table by boundary

### 5.1 Where the rows live

Each row is stated on the object that carries its datum:

- **an ambient W**, one presentation whose points are read as the ordinals
  ∂x ([Arithmetic/Ambient](src/SPT/Cubical/OrdinalGeometry/Arithmetic/Ambient.agda)), where
  comparison, joins, decisions, subtraction and division hold outright;
- **presentations under initial maps and segments**, where zero,
  successors, limits of chains, classification as retained data, and the
  arithmetic hold
  ([Arithmetic](src/SPT/Cubical/OrdinalGeometry/Arithmetic/) and
  [Presentation/Limit](src/SPT/Cubical/OrdinalGeometry/Presentation/Limit.agda));
- **reflected order types**, where suprema of small families and the
  reflected classification hold
  ([Cubical/Reflection/Supremum](src/SPT/Cubical/OrdinalGeometry/Cubical/Reflection/Supremum.agda),
  [Cubical/Reflection/Classification](src/SPT/Cubical/OrdinalGeometry/Cubical/Reflection/Classification.agda)).

The arithmetic follows the KNFX specifications (zero, successor and limit
clauses, quantified over every zero, successor and supremum).

### 5.2 The table

"Without the datum" means the row asked of all presentations at once.
→ LPO names the discriminator deriving LPO, and LPO → names the converse
([Arithmetic/Comparison](src/SPT/Cubical/OrdinalGeometry/Arithmetic/Comparison.agda)).
Discriminators are in
[Arithmetic/Ambient/Discriminator](src/SPT/Cubical/OrdinalGeometry/Arithmetic/Ambient/Discriminator.agda)
unless another module is named.

| # | Row | Holds with its datum | Without the datum |
|---|---|---|---|
| 1 | x < y ≤ z → x < z | points; presentations (`Map.along`, `Map.bounded`) | — |
| 2 | x ≤ y < z → x < z | ambient (`Ambient.along`); a strict bound, or a segment when ≤ is split (`Characterization.strictly`, `segment`) | → LPO (`along`); LPO → (`Comparison.along`) |
| 3 | well-founded | `<-wf`; ≺𝒫 (`Embedding.wf`); proper segments of domains in W (`Ambient.wf`) | — |
| 4 | extensional | points (`≈↓→≈`); presentations (`Map.antisymmetry`); domains (`Cone.injective`) | — |
| 5 | zero, successors | `Characterization` (zero; P + 1 the strong successor; both unique); P < Q ⇔ P + 1 ≤ Q, monotone for ≃𝒫 and ≺𝒫 (`Successor`); for ≤ on domains in W (`Ambient.successor-initial`) | monotone for ≤ and <: → LPO ([`Successor.Discriminator`](src/SPT/Cubical/OrdinalGeometry/Arithmetic/Successor/Discriminator.agda): `initial`, `segment`); LPO → (`Comparison.successor-initial`, `successor-segment`) |
| 6 | binary joins | ambient (`Ambient.join`) | → LPO (`join`); LPO → (`Comparison.join`) |
| 7 | limits of increasing sequences | `Characterization.Increasing`; chains (`Presentation.Limit`); ascending points of W (`Ambient.ascending`) | — |
| 8 | suprema of small families | reflected: least among well-orders (`Reflection.Supremum`: `supremum`, `upper`, `least`, `least-initial`), also among TypeTopology's ordinals; presented for chains and for families in an ambient (`Reflection.Supremum.Chain`, `Enumerated`), all strictly below ω₁ | a merely presented supremum of every ℕ-family ⇔ LPO (`Reflection.Supremum.Discriminator`, `Reflection.Supremum.Comparison.strength`); suprema among presentations: → LPO (`supremum`), LPO → (`Comparison.supremum`); strict upper bounds: → LPO ([`Comparison.Discriminator`](src/SPT/Cubical/OrdinalGeometry/Arithmetic/Comparison/Discriminator.agda)`.bound`), LPO → (`Comparison.bound`) |
| 9 | classification | retained data (`Classification.Classified`): ∅, P + 1 and limits classified, preserved by +, ·, ω^ (`sum`, `product`, `power`), `cofinal`; reflected (`Reflection.Classification.classified`); pointwise, local and inductive refinements ([`Classification.Pointwise`](src/SPT/Cubical/OrdinalGeometry/Arithmetic/Classification/Pointwise.agda), [`Local`](src/SPT/Cubical/OrdinalGeometry/Arithmetic/Classification/Local.agda), [`Induction`](src/SPT/Cubical/OrdinalGeometry/Arithmetic/Classification/Induction.agda)) | → LPO ([`Classification.Discriminator`](src/SPT/Cubical/OrdinalGeometry/Arithmetic/Classification/Discriminator.agda): `inhabited`, `classified`, `shaped`) |
| 10 | addition | `Arithmetic.Addition`; unique at hereditary arguments ([`Uniqueness`](src/SPT/Cubical/OrdinalGeometry/Arithmetic/Uniqueness.agda)`.unique-addition`); commutes with TypeTopology's +ₒ (`TypeTopology.Arithmetic`) | — |
| 11 | multiplication | `Arithmetic.Multiplication`; unique (`Uniqueness.unique-multiplication`); commutes with ×ₒ | — |
| 12 | exponentiation | base ω (`Arithmetic.Exponential`, `Operation.Exponential`, `ExactOrder.Exponential`); unique (`Uniqueness.unique-exponential`); reflected specification (`TypeTopology.Arithmetic.Exponential`) | — |
| 13 | subtraction | ambient (`Ambient.subtract`); along an initial map with decided image (`Subtraction`); reflected (`Remainder.subtraction`) | → LPO (`Subtraction.Discriminator.remainder`); LPO → (`Comparison.decided`, `subtract`) |
| 14 | division | ambient (`Ambient.divide`, `place`); along a placement, unique (`Division`); reflected (`Remainder.division`) | → LPO ([`Division.Discriminator`](src/SPT/Cubical/OrdinalGeometry/Arithmetic/Division/Discriminator.agda)`.division`) |
| 15 | x < ω decidable | ambient (`Ambient.below?`, `finite?`) | → LPO (`finite`); LPO → (`Comparison.finite`) |
| 16 | x < y decidable | ambient (`Ambient.decidable`) | → LPO (`decidable`); LPO → (`Comparison.decidable`) |
| 17 | ≤ splits | ambient (`Ambient.split`) | → LPO (`split`); LPO → (`Comparison.split`) |
| 18 | trichotomy | ambient (`Ambient.compare`) | → LPO (`trichotomy`); LPO → (`Comparison.trichotomy`) |

On the reflected side, rows 2, 13 and 15–18, asked of the order types of
all presentations, also give LPO
([Reflection/Simulation/Discriminator](src/SPT/Cubical/OrdinalGeometry/Cubical/Reflection/Simulation/Discriminator.agda)).
For all of Ord these rows are equivalent to excluded middle (KNFX).

[Comparison/Strength](src/SPT/Cubical/OrdinalGeometry/Arithmetic/Comparison/Strength.agda)
packages both directions. Asked of all presentations, each of the rows 2,
5, 6, 8, 13 and 15–18 is equivalent to LPO, and so are comparability, the
decidability of ≤ and of ≃𝒫, and strict upper bounds of ℕ-families
(`comparable`, `initial`, `equivalent`, `bound`). The equivalences are
stated at level zero, where the discriminators are; the positive direction
holds at every level. Rows 9 and 14 give LPO without their data, and their
converses are not addressed.

[Characterization/Strength](src/SPT/Cubical/OrdinalGeometry/Arithmetic/Characterization/Strength.agda)
gives the weaker principles. Deciding whether P is zero is exactly WLPO
(`zero-strength`); deciding P ≃𝒫 ω is exactly LPO (`omega-strength`), and
so is deciding P ≃𝒫 Q (`Comparison.Strength.equivalent`). Stability of
P ≃𝒫 ω + 1 under double negation lies between MP and LPO (`stable`); its
exact strength is not determined.

[OrdinalGeometry/Arithmetic.agda](src/SPT/Cubical/OrdinalGeometry/Arithmetic.agda) restates
the whole table as two records. `Rows W`, inhabited by `rows W` for every
presentation W, holds the order rows for the ordinals of W, each with its
further datum in the type of its field. `Strength`, inhabited by
`strength`, is the column without the datum. Rows 10–12 are `addition`,
`multiplication` and `exponential`, with `unique-addition`,
`unique-multiplication` and `unique-exponential`.

### 5.3 Why LPO is enough for comparison

[ExactOrder/Comparison](src/SPT/Cubical/OrdinalGeometry/ExactOrder/Comparison.agda) proves
that under LPO any two exact orders are comparable (`comparable`). The
comparison is Cantor's: the Boolean relation "the lower cones of x and y
are matched",

```text
x ∼ y  =  (∀ a < x. ∃ b < y. a ∼ b)  ∧  (∀ b < y. ∃ a < x. a ∼ b)
```

defined by recursion along both accessibility proofs. LPO decides each
bounded quantifier through the enumerations, so nothing is chosen, and one
side of the matching is exhausted. Comparing two recursive well-orders is
not an arithmetical problem, while one use of LPO decides one Σ⁰₁
question. LPO suffices here because it is applied at every step of a
transfinite recursion along the orders. Normalization carries the result
to all presentations (`Comparison.comparable`).

### 5.4 What the table shows

Every row holds with its datum. Asked without it, each of the rows 2, 5, 6,
8, 13 and 15–18 is exactly LPO, and rows 9 and 14 give LPO. This agrees with
the KNFX theorems rather
than contradicting them: those theorems concern one carrier asked to carry
every row at once, and here no carrier is asked to. What the geometry adds
is the location of each trade-off at a specific datum, together with a proof
that the datum cannot be removed for less than LPO.

## 6. TypeTopology, and what reflection forgets

### 6.1 The bridge

[Cubical/TypeTopology/Bridge](src/SPT/Cubical/OrdinalGeometry/Cubical/TypeTopology/Bridge.agda)
maps Cubical well-orders to the ordinal record of TypeTopology's
`Ordinals.Type`, keeping carrier and relation unchanged. Only
equality-valued laws and accessibility witnesses cross the library
boundary. On top of it:

- simulations correspond
  ([TypeTopology/Simulation](src/SPT/Cubical/OrdinalGeometry/Cubical/TypeTopology/Simulation.agda)),
  and the suprema of §5 are suprema among TypeTopology's ordinals
  ([Reflection/Supremum/TypeTopology](src/SPT/Cubical/OrdinalGeometry/Cubical/Reflection/Supremum/TypeTopology.agda));
- reflection commutes with TypeTopology's arithmetic: (P + Q)′ ≃ P′ +ₒ Q′,
  (P + 1)′ ≃ P′ +ₒ 𝟙ₒ and (P · Q)′ ≃ P′ ×ₒ Q′
  ([TypeTopology/Arithmetic](src/SPT/Cubical/OrdinalGeometry/Cubical/TypeTopology/Arithmetic.agda)),
  with exponentiation, subtraction and division in its
  [Exponential](src/SPT/Cubical/OrdinalGeometry/Cubical/TypeTopology/Arithmetic/Exponential.agda)
  and [Remainder](src/SPT/Cubical/OrdinalGeometry/Cubical/TypeTopology/Arithmetic/Remainder.agda).

Function extensionality and univalence come from Cubical
([TypeTopology/FunExt](src/SPT/Cubical/OrdinalGeometry/Cubical/TypeTopology/FunExt.agda),
[TypeTopology/Univalence](src/SPT/Cubical/OrdinalGeometry/Cubical/TypeTopology/Univalence.agda)).
TypeTopology's `idtoeq` is inverted by sending an equivalence to its
Cubical `ua`, read in TypeTopology's identity type, so `Univalence` holds
and TypeTopology's univalent ordinal theory can be instantiated; §4.6
uses it for OO.

TypeTopology's `Ordinals.Arithmetic` cannot be checked with Agda 2.8.0:
its dependency `Naturals.Addition` binds the builtin NATPLUS a second
time, after `Agda.Builtin.Nat`, whose natural numbers TypeTopology uses.
So +ₒ, ×ₒ and 𝟙ₒ are built from `Ordinals.WellOrderArithmetic`, as
`Ordinals.Arithmetic` builds them. The TypeTopology files used are copied
into [TypeTopology/](src/SPT/Cubical/TypeTopology/). Two of them are shortened so that
nothing imports `Naturals.Addition`: `Ordinals.OrdinalOfOrdinals` loses
one lemma, and `UF.SIP-Examples` one example. [NOTICE](NOTICE) lists every
change.

### 6.2 What reflection forgets

The reflection is faithful on order types. These theorems measure how much
it forgets.

- **Geometries.**
  [Fiber/Geometry](src/SPT/Cubical/OrdinalGeometry/Cubical/Fiber/Geometry.agda):
  two geometries that differ only in their selected diagonal are
  path-distinct, while §4.3 makes their ω₁ path-equal. So G ↦ ω₁^G is not
  an embedding.
- **Positions.**
  [Fiber/Position](src/SPT/Cubical/OrdinalGeometry/Cubical/Fiber/Position.agda)
  and [Fiber/Postcomposed](src/SPT/Cubical/OrdinalGeometry/Cubical/Fiber/Postcomposed.agda):
  for fixed G, let q_G send a position to the order type of its
  presentation. The fiber of q_G over the one-point order contains the
  pointed small universe 𝒰_{ℓ,∗} = Σ T. T as a split retract. The same holds
  for the fibers of a ∘ q_G for every map a out of well-orders, with no
  condition on a. The mechanism is simple: a pointed type (T, t₀) presents
  the one-point order, with carrier T, every two points equivalent, empty
  strict order, and t₀ enumerated at every index; recovery reads the
  carrier and the zeroth entry. Pointed univalence then carries the pointed
  automorphisms of T into loops of the fiber
  ([PointedUnivalence](src/SPT/Cubical/OrdinalGeometry/Cubical/Fiber/Postcomposed/PointedUnivalence.agda),
  [Automorphism](src/SPT/Cubical/OrdinalGeometry/Cubical/Fiber/Postcomposed/Automorphism.agda)).
  Higher carriers are not needed for this. For the set T = 𝟐 × 𝟐, pointed
  at (false, false), swapping the two coordinates already gives a
  nontrivial loop, so the fiber is not a set and q_G is not an embedding
  (`positionFiber-not-set`, `projection-not-embedding`).
- **Unbounded higher structure.** With T = 𝟐 × Πₙ K(ℤ, n), every
  level-zero geometry G has one fixed point in the space of presentations
  of a principal segment of ω₁^G equivalent to 1. It carries a nontrivial
  cell cₙ ∈ Ωⁿ⁺¹ for every n, so that space has no finite h-level
  ([Fiber/Principal/Unbounded](src/SPT/Cubical/OrdinalGeometry/Cubical/Fiber/Principal/Unbounded.agda):
  `not-finite-hlevel`). The same holds for every
  postcomposed position fiber
  ([Fiber/Postcomposed/Unbounded](src/SPT/Cubical/OrdinalGeometry/Cubical/Fiber/Postcomposed/Unbounded.agda):
  `fiber-not-finite-hlevel`).
- **Truncation.** For level-zero G, that space of presentations is not a
  set, while its propositional truncation `MerelyPresented` is
  contractible, so the truncation map is not an embedding
  ([Fiber/Principal/Loop](src/SPT/Cubical/OrdinalGeometry/Cubical/Fiber/Principal/Loop.agda):
  `not-set`, `merelyPresented-isContr`, `truncation-not-embedding`).
  Truncating is exactly the step that loses this data.
- **Heights.** Rank (§4.7) forgets in the same way, with labels in place
  of presentations ([Fiber/Height](src/SPT/Cubical/OrdinalGeometry/Cubical/Fiber/Height.agda)).
  For every well-order α, the fiber of rank over α + 1 contains the merely
  inhabited types Σ A. ∥A∥ as a split retract. A merely inhabited type A
  goes to the node labelled A whose children are all the canonical height
  of α, which has rank α + 1 (`copies-rank`). Recovery reads the root
  label, which is merely inhabited because the path places the top point
  of α + 1 in the rank of the root. No base point is needed, so negation
  on 𝟐 already gives a nontrivial loop: the fiber is not a set and rank is
  not an embedding, at every level (`fiber-not-set`, `not-embedding`).
  Translations of Πₙ K(ℤ, n) give cells in every dimension, so the fiber
  has no finite h-level, and neither has rank as a map
  ([Fiber/Height/Unbounded](src/SPT/Cubical/OrdinalGeometry/Cubical/Fiber/Height/Unbounded.agda):
  `fiber-not-finite-hlevel`, `rank-not-finite-hlevel`). Over an empty
  well-order, by contrast, the fiber is contractible: the leaf is the only
  height of rank 0 (`empty-fiber`).
- **In TypeTopology's own terms.**
  [OmegaOneLoss](src/SPT/Cubical/OrdinalGeometry/Cubical/TypeTopology/OmegaOneLoss.agda),
  [PositionLoss](src/SPT/Cubical/OrdinalGeometry/Cubical/TypeTopology/PositionLoss.agda),
  [IdentityFiberLoss](src/SPT/Cubical/OrdinalGeometry/Cubical/TypeTopology/IdentityFiberLoss.agda),
  [HeightLoss](src/SPT/Cubical/OrdinalGeometry/Cubical/TypeTopology/HeightLoss.agda)
  and [Loss](src/SPT/Cubical/OrdinalGeometry/Cubical/TypeTopology/Loss.agda):
  the projections into TypeTopology's ordinals, from geometries, positions
  and heights, fail TypeTopology's own embedding predicate, measured in its
  own identity fibers. For heights the map is rank′(t) = toOrdinal(rank t).
  Since toOrdinal keeps the carrier, the retraction above carries over
  (`rankIdentityFiber-not-finite-TT-hlevel`, `rank′-not-TT-embedding`).

The reflected ordinal is a set. All of this higher structure lives in
spaces of presentations and in the labels of heights. They contain
pointed, or merely inhabited, types with their automorphisms and, since
neither presentations nor labels are required to be sets, cells of every
dimension. These theorems measure how much reflection and rank forget.
That the forgotten data matters is shown elsewhere: by the LPO boundaries
of §5, and by its use in the ID₁ bound of §8.

## 7. Relation dictionary

| Relation | Between | Witness | Module |
|---|---|---|---|
| x <ₚ y, x ≈ₚ y | points of P | fields of P, type-valued | [CountableOrdinal](src/SPT/Cubical/OrdinalGeometry/Presentation/CountableOrdinal.agda) |
| P ≤ Q | presentations | initial map | [Presentation/Map](src/SPT/Cubical/OrdinalGeometry/Presentation/Map.agda) |
| P < Q | presentations | segment: bounded embedding whose image is the cone below its ceiling | [Presentation/Map](src/SPT/Cubical/OrdinalGeometry/Presentation/Map.agda) |
| P ≺𝒫 Q | presentations | embedding with a ceiling above its image | [CountableOrdinal](src/SPT/Cubical/OrdinalGeometry/Presentation/CountableOrdinal.agda) |
| P ≃𝒫 Q | presentations | maps both ways, inverse modulo ≈ | [CountableOrdinal](src/SPT/Cubical/OrdinalGeometry/Presentation/CountableOrdinal.agda) |
| α ≼ β | well-orders | simulation | Cubical library; [Reflection/Simulation](src/SPT/Cubical/OrdinalGeometry/Cubical/Reflection/Simulation.agda) |
| α ≺ β | well-orders | bounded simulation, a principal segment | Cubical library; [Reflection/Simulation](src/SPT/Cubical/OrdinalGeometry/Cubical/Reflection/Simulation.agda) |

The checked bridges are: ≤ corresponds to ≼, and < to ≺, through
reflection in both directions (§4.1). ≺𝒫 is different from <, since a
bounded embedding need not be a segment. Bounding a sequence by ≺𝒫 is free
(the diagonal); bounding it by segments is exactly LPO.

## 8. Toward ordinal analysis: ID₁

This section describes Part II. Its modules are in the main development
(†) and are named without links.

### 8.1 Heights and their readings

Heights of infinitary derivations are *open heights* (`OpenHeight.Base` †):
well-founded trees whose ordinary nodes branch over the points of a
countable index ordinal. A *stage node* `stage H m` gives a height H P to
every presentation P, monotonically along embeddings. The stage node takes
the place where a classical analysis has Ω. It is read at a level and never
as a whole.

The reading of a height t at a level L, itself a presentation, is a
presentation `read t L` (`OpenHeight.Reading` †), defined by structural
recursion on t and L:

- a node over I reads as L + (Σᵢ (step (f i) L + 1))·ω + Σ_c (iterate c + 1);
- a stage node reads as L + Σ_c (read (H (∂_L c)) L + 1).

Here c ranges over the normalized points of L, so a stage node is only ever
sampled at the cones of the current level. `step s L = read s (read s L + 1)`
reads s at the level its own reading reaches, and the iterate runs along
the points of L.

### 8.2 The calculus and its evaluation

The infinitary calculus with stages (`Tait.Inductive.Base` †) has a stage
rule for a cedent containing n ∉ I. It has one premise for every
presentation P, at height H P, deriving the cedent together with the staged
formula n ∉ I_P. The rule also keeps the bound `stage H m ⊴ t`.

`Tait.Inductive.Evaluation` † evaluates a derivation with literal cuts at
height t, at a level V, into evidence at height `read t V`. At a stage
rule, n ∉ I is refuted by evidence for n ∈ I that already lies in a cone of
V. Boundedness (`Tait.Inductive.Boundedness` †) turns that evidence into
evidence for n ∈ I at the stage given by the cone, at the same height,
which refutes the staged formula of the premise at that stage. Only that
premise is evaluated, and its height embeds into `read t V` through the
stage node and the retained bound. An upright cedent (no negative literal
of the predicate) derived with no staged formulas obtains a positive
derivation at height `read t ∅` (`placed`).

### 8.3 The upper bound

`Theories.ID.Upper` † and `Theories.ID.Uniform` †: every ID₁ derivation of a
cedent related to an upright closed cedent Δ gives a cut-free positive
derivation of Δ at a presented height strictly below one presented ordinal
O, in the sense of ≺𝒫. O is the closure of the readings of a sequence of
universal heights. The scheme-free O of `Uniform` receives the bound of
every positive scheme d (O d ↪ O).

**No ordinal notation containing Ω, and no collapsing function, is defined
or used.** Heights are well-founded trees whose stage nodes retain a height
for every presentation. Such a node is only read at a countable level, at
the stages that level contains. The bound for an evaluated derivation is the
reading of its retained heights at the stage where its actual evidence
lies.

Every analysis of ID₁ must evaluate premises indexed by all stages at the
stages a derivation actually uses: Bachmann does this with fundamental
sequences of length Ω, and Buchholz's Ω-rule method with collapsing
functions. Here it is done by reading retained heights at levels, with no
notation for Ω.

### 8.4 Calibration

`Theories.ID.Uniform.Calibration` † proves O ↪ BH, where BH is the
Bachmann–Howard segment of a two-index notation system of Weiermann. The
notation enters only this calibration module; the bound of §8.3 does not
import it, and the calibration is proved after the bound.

### 8.5 Status

- The lower half, that ID₁ proves transfinite induction along the
  predecessor domain of every point of O, is in progress. The points of O
  have finite descriptions with a Boolean validity check, proved sound and
  complete (`Theories.ID.Uniform.Decision` †: `decide`). The current step
  is to express that validity arithmetically inside ID₁.
- The bound covers upright targets: cedents without negative literals of
  the predicate.
- O d and O are not shown equal.
- Peano arithmetic is analysed with both halves at the geometric ε₀
  (`Theories.PA.Presented.Analysis` †: `analysis`). A calibration with
  Cantor normal forms enters only its lower half, as coordinates of PA's
  numeral presentations.

## 9. Scope and nonclaims

- Presentations are not required to be sets, and no claim is made that two
  presentations of one order type are identified (§6.2).
- As constructed, the carrier of ω₁ lies one level above the presentations;
  up to equivalence ω₁ is small and the same at every level (§4.6). Its
  uniqueness concerns the well-order, not the geometry producing it.
- The diagonal of §3 is a strict upper bound, not a least one.
- Regularity of ω₁ is not constructive: it gives LPO, and LPO with
  countable choice gives it (§4.5).
- The comparison of ω₁ with H_ℕ uses excluded middle or resizing as stated
  in §4.4.
- Rows 9 and 14 without their data give LPO; whether LPO suffices for them
  is not addressed. The exact strength of stability at ω + 1 is not
  determined (§5.2).
- The ID₁ results are † and cover only the upper half (§8.5).
- For closed heights (§4.7) the release proves that rank sends children
  strictly below their parents, that the rank of Ord(ℓ) is Ord(ℓ), and
  what rank forgets over 0 and over successors (§6.2). It does not state
  how rank treats ⊑ and ⊏, nor what its fibers over limits contain.
- The inaccessible points of Ord(ℓ) take the reflector as a parameter
  (§4.8). Agda gives one by induction–recursion, which this release does
  not contain. Degrees of Mahloness beyond the first, and clubs other
  than those given by functions, are not addressed.

## 10. Related work

- The Univalent Foundations Program, *Homotopy Type Theory: Univalent
  Foundations of Mathematics*, Institute for Advanced Study, 2013, §10.3:
  ordinals as extensional well-founded relations, initial segments `A_{/a}`,
  and suprema of small families (Lemma 10.3.22), used in
  [Reflection/Supremum](src/SPT/Cubical/OrdinalGeometry/Cubical/Reflection/Supremum.agda).
- N. Kraus, F. Nordvall Forsberg and C. Xu, *Type-Theoretic Approaches to
  Ordinals*: Table 1 and the specifications of the arithmetic followed in
  §5.
- T. de Jong, N. Kraus, F. Nordvall Forsberg and C. Xu, *Set-Theoretic and
  Type-Theoretic Ordinals Coincide*.
- M. H. Escardó and contributors, *TypeTopology*,
  https://github.com/martinescardo/TypeTopology: the ordinal library compared
  with in §6.
- P. Aczel, *The type theoretic interpretation of constructive set theory*,
  1978, and its sequel on choice principles, 1982: sets as well-founded
  trees over a universe, with extensional equality defined afterwards. The
  index type each tree keeps validates the presentation axiom and countable
  and dependent choice. It is a close precedent for building the
  intensional object first and recovering extensional identity afterwards.
  Here that order is applied to ordinals, the reflection is a separate step
  (§4), and what each kept datum is worth is measured row by row (§5) and
  by what the reflection forgets (§6.2).
- H. Bachmann, *Die Normalfunktionen und das Problem der ausgezeichneten
  Folgen von Ordnungszahlen*, 1950: fundamental sequences of length Ω.
- W. Buchholz, the Ω-rule method for ID₁, with collapsing functions.
