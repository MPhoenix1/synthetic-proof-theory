# Synthetic Proof Theory

*Ordinal analysis as a type-theoretic discipline, in Agda.*

Synthetic Proof Theory carries out ordinal analysis inside type theory.
Ordinals are presentations with their retained data, heights of infinitary
derivations are trees read into presentations, and every bound is a
construction in type theory. This repository is its public release. Part I,
Ordinal Geometry, is released here; Part II, the analyses, is forthcoming.

## Part I: Ordinal Geometry

*Countable ordinals as retained presentations, and the ordinal of
ordinals as a height.*

Ordinal Geometry studies ordinals in intensional type theory through the
data that present them, beginning with countable ordinals and their
presentations. A presentation is a countable well-founded strict order with
its equivalence relation, a comparison function and a partial enumeration,
all kept as data, and a point x is read as its predecessor domain
∂ₚx = Σ y. y <ₚ x. Order types are recovered afterwards by an explicit
reflection into Cubical well-orders, at which level ∂ₚx is the initial
segment that the HoTT book writes `A_{/x}`.

The development constructs ω₁ from presentations with a constructive
characterization. It places each property in the table of Kraus, Nordvall
Forsberg and Xu (*Type-Theoretic Approaches to Ordinals*) on the object
that carries its datum, and proves that removing the datum costs exactly
LPO, except for rows 9 and 14, where it costs at least LPO. None of these
strengths depends on relations with several witnesses. It also measures
what the reflection into ordinary ordinals forgets.

One level up, the ordinal of ordinals is itself a height: a tree whose
children are all the heights of a universe. Its rank is Cubical's ordinal
of ordinals, which is TypeTopology's OO. Given the Mahlo rule, reflections
of the universe give its inaccessible points. Compared with the classical
notions as ω₁ is compared with the ℕ-Hartogs well-order, they are
inaccessible cardinals under excluded middle and choice, and the ordinal of
ordinals is Mahlo in the function form. Everything is checked with `--safe`
and no postulates.

### Main results

| Result | Modules |
|---|---|
| Presentations; extensionality modulo the retained equivalence | [CountableOrdinal](src/SPT/Cubical/OrdinalGeometry/Presentation/CountableOrdinal.agda), [Map](src/SPT/Cubical/OrdinalGeometry/Presentation/Map.agda) |
| A choice-free countable diagonal; no ℕ-family covers all presentations | [CountableOrdinal](src/SPT/Cubical/OrdinalGeometry/Presentation/CountableOrdinal.agda) |
| ω₁ from presentations: α lies below ω₁ exactly when it is merely presented; ω₁ is least, unpresentable, and unique | [OmegaOne/Base](src/SPT/Cubical/OrdinalGeometry/Cubical/OmegaOne/Base.agda), [OmegaOne/Cut](src/SPT/Cubical/OrdinalGeometry/Cubical/OmegaOne/Cut.agda), [Specification](src/SPT/Cubical/OrdinalGeometry/Cubical/OmegaOne/Specification.agda) |
| ω₁ is small up to equivalence and the same at every universe level; it is the unique point of the ordinal of ordinals whose predecessors are exactly the merely presented well-orders | [OmegaOne/Small](src/SPT/Cubical/OrdinalGeometry/Cubical/OmegaOne/Small.agda), [Reflection/Ordinals](src/SPT/Cubical/OrdinalGeometry/Cubical/Reflection/Ordinals.agda) |
| Comparison with the ℕ-Hartogs well-order, under explicit hypotheses | [Hartogs/Base](src/SPT/Cubical/OrdinalGeometry/Cubical/Hartogs/Base.agda), [OmegaOne/Hartogs](src/SPT/Cubical/OrdinalGeometry/Cubical/OmegaOne/Hartogs.agda) |
| Regularity of ω₁ gives LPO; LPO and countable choice give regularity | [Regularity](src/SPT/Cubical/OrdinalGeometry/Cubical/OmegaOne/Regularity.agda) |
| Each row of the KNFX table holds with its datum; rows 2, 5, 6, 8, 13 and 15–18, asked of all presentations, are equivalent to LPO, and rows 9 and 14 give LPO | [Arithmetic.agda](src/SPT/Cubical/OrdinalGeometry/Arithmetic.agda), [Arithmetic/](src/SPT/Cubical/OrdinalGeometry/Arithmetic/), [ExactOrder/Comparison](src/SPT/Cubical/OrdinalGeometry/ExactOrder/Comparison.agda), [Reflection/Supremum](src/SPT/Cubical/OrdinalGeometry/Cubical/Reflection/Supremum.agda) |
| The strengths do not depend on relations with several witnesses: every row has the same strength over Boolean orders and over propositional presentations | [Comparison/Representatives](src/SPT/Cubical/OrdinalGeometry/Arithmetic/Comparison/Representatives.agda), [Presentation/Propositional](src/SPT/Cubical/OrdinalGeometry/Presentation/Propositional.agda) |
| A faithful bridge to TypeTopology's ordinals, and fibers of the projection with no finite h-level | [TypeTopology/Bridge](src/SPT/Cubical/OrdinalGeometry/Cubical/TypeTopology/Bridge.agda), [Fiber/Position](src/SPT/Cubical/OrdinalGeometry/Cubical/Fiber/Position.agda), [Fiber/Principal/Unbounded](src/SPT/Cubical/OrdinalGeometry/Cubical/Fiber/Principal/Unbounded.agda) |
| TypeTopology's univalence holds in Cubical Agda; Cubical's ordinal of ordinals is TypeTopology's OO, and ω₁ is the segment of OO below the ordinal of Ω | [TypeTopology/Univalence](src/SPT/Cubical/OrdinalGeometry/Cubical/TypeTopology/Univalence.agda), [TypeTopology/OrdinalOfOrdinals](src/SPT/Cubical/OrdinalGeometry/Cubical/TypeTopology/OrdinalOfOrdinals.agda) |
| The ordinal of ordinals as a height: Ord(ℓ) lies above every height of level ℓ and below none (Burali-Forti); its rank is Cubical's ordinal of ordinals, so TypeTopology's OO | [Height/Ordinals](src/SPT/Cubical/OrdinalGeometry/Height/Ordinals.agda), [Cubical/Height/Rank](src/SPT/Cubical/OrdinalGeometry/Cubical/Height/Rank.agda), [Cubical/Height/Ordinals](src/SPT/Cubical/OrdinalGeometry/Cubical/Height/Ordinals.agda) |
| Rank forgets the labels of heights: its fiber over every successor contains the merely inhabited types, so it has no finite h-level and rank is not an embedding, also as a map into TypeTopology's ordinals; over 0 the fiber is contractible | [Fiber/Height](src/SPT/Cubical/OrdinalGeometry/Cubical/Fiber/Height.agda), [Fiber/Height/Unbounded](src/SPT/Cubical/OrdinalGeometry/Cubical/Fiber/Height/Unbounded.agda), [TypeTopology/HeightLoss](src/SPT/Cubical/OrdinalGeometry/Cubical/TypeTopology/HeightLoss.agda) |
| Inaccessible points of the ordinal of ordinals, from reflections of the universe: under excluded middle the rank of a reflection is the Hartogs well-order of its child universe; with choice it is inaccessible; with a reflector, Ord(ℓ) is Mahlo in the function form | [Height/Ordinals/Mahlo](src/SPT/Cubical/OrdinalGeometry/Height/Ordinals/Mahlo.agda), [Cubical/Height/Hartogs](src/SPT/Cubical/OrdinalGeometry/Cubical/Height/Hartogs.agda), [Cubical/Height/Mahlo](src/SPT/Cubical/OrdinalGeometry/Cubical/Height/Mahlo.agda), [Hartogs/Cardinal](src/SPT/Cubical/OrdinalGeometry/Cubical/Hartogs/Cardinal.agda) |

### Reading

[GUIDE.md](GUIDE.md) explains the mathematics and the exact scope of each
result, with reading paths for type theorists and for proof theorists. Its
§8 describes Part II: an upper bound for ID₁ obtained with no ordinal
notation for Ω and no collapsing function, calibrated against
Bachmann–Howard only afterwards.

## Layout

Every module is under `src/SPT/Cubical`, and its name follows its path, as
in `SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal`.

- `OrdinalGeometry/Presentation`: presentations, maps, sums, limits of
  chains, normalization, propositional presentations.
- `OrdinalGeometry/ExactOrder`: exact countable orders, Boolean orders,
  their comparison under LPO, and ω^.
- `OrdinalGeometry/Operation`: operations on initial maps, normal
  operations.
- `OrdinalGeometry/Height`: closed heights, their simulation order, the
  ordinal of ordinals as a height, the boundaries of reflections, and the
  inaccessible points of the ordinal of ordinals.
- `OrdinalGeometry/Arithmetic`: the KNFX table, with ambients,
  characterizations, +, ·, ω^, subtraction, division, discriminators and
  their strengths, also over classes of representatives;
  `OrdinalGeometry/Arithmetic.agda` restates the whole table as two
  records, `Rows` and `Strength`.
- `OrdinalGeometry/Cubical`: the Cubical modules. `Reflection`: order
  types, maps, suprema, classification, countability, the ordinal of
  ordinals; `OmegaOne`: ω₁, its cut, specification, size and regularity,
  and its comparison with H_ℕ; `Hartogs`: the Hartogs well-orders of ℕ
  and of universes, and the classical cardinal notions; `Fiber`: what
  reflection and rank forget; `Height`: the rank of a height, of the
  ordinal of ordinals and of reflections, and the Mahlo comparison;
  `TypeTopology`: the bridge to TypeTopology's ordinals, its univalence,
  and its ordinal of ordinals.
- `Core`: supporting constructions. `Mahlo`: the Mahlo rule, reflections
  over a Tarski family with the decoding laws of their formers, and the
  universe as a parent; `WellFounded`: accessibility,
  well-founded relations, lexicographic orders, and termination of
  rewriting by ranks; `Nat`: orders on ℕ, least witnesses, a pairing of
  ℕ × ℕ with ℕ, and first successes of partial sequences; `Equality`:
  propositions and sets, contractibility, fibers, isomorphisms of types
  A ≅ B, and covers; `Generator`: trees and linear histories over
  signatures.
- `TypeTopology`: files copied from TypeTopology; see [NOTICE](NOTICE).
- [Everything.agda](src/SPT/Cubical/Everything.agda): imports every module.

## Checking

Requirements: Agda 2.8.0, with `standard-library-2.3` and `cubical-0.9`
registered as libraries.

The repository is one Agda library, [SPT.agda-lib](SPT.agda-lib):

```text
name: SPT
include: src
depend: standard-library cubical-0.9
flags: --safe
```

From the repository root, this checks every module:

```text
agda src/SPT/Cubical/Everything.agda
```

Every module also sets `--safe` in its own OPTIONS pragma. The modules under
`OrdinalGeometry/Cubical` use `--cubical --guardedness`, and all others are
`--cubical-compatible`. Every module of the development, and the thirteen
copied TypeTopology files that need it, also sets
`-WnoUnsupportedIndexedMatch`, as the cubical library does in its own
flags. That warning says that a function defined by pattern matching on an
indexed family does not compute when applied to a transport in Cubical
Agda. It concerns computation, not what is checked.

## License

GNU General Public License, version 3: see [LICENSE](LICENSE). [NOTICE](NOTICE)
gives the copyright and describes the files copied from TypeTopology.
