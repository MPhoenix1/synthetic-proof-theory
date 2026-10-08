# Synthetic Proof Theory

*Ordinal analysis as a type-theoretic discipline, in Agda.*

Synthetic Proof Theory carries out ordinal analysis inside type theory.
Ordinals are presentations with their retained data, heights of infinitary
derivations are trees read into presentations, and every bound is a
construction in type theory. This repository is its public release. Part I,
Ordinal Geometry, is released here; Part II, the analyses, is forthcoming.

## Part I: Ordinal Geometry

*Countable ordinals as retained presentations.*

Ordinal Geometry studies countable ordinals in intensional type theory
through their presentations. A presentation is a countable well-founded
strict order with its equivalence relation, a comparison function and a
partial enumeration, all kept as data, and a point x is read as its
predecessor domain ∂ₚx = Σ y. y <ₚ x. Order types are recovered afterwards
by an explicit reflection into Cubical well-orders, at which level ∂ₚx is
the initial segment that the HoTT book writes `A_{/x}`.

The development constructs ω₁ from presentations with a constructive
characterization. It places each property in the table of Kraus, Nordvall
Forsberg and Xu (*Type-Theoretic Approaches to Ordinals*) on the object
that carries its datum, and proves that removing the datum costs exactly
LPO. It also measures what the reflection into ordinary ordinals forgets.
Everything is checked with `--safe` and no postulates.

### Main results

| Result | Modules |
|---|---|
| Presentations; extensionality modulo the retained equivalence | [CountableOrdinal](src/SPT/Cubical/OrdinalGeometry/Presentation/CountableOrdinal.agda), [Map](src/SPT/Cubical/OrdinalGeometry/Presentation/Map.agda) |
| A choice-free countable diagonal; no ℕ-family covers all presentations | [CountableOrdinal](src/SPT/Cubical/OrdinalGeometry/Presentation/CountableOrdinal.agda) |
| ω₁ from presentations: α lies below ω₁ exactly when it is merely presented; ω₁ is least, unpresentable, and unique | [OmegaOne/Base](src/SPT/Cubical/OrdinalGeometry/Cubical/OmegaOne/Base.agda), [OmegaOne/Cut](src/SPT/Cubical/OrdinalGeometry/Cubical/OmegaOne/Cut.agda), [Specification](src/SPT/Cubical/OrdinalGeometry/Cubical/OmegaOne/Specification.agda) |
| Comparison with the ℕ-Hartogs well-order, under explicit hypotheses | [Hartogs/Base](src/SPT/Cubical/OrdinalGeometry/Cubical/Hartogs/Base.agda), [OmegaOne/Hartogs](src/SPT/Cubical/OrdinalGeometry/Cubical/OmegaOne/Hartogs.agda) |
| Regularity of ω₁ gives LPO; LPO and countable choice give regularity | [Regularity](src/SPT/Cubical/OrdinalGeometry/Cubical/OmegaOne/Regularity.agda) |
| Each row of the KNFX table holds with its datum; rows 2, 5, 6, 8, 13 and 15–18, asked of all presentations, are equivalent to LPO, and rows 9 and 14 give LPO | [Arithmetic.agda](src/SPT/Cubical/OrdinalGeometry/Arithmetic.agda), [Arithmetic/](src/SPT/Cubical/OrdinalGeometry/Arithmetic/), [ExactOrder/Comparison](src/SPT/Cubical/OrdinalGeometry/ExactOrder/Comparison.agda), [Reflection/Supremum](src/SPT/Cubical/OrdinalGeometry/Cubical/Reflection/Supremum.agda) |
| A faithful bridge to TypeTopology's ordinals, and fibers of the projection with no finite h-level | [TypeTopology/Bridge](src/SPT/Cubical/OrdinalGeometry/Cubical/TypeTopology/Bridge.agda), [Fiber/Position](src/SPT/Cubical/OrdinalGeometry/Cubical/Fiber/Position.agda), [Fiber/Principal/Unbounded](src/SPT/Cubical/OrdinalGeometry/Cubical/Fiber/Principal/Unbounded.agda) |

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
  chains, normalization.
- `OrdinalGeometry/ExactOrder`: exact countable orders, their comparison
  under LPO, and ω^.
- `OrdinalGeometry/Operation`: operations on initial maps, normal
  operations.
- `OrdinalGeometry/Arithmetic`: the KNFX table, with ambients,
  characterizations, +, ·, ω^, subtraction, division, discriminators and
  their exact strengths; `OrdinalGeometry/Arithmetic.agda` restates the
  whole table as two records, `Rows` and `Strength`.
- `OrdinalGeometry/Cubical`: the Cubical modules. `Reflection`: order
  types, maps, suprema, classification, countability; `OmegaOne`: ω₁, its
  cut, specification and regularity, and its comparison with H_ℕ;
  `Hartogs`: the ℕ-Hartogs well-order; `Fiber`: what reflection forgets;
  `TypeTopology`: the bridge to TypeTopology's ordinals.
- `Core`: supporting constructions. `WellFounded`: accessibility,
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
`--cubical-compatible`. Every module of the development, and the nine copied
TypeTopology files that need it, also sets `-WnoUnsupportedIndexedMatch`, as
the cubical library does in its own flags. That warning says that a function
defined by pattern matching on an indexed family does not compute when
applied to a transport in Cubical Agda. It concerns computation, not what is
checked.

## License

GNU General Public License, version 3: see [LICENSE](LICENSE). [NOTICE](NOTICE)
gives the copyright and describes the files copied from TypeTopology.
