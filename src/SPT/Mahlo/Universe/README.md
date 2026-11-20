# A generated Mahlo universe

[Universe](../Universe.agda) defines a small Tarski universe by native induction–recursion, from a displayed seed `U : DΣ ℓ ℓ` ([Foundation/Spaces](../../Foundation/Spaces.agda)) and a fixed operator Ψ on complete small families. Its codes form a closure of the ambient formers and Ψ, hence a Mahlo reflection of the ambient family, and they are closed under one form of coded indexed induction–recursive formation. [Formation](Formation.agda) reads the spaces of the reflected child off the universe and checks what its formation retains.

```text
Fam ℓ = Σ(A : Set ℓ).(A → Set ℓ)
Ψ : Fam ℓ → Fam ℓ
Code U Ψ : Set ℓ
decode   : Code U Ψ → Set ℓ
```

In Agda the operator type is `Ambient.Operator ℓ` ([Ambient](../Ambient.agda)).

| Module | Contents |
| --- | --- |
| [Universe](../Universe.agda) | The codes and their decoding, defined together (`Code`, `decode`): U's base and fibers, all ordinary formers, Ψ's complete results and branches, and coded seed diagrams (`Seeds`) naming whole indexed boundary families of [Boundary](Boundary.agda) and their exact fills (`boundary`, `filling`), every decoding equation judgmental. The codes form a closure of the ambient formers and Ψ (`closure`), with the child's formers and laws (`formers`, `laws`), hence a Mahlo reflection of the ambient family (`reflection`), and they have dependent induction (`Methods`, `ind`). |
| [Boundary](Boundary.agda) | Retained boundaries and their fills, by homogeneous indexed induction–recursion, Agda's own, over an index type, a seed family and the fills of the seeds. A boundary is a seed, or a fan: a boundary with a boundary at every fill of it (`RetainedBoundary`: `retained-seed`, `filler-indexed-fan`). Its fills are decoded together with it (`RetainedFill`): a seed's are its given fills, and a fan's are the complete fans of child fills, one at every fill of the boundary, both by refl (`retained-seed-fill-computes`, `filler-indexed-fan-fill-computes`). [Universe](../Universe.agda) codes them inside its own induction–recursive definition (`boundary`, `filling`). |
| [Formation](Formation.agda) | The spaces of the reflected child ([Child](../Child.agda)) use the generated universe literally: its carrier, decoding and formers are the universe's (`code-β`, `decode-β`, `formers-β`), and the seed space U is recovered (`ambient-β`, `point-β`). A nonconstant operator keeps the complete input family and returns point-dependent fibers; selecting a different result point changes later total formation (`no-selection-loss`). Coded boundary families and their fills feed later formation: complete fills, not boundaries alone, determine the next total (`Boundary.no-filler-loss`), and a generated carrier can be the index type of a further formation (`Boundary.next`). |

## Formation and computation

| Constructors | Decoding |
| --- | --- |
| `codes`, `old c` | `Base U`, `Fiber U c` |
| `empty`, `unit`, `two`, `natural` | `Lift ℓ 𝟘`, `Lift ℓ 𝟙`, `Lift ℓ 𝟚`, `Lift ℓ ℕ` |
| `product a b`, `sum a b` | Dependent functions and dependent pairs |
| `tree a b` | The W-type of [Foundation/Tree/W](../../Foundation/Tree/W.agda) |
| `identity a x y` | `x ＝ y` in `decode a` |
| `result a b` | The domain returned by Ψ |
| `branch a b y` | Its dependent fiber at the returned point `y` |
| `boundary S i` | The entire indexed boundary type at `i` |
| `filling S i r` | The exact filler type of boundary `r` |

All decoding clauses compute judgmentally. `formers U Ψ` supplies all eight ordinary formers, and `laws U Ψ` proves their decoding equations. `Methods` and `ind` give dependent induction over every constructor.

The constructor pair `codes , old` represents the entire supplied U. `ambient-β` recovers its complete family by `refl`; `sum codes old` decodes to `Total U`. `inclusion` is the split map keeping each old base and its literal fiber. `universe U Ψ` packages the generated codes and decoder as a `DΣ ℓ ℓ`.

`action` sends `(a , b)` to `(result a b , branch a b)`. Its equation is

```text
map (action F) ＝ Ψ (map F).
```

It holds by `refl` for every complete generated family, including arbitrary dependent branch functions. Both the returned domain and its whole fiber family are retained.

## Coded indexed formation

`Seeds C D` retains a coded index type, an index-dependent seed code, and a filler code for every seed. All three components of a diagram `S : Seeds (Code U Ψ) decode` therefore belong to the current universe.

The constructors `boundary S i` and `filling S i r` occur in the defining mutual block. They decode to the actual `RetainedBoundary` and `RetainedFill` of [Boundary](Boundary.agda). The boundary argument of `filling` has type `decode (boundary S i)`, so it is an exact point of the generated carrier. Both decoding equations hold by `refl`. `filling-seed-β` and `filling-fan-β` expose the original seed and full dependent-fan equations.

`formed S i` packages these codes as a complete family. `formed-β` recovers the entire generated boundary and filler pair, and `formed-total-β` names its complete dependent total. `All S P` packages the induction hypotheses for every code in the diagram; the extended `ind` handles both new cases.

All types remain at level ℓ. The generated carrier can itself be the coded index of another diagram, and its fillers can become the new seed types. This closes the universe under this particular indexed formation; reflection of arbitrary operators inside the universe remains a separate construction.

## The reflected child's spaces

`reflection U` is a constructed `MahloReflection` ([Decoding](../Decoding.agda)) for the parent with codes `Set ℓ` and identity decoding. For each Ψ, its returned carrier is literally `Code U Ψ`, and its closure is that of the universe. Thus the concrete small space type is

```agda
Child.Mahlo-Space (Universe.reflection U) Ψ
```

Its code type, decoder, and ordinary formers are judgmentally those of the universe. The parent code type is in `Set (lsuc ℓ)`, while the generated codes, decoded types, and spaces are in `Set ℓ`. This gives closure under the chosen Ψ; it does not assert reflection of arbitrary operators inside the completed generated universe.

## Selections and fills in Formation

[Formation](Formation.agda) develops the literal specialization, exact recovery of U, repeated action, dependent products and identities, W-formation, and induction. Its nonconstant operator returns empty or inhabited fibers according to the selected result point. A subsequent dependent sum remains empty or inhabited accordingly, and `no-selection-loss` refutes identifying the two resulting types.

Its `Boundary` namespace forms indexed carriers, their exact filler codes, and complete spaces for the Mahlo action. Two fans with the same domain have fillable and unfillable children, and `no-filler-loss` refutes identifying the resulting dependent totals. `next` uses the first generated carrier as its index type and the first fillers as its seeds; `nested-filling-β` and `nested-spine-β` check the repeated formation.
