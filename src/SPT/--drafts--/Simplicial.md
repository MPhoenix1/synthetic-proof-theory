# The ambient Mahlo rule in simplicial sets (UIR7)

Status: sketch, revised 2026-11-01 after an outside review. The review
judged the construction viable and asked for the repairs
made here: a strict inequality, a precise notion of size, the club, the
isomorphism of a representing vertex, a proof of the embedding lemma, a
convention for the formers, and assembly as one fibration. Next: a
detailed proof. The construction and its lemmas are ours. Every fact cited
is from a source read. This is the model input for `SPT.Mahlo.DS`.

## Assumptions

- **External:** ZFC with a strongly Mahlo cardinal κ and inaccessibles
  κ < κ₁ < … for the levels above. Classical reasoning and choice are
  used outside the model.
- **Internal:** intensional Martin-Löf type theory with Π, Σ, identity
  types, W, 0, 1, +, Tarski universes and univalence. No choice or
  excluded middle is assumed inside.
- **Syntax:** Kapulkin–Lumsdaine interpret the syntax "assuming
  initiality (Conjecture 1.2.9)"; without it, their structures interpret
  individual judgements by hand (Cor. 2.3.5).
  - **In SPT** (`SPT.Foundation.Tree`): derivations are trees over a
    signature.
    - **Interpretation:** a fold into any algebra
      (`SPT.Foundation.Tree.Fold`), unique pointwise with no
      extensionality (`Fold.Initiality.fold-unique`), compared by
      relational folds.
    - **Substitution:** `bind`, with unit and associativity laws.
    - **Change of signature:** exact and lax translations of signatures,
      along which folds are natural (`lax-tree-fold-natural`).
  - **The core theory** ([MartinLof](../MartinLof/README.md)):
    - Martin-Löf type theory with W, Russell universes at closed levels,
      Lift, and as its only constants univalence (TypeTopology's
      `is-univalent`) and `Mahlo (Ambient.formers ℓ)` at every level, with
      their statements written in the theory's syntax
      ([MartinLof/Univalence](../MartinLof/Univalence.agda),
      [MartinLof/Mahlo](../MartinLof/Mahlo.agda)).
    - Raw syntax, with substitution laws.
    - The judgments and every rule, equality judgments included, as one
      signature. Its derivations are generated histories.
    - Both statements are types at level l+1, so the constants are terms
      of them in every valid context (`univalence-type`, `univalence-term`,
      `mahlo-type`, `mahlo-term`).
    - Soundness and consistency ([MartinLof/Soundness](../MartinLof/Soundness.agda)):
      a model supplies closed terms of the values of the two statements.
    - The Mahlo constant is at every level, so a model of this theory
      needs every universe Mahlo: Mahlo cardinals κ₀ < κ₁ < ⋯, one per
      level, and an inaccessible above them. One Mahlo cardinal suffices
      for the DS result at a single level (below).
  - **Models** ([MartinLof/Model](../MartinLof/Model.agda)): the base is a natural
    model whose types are the terms of a tower of Russell universes, and
    there is a structure per former. Operations are total, and their laws
    hold where the arguments are typed.
  - **What this leaves:**
    - presenting the simplicial structures as such a model, on paper:
      - terms at level l are maps into the total space of the universe at
        l, and their types are the composites with the projection, read
        in the universe above;
      - comprehension is by chosen pullback along codes;
      - mixed levels use the restricted structures;
      - values off the typed arguments are chosen classically.
  - **Outside:** de Boer (licentiate thesis, Stockholm 2020; abstract
    read) does that work for Martin-Löf type theory with 0, 1, ℕ, +, Π, Σ,
    identity types and a cumulative hierarchy of universes, formalized in
    Agda with Brunerie. W is not among them.

## What is to be shown

Interpret the theory in simplicial sets (Kapulkin–Lumsdaine), with
`Set ℓ` read as the universe $U_κ$ and `Set (lsuc ℓ)` as $U_{κ_1}$.

**Claim (ours).** The type `Mahlo (Ambient.formers ℓ)` of
`SPT.Mahlo.Specification` and `SPT.Mahlo.Ambient` has an element in this
model, alongside univalence.

`SPT.Mahlo.DS` is checked, `--safe --without-K`, with extensionality only
as explicit hypotheses for named function types, all of which hold under
univalence ([DS README](../Mahlo/DS/README.md)).
It turns that element into `Smallness ℓ` (`Ambient.smallness`, no
hypothesis), and from there into every form of induction–recursion that
the DS README lists: type-valued small-arity Dybjer–Setzer induction–recursion,
indexed polynomial induction–recursion with Dybjer–Setzer's rules for
general indexed induction–recursion, induction–recursion with outputs
in any type, the Mahlo rule of every family admitting the small types,
and set-valued descriptions with set arities. So all of these,
with decoding as an identity, would be consistent with univalence
relative to ZFC with a Mahlo cardinal and inaccessibles above it.

## Facts used

- **Vertex detection** (Christensen, *Non-accessible localizations*,
  J. Topology 2024, arXiv 2109.06670 §5.2, read through the arXiv HTML).
  Prop. 5.10: a (−1)-truncated fibration between fibrant simplicial sets
  has a section if and only if its fiber over every vertex is nonempty.
  Those fibers are then contractible, so the map is a trivial fibration.
- **Universes** (Kapulkin–Lumsdaine, *The simplicial model of univalent
  foundations (after Voevodsky)*, JEMS 2021, arXiv 1211.2851; read).
  - **Basic properties:** $U_α$ is a univalent Kan complex (Thm 2.2.1,
    §3). It is strictly universal for α-small well-ordered fibrations and
    weakly universal for α-small fibrations (Cor. 2.1.12), α-small meaning
    fibers over every simplex of cardinality below α.
  - **Structures:** for α inaccessible, $U_α$ carries Π-, Σ-, Id-, W-, 1-,
    0- and +-structures (Thm 2.3.4).
  - **Smaller universes:** for β < α inaccessible, $U_β$ is represented by
    a vertex $u_β$ of $U_α$. There is a natural inclusion $i : U_β → U_α$
    whose pullback of $U_α$'s universal family is $U_β$'s "by
    construction".
  - **Restricted structures:** each structure of $U_α$ composed with $i$
    factors through $i$, giving $U_β$ structures that commute with it.
    The structures $U_β$ has on its own "do not automatically commute
    with i" (remark after Thm 2.3.4).
  - **η:** Π-η holds (Prop. 2.3.6).
  - **Scope:** their type theory is Π, Σ, Id, W, 0, 1, + and Tarski
    universes; CIC's general scheme of inductive definitions is "not
    pursued".
- **Pattern matching** (Cockx, PhD thesis, KU Leuven 2017, §4.3, read).
  - **Translation** (Thm 4.27): a definition by a valid case tree, whose
    splits have positive or negative unifiers and whose recursion is
    structural on a datatype, translates to eliminators without K.
  - **Same reduction** (Thm 4.29): with strong positive unifiers, the
    translation has the same reduction behaviour.
  - **Strength:** every rule of the thesis's algorithm is strong except
    deletion (§3.3), which `--without-K` forbids. The algorithm was
    released in Agda 2.5.1; later changes to Agda's unifier are not
    checked.
  - **Earlier criterion:** Cockx, Devriese, Piessens, JFP 2016, Thm 1,
    read.
- **Inductive types from W** (Hugunin, *Why Not W?*, TYPES 2020, read).
  Assuming strict β for all formers and strict η for Σ and Π, ℕ, lists, W
  and the like built from W, Id, Σ, Π and universes compute as expected,
  compatibly with univalence.
- **Excluded middle** holds in this model (Kapulkin–Lumsdaine, TAC 2020,
  read). It is not used below.

## Construction (ours)

Write $D_α$ for the decoding of $U_α$ and
$\mathsf F_α = Σ_{X : U_α} (D_α X → U_α)$ for its space of families.

1. **Families and size.** A closed family is a diagram $E \xrightarrow{p}
   A → 1$ with A a Kan complex and p a Kan fibration. It is μ-small when
   both A and p are: fibers over every simplex of cardinality below μ.
   - **Equivalence:** two closed families are equivalent when there is an
     equivalence of indices and, over it, a fiberwise equivalence of
     members. By univalence this is a path in $\mathsf F_κ$.
   - **Size:** the size $|G|$ of a closed family G is the least μ such
     that G is equivalent to a μ-small family.
2. **Lemma A, the bound.** For a closed operator ψ (a vertex of
   `Operator ℓ`) and α < κ, let
   $b_ψ(α) = \sup \{\, |ψ(G)| : |G| < α \,\}$. Then $b_ψ(α) < κ$.
   - **Counting:** an α-small family, α infinite, has $|A_n| < α$ and
     $|E_n| ≤ α$ in each degree n. The whole diagram (faces, degeneracies
     and p) is coded by sets of size at most $α · ℵ_0$. So there are at
     most $2^{α · ℵ_0} < κ$ isomorphism classes, κ being a strong limit.
     This counts whole diagrams, their twisting included, not lists of
     fiber types.
   - **Invariance:** isomorphic families are equivalent, hence joined by a
     path in $\mathsf F_κ$. ψ maps it to a path between the outputs, so
     the outputs have the same size.
   - **Bound:** so $b_ψ(α)$ is a supremum of fewer than κ sizes, each
     below κ because outputs lie in $\mathsf F_κ$. κ is regular.
3. **Lemma B, component invariance.** For a path $p : ψ_0 = ψ_1$ and an
   input G, applying evaluation at G to p gives $ψ_0(G) = ψ_1(G)$. So
   $b_{ψ_0} = b_{ψ_1}$, and the bound depends only on the path component
   c; write $b_c$.
4. **Closure points.** Let
   $C_c = \{\, λ < κ : ∀ β < λ.\ b_c(β) < λ \,\}$.
   - **Unbounded:** from ξ < κ, put $ξ_0 = ξ + 1$ and
     $ξ_{n+1} = \sup_{β < ξ_n} b_c(β) + 1$, below κ by regularity. Then
     $\sup_n ξ_n < κ$, since cf κ > ω, and it lies in $C_c$.
   - **Closed:** a limit of members is a member.
   - **The choice of $λ_c$:** κ is Mahlo, so $C_c$ contains an
     inaccessible; $λ_c$ is the least. This selection uses no choice. The
     construction as a whole uses ZFC's choice (well-orderings of fibers,
     the lifts behind Prop. 5.10).
5. **The carrier.** A simplicial set is the sum of its connected
   components, and for a Kan complex these are its path components. On
   the component c, with λ = $λ_c$, the carrier is constant at the vertex
   $u_λ$ of $U_κ$ representing $U_λ$, which comes with an isomorphism
   $χ_λ : D_κ(u_λ) ≅ U_λ$. Interpretation is the composite
   $D_κ(u_λ) \xrightarrow{χ_λ} U_λ \xrightarrow{i_λ} U_κ$.
6. **Embedding lemma.**
   - **The universe:** $i_λ$ is an embedding. For $a, b : U_λ$, the map
     $\mathrm{ap}_{i_λ} : (a = b) → (i_λ a = i_λ b)$ sits over the
     comparison $(D_λ a ≃ D_λ b) → (D_κ(i_λ a) ≃ D_κ(i_λ b))$. The two
     vertical maps are equivalences by univalence, and the comparison is
     an equivalence because $D_λ$ is the pullback of $D_κ$ along $i_λ$.
     So $\mathrm{ap}_{i_λ}$ is an equivalence. Preservation of the
     identity former alone would not give this; the univalence square
     does.
   - **Its families:** $j_λ : \mathsf F_λ → \mathsf F_κ$,
     $(a, b) ↦ (i_λ a, i_λ ∘ b)$, is an embedding. Its fiber over (A, B) is
     equivalent to
     $Σ_{(a, p) : \mathrm{fib}_{i_λ}(A)}\ Π_{x : D_λ a}\ \mathrm{fib}_{i_λ}(B(\bar p\, x))$,
     where $\bar p : D_λ a ≃ D_κ A$ is induced by p. The fibers of $i_λ$
     are propositions, so by function extensionality so is this type.
   - **Scope:** neither step needs the classified types to be sets.
   - **Checked internally** :
     `Embedding` (not included in this release) proves both steps in
     cubical Agda for any univalent families with a decoding-compatible map
     (`Univalent`, `embedding`, `families-embedding`), and that the families
     named over a family form a proposition (`names`).
7. **Lemma C, names by vertex detection.** Let $O_c$ be the component c
   of `Operator ℓ` and $Γ_c = O_c × \mathsf F_λ$. The naming fibration
   $q_c : N_c → Γ_c$ interprets
   $N_c(ψ, F) = Σ_{G : \mathsf F_λ} (j_λ G = ψ(j_λ F))$, the homotopy
   pullback of $j_λ$ along $e_c(ψ, F) = ψ(j_λ F)$. It is this fibration
   that is claimed to be a Kan fibration, not $j_λ$ itself.
   - **Propositions:** by 6 each fiber is a proposition, so $q_c$ is
     (−1)-truncated.
   - **At a vertex** (ψ₀, F₀): F₀ is λ-small and λ is inaccessible, so
     in each degree the simplices of its index and of its total family
     number fewer than λ. Choose μ < λ with $|j_λ F_0| < μ$. Then
     $|ψ_0(j_λ F_0)| ≤ b_c(μ) < λ$, so the output is equivalent to a
     λ-small family. That family is a pullback of $U_λ$'s universal family
     (Cor. 2.1.12), so it is $j_λ G$ for some G. By univalence the
     equivalence is a path, so the fiber is nonempty.
   - **Section:** by Prop. 5.10, $q_c$ has a section. Its two components
     are `inner` and `inner-β`.
8. **Former names.** Convention: fix the structures of $U_κ$ first, and
   give each $U_λ$ their restrictions along $i_λ$ ("Restricted
   structures" under Facts), keeping the comparison $χ_λ$. Under it the formers commute with $i_λ$
   on the nose, and their names are given by refl. Without the convention
   a name is an identity of codes, which `Closure` accepts.
9. **Lemma D, assembly.** The $q_c$ form one fibration
   $q : ∐_c N_c → ∐_c Γ_c$, whose base is the context of an operator and a
   family in its carrier. Its fibers are propositions, nonempty at every
   vertex, so Prop. 5.10 applied once gives `inner` with `inner-β` over
   the whole context. Instances in other contexts are its pullbacks, not
   new choices. The carrier, `interpret` and the former names vary
   componentwise. These are terms in the context ψ : `Operator ℓ`, and
   abstraction gives the element of `Mahlo (Ambient.formers ℓ)`.

The vertex witnesses only show inhabitation; the section theorem produces
the coherent construction. Step 7 is where De Morgan cubical sets differ:
there, a (−1)-truncated fibration over a fibrant base can have nonempty
vertex fibers and no section (Model.md).

## Soundness obligation (an audit)

The interpretation in simplicial sets of the import cone of
`SPT.Mahlo.DS.Ambient` and `SPT.IR.Smallness`. Its 33
modules are all `--safe --without-K`, with no induction–recursion; the
only outside imports are `Agda.Primitive` and Agda's builtin types
(`Agda.Builtin.*`). Extensionality enters only as explicit hypotheses
(`SPT.Foundation.Extensionality`), which hold by univalence.

| Kind | In the cone | Interpretation | Status |
| --- | --- | --- | --- |
| KL's constructors | Π, Σ, universes, 𝟘, + | KL Thm 2.3.4; universes cumulative by the strict inclusion | Read |
| Records | Σ, 𝟙, `Lift`, `Signature`, `Algebra`, `Formers`, `Closure`, … | Iterated Σ with η | Standard |
| Non-indexed data | 𝟚, ℕ, `List`, `Maybe`, `⊎`, `Tag`, W, `DS` (arities in a universe) | Initial algebras of polynomials, KL's W-structure with 0, 1, + | Read (KL; Hugunin for the computation rules) |
| Identity type | `_＝_` | KL's Id-structure, J with strict β | Read |
| Indexed, variable targets | `SPT.Foundation.Tree` (history trees: children at `boundary o p`) | Checked W-trees, Σ (t : W) (Check t j), over one ordinary W-type with identity types, Σ, Π, ⊎ and ⊥ | Checked: [SPT.Foundation.Tree.W.Indexed](../Foundation/Tree/W/Indexed.agda); induction with both computation rules by refl, no extensionality |
| Indexed, non-variable target | `Generated.Operation` (`apply a : Operation (operation a)`) | The homotopy fiber Σ a, operation a ＝ c, with `apply a` at refl; matching by J | The device of the row above without recursion |
| Pattern matching | Every definition by cases | Translation to eliminators with the same reduction (Cockx Thms 4.27, 4.29) | Read; strength of the rules from §3.3; unifier as of Agda 2.5.1 |
| Unused | `Fin`, `_≤ℕˢ_` (re-exported by `SPT.Base` only) | None needed | Checked by scan |

Universe-polymorphic definitions are schemes over levels, and each closed
instance is interpreted. The cardinal and assembly logic of the
construction is checked in Agda (`Simplicial/`, cubical Agda
modules not included in this release):
- Lemma A (step 2), Lemma B (step 3) and the closure points with their
  constancy on components (steps 4–5);
- Lemma C at vertices (step 7);
- the section by vertex detection (step 9).
The external facts stay named hypotheses there:
- sizes and their invariance;
- the counting cover;
- Kapulkin–Lumsdaine's naming;
- Christensen's Prop. 5.10;
- the truncation of the naming fibration.
Reading those facts off simplicial sets in detail remains on paper. The source-to-core interpretation is
accounted for by the listed reductions and translation results, subject
to checking their application to the actual definitions. The
interpretation of the core theory's syntax in the model is not yet
built (Assumptions, "Syntax"). For the paper theorem the
construction can be stated in the supported Martin-Löf fragment with its
eliminators written out, so soundness of all of current Agda is not
needed.

## Relation to the other routes

- **The strict form** ([StrictMahlo.md](StrictMahlo.md)):
  `Strict-Mahlo`, every law an equality of maps, as LCTT's judgmental I1′
  needs. Its carrier is literal codes built by one chain over the
  operators, with the local Mahlo bounds only witnessing smallness, not
  this construction's U_λ, which has no strict `inner-β`.
- **De Morgan cubical sets** (Model.md): the same design,
  with closure points per path component by size. Vertex detection
  replaces discretization.
- **Background** (Cavallo–Sattler, *Eliminating reversals from cubical
  type theories*, LICS 2026, arXiv 2605.15080; abstract and introduction
  read). A model of cubical type theory with reversal and without
  connections whose homotopy theory is classically that of spaces. No
  such model with connections is known. It is not a model of cubical
  Agda's fragment.
