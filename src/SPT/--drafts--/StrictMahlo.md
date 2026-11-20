# The strict ambient Mahlo rule in simplicial sets

Status: proof on paper, 2026-11-03. The cardinal logic of §6 (the closure point of Lemma 6.4 and the induction of Lemma 6.7) is checked in Agda against named hypotheses (`StrictMahlo/`, cubical Agda modules not included in this release); everything else is proved here on paper. Cited facts are from Kapulkin–Lumsdaine (KL, arXiv 1211.2851, read) and from Annenkov–Capriotti–Kraus–Sattler (ACKS, arXiv 1705.03307v4, §2.5.1 read), with their numbers.

The construction reads Mahlo as resident operator dynamics: the decoding a child returns is the parent's decoding pulled back along the child's code map, never a rebuilt one, and residence names the base of that pullback by a parent code. It is one chain over the operators, with local Mahlo bounds.

[Simplicial.md](Simplicial.md) gives the ambient Mahlo rule in simplicial sets with its law `inner-β` an identification. This document gives the strict form that LCTT's judgmental I1′ needs: `Strict-Mahlo` of [TwoLevel/Mahlo](../TwoLevel/Mahlo.agda), every law an equality of maps.

## 0. Results

Fix a strongly Mahlo cardinal $\kappa$: $\kappa$ is inaccessible (uncountable, regular, strong limit) and the inaccessible cardinals below $\kappa$ form a stationary subset of $\kappa$. Let $U$ be a graded universe at $\kappa$ (Definition 1.3), with universal fibration $\pi : \tilde U \to U$, simplicial set of families $F$ (§2) and simplicial set of operators $O := F^F$.

**Theorem A.** There are a map $r : O \to U$ and, writing $R := r^{\ast}\tilde U \to O$ for the pulled-back family and $F_R$, $I_R$, $J_R$ for its families, identity data and readout (§3):

- a map $i : R \to U$ (the interpretation);
- sections $e_0, e_1, e_2, e_{\mathbb N}$ of $R \to O$;
- maps over $O$: $\mathsf{product}, \mathsf{sum}, \mathsf{tree} : F_R \to R$, $\mathsf{identity} : I_R \to R$ and $\mathsf{inner} : F_R \to F_R$;

such that the following are equalities of maps of simplicial sets:

$$
\begin{gathered}
i \circ e_0 = 0_U, \quad i \circ e_1 = 1_U, \quad i \circ e_2 = 2_U, \quad i \circ e_{\mathbb N} = \mathbb N_U, \\
i \circ \mathsf{product} = \Pi_U \circ J_R, \quad i \circ \mathsf{sum} = \Sigma_U \circ J_R, \quad i \circ \mathsf{tree} = W_U \circ J_R, \\
i \circ \mathsf{identity} = \mathrm{Id}_U \circ (\mathrm{pr}_2, \mathrm{pr}_3), \\
J_R \circ \mathsf{inner} = \mathrm{ev} \circ (p_F, J_R).
\end{gathered}
$$

Here $0_U, \ldots, \mathrm{Id}_U$ are the parent's chosen formers, $\mathrm{ev} : O \times F \to F$ is evaluation and $p_F : F_R \to O$ the projection. Read with $(R, i)$: every operator $\Psi$ has a child $r(\Psi)$, a code of the parent, whose points are interpreted by $i$ and closed under every former and under $\Psi$, with every decoding law literal.

**Corollary B.** In a model of two-level type theory in simplicial sets whose fibrant universe at level $\ell$ is a graded universe at a strongly Mahlo $\kappa$ (assumption T1, §1.3), the outer type `Strict-Mahlo (Ambient.formers ℓ)` has a global element.

**Corollary C** (conditional on T2, §1.3). With a strongly Mahlo cardinal for the level of every stratum (`Stratum` has the $\omega$ strata `𝓤₀`, `next 𝓤₀`, …) and an inaccessible cardinal above all of them (ACKS's universe $M_\omega$, T1), LCTT's syntax with every rule has no closed term of empty (Theory/Formal/Standard/Consistency, `consistent-with-mahlo`), relative to ZFC with those cardinals, in a model whose closed types are Kan complexes and whose fibrant universes are univalent (KL Theorem 3.4.1; ACKS §2.5.1).

The Mahlo property is used once, in Lemma 6.4: it makes the chain of each operator simplex stop at a stage below $\kappa$ (Lemma 6.8), and every stage below $\kappa$ is $\kappa$-small because $\kappa$ is inaccessible (Lemma 6.9), so the carrier is small (§7). A second proof of the stop takes the closure point for the chain's own growth instead of the grading (Lemmas 6.11, 6.12); it uses Mahlo once, in Lemma 6.11, and needs only (U1) and (U2) of Definition 1.3 (Remark 6.13). The closure (§3–§5) uses only that $\kappa$ is inaccessible: closure is free, and Mahlo is residence (Mahlo/Residence/README). The closure is moreover the initial algebra of its step functor, in every context (Proposition 5.5), so the model has strict induction over child codes (Corollary 7.3), which `Strict-Mahlo` does not ask for.

## 1. Conventions and cited facts

### 1.1 Sizes

For a simplicial set $X$, $\lVert X\rVert$ is the cardinality of the set of all its simplices, of every dimension. For a map $f : Y \to X$ and an $m$-simplex $x : \Delta^m \to X$, the fiber of $f$ over $x$ is the set $f^{-1}(x) \subseteq Y_m$ (KL Def. 2.1.1), and $f$ is $\mu$-small when every such fiber has fewer than $\mu$ elements (KL Def. 2.1.3). The pullback $x^{\ast}Y \to \Delta^m$ is the standard one, $x^{\ast}Y := \lbrace (t, y) \in \Delta^m \times Y \mid x(t) = f(y) \rbrace$, dimensionwise. For an ordinal $\xi$, $\xi^{+}$ is the least cardinal greater than $\xi$, that is $|\xi|^{+}$ for infinite $\xi$.

**Lemma 1.1.** Let $\mu$ be an uncountable regular cardinal.

1. $f : Y \to X$ is $\mu$-small iff $\lVert x^{\ast}Y\rVert < \mu$ for every simplex $x$ of $X$.
2. If $f$ is $\mu$-small and $\lVert X\rVert < \mu$ then $\lVert Y\rVert < \mu$.

*Proof.* (1) The simplices of $x^{\ast}Y$ over the countably many simplices $x\theta$ of $\Delta^m$ correspond to the fibers $f^{-1}(x\theta)$; a countable union of sets of size $< \mu$ has size $< \mu$, and conversely each fiber $f^{-1}(x)$ sits inside $x^{\ast}Y$. (2) $Y$ is the union of the fibers over the fewer than $\mu$ simplices of $X$, each of size $< \mu$; $\mu$ is regular. ∎

### 1.2 Kapulkin–Lumsdaine

For a regular cardinal $\alpha$, KL build $U_\alpha$ from Scott's-trick representatives of isomorphism classes of $\alpha$-small well-ordered fibrations: the $n$-simplices of $U_\alpha$ are those classes over $\Delta^n$, and $p_\alpha : \tilde U_\alpha \to U_\alpha$ is the universal one, its fiber over an $n$-simplex $c$ being the main fiber of $c$ (KL §2.1, Def. 2.1.3, Notation 2.1.6, Def. 2.1.9).

- **K1** (Lemma 2.1.10) $p_\alpha$ is a Kan fibration.
- **K2** (Corollary 2.1.12) $p_\alpha$ is strictly universal for $\alpha$-small well-ordered fibrations and weakly universal for $\alpha$-small fibrations: every $\alpha$-small Kan fibration $Y \to X$ is isomorphic over $X$ to $x^{\ast}\tilde U_\alpha$ for some $x : X \to U_\alpha$.
- **K3** (Theorem 2.2.1) $U_\alpha$ is a Kan complex.
- **K4** (Lemma 2.3.1) For Kan fibrations $Z \to Y \to X$, the dependent product of $Z \to Y$ along $Y \to X$ is a Kan fibration over $X$. (A fact about simplicial sets, used for every base below.)
- **K5** (Theorem 2.3.4) For $\alpha$ inaccessible, $U_\alpha$ carries Π-, Σ-, Id-, W-, 1-, 0- and +-structures; for an inaccessible $\beta < \alpha$ the composite of each structure with the inclusion $i : U_\beta \to U_\alpha$ lands in $U_\beta$ and factors through $i$ ("$U_\beta$ gives an internal universe in $U_\alpha$ closed under all these constructors").
- **K6** (construction, §2.1) Scott's-trick representatives do not depend on the bound, so for $\beta < \alpha$ the inclusion $i$ is a literal inclusion of sub-simplicial sets, $U_\beta(n) \subseteq U_\alpha(n)$, with $\tilde U_\beta = i^{\ast}\tilde U_\alpha$; and an $n$-simplex $c$ of $U_\alpha$ lies in $U_\beta$ iff $c$ is $\beta$-small.

### 1.3 Graded universes and two-level type theory

Write, for any Kan fibration $\pi : \tilde U \to U$, $F$ for its simplicial set of families (§2.1).

**Definition 1.3.** A *graded universe* at $\kappa$ is a Kan fibration $\pi : \tilde U \to U$ together with:

- **(U1)** $\pi$ is $\kappa$-small, and every $\kappa$-small Kan fibration $Y \to X$ is isomorphic over $X$ to $x^{\ast}\tilde U$ for some $x : X \to U$;
- **(U2)** maps $\Pi_U, \Sigma_U, W_U : F \to U$ and $\mathrm{Id}_U : \tilde U \times_U \tilde U \to U$, and vertices $0_U, 1_U, 2_U, \mathbb N_U$ of $U$ (the parent's formers);
- **(U3)** for every inaccessible $\lambda < \kappa$, a sub-simplicial set $U_\lambda \subseteq U$ containing the four vertices, every simplex of which is $\lambda$-small, and closed under the formers: writing $F_\lambda \subseteq F$ for the families $(c, \beta)$ with $c$ in $U_\lambda$ and $\beta$ landing in $U_\lambda$, the maps $\Pi_U, \Sigma_U, W_U$ send $F_\lambda$ into $U_\lambda$, and $\mathrm{Id}_U$ sends pairs over $U_\lambda$ into $U_\lambda$;
- **(U4)** an ordinal-valued size $\rho$ on the simplices of $F$ such that
  - (a) for every inaccessible $\lambda < \kappa$, a simplex $G$ of $F$ lies in $F_\lambda$ iff $\rho(G) < \lambda$;
  - (b) $\rho(G) < \kappa$ for every $G$;
  - (c) for every uncountable cardinal $\mu < \kappa$, fewer than $\kappa$ simplices $G$ of $F$ have $\rho(G) < \mu$.

**Lemma 1.4.** KL's $U_\kappa$, with $U_\lambda :=$ its sub-simplicial set $U_\lambda$ (K6) and $\rho(c, \beta) := \lVert c^{\ast}\tilde U\rVert + \lVert \beta^{\ast}\tilde U\rVert$ ($\beta^{\ast}\tilde U$ the pullback of $\tilde U$ along $\beta$), is a graded universe at $\kappa$.

*Proof.* (U1): K1, K2 and the construction. (U2): K5, with $2_U$ the sum of two copies of $1_U$ and $\mathbb N_U$ the code of the natural numbers built from the W-, 0-, 1- and +-structures (KL's W-types; Hugunin for the computation rules, as in Simplicial.md). (U3): K5, K6; the four vertices have countable diagrams, so they are $\lambda$-small for every uncountable $\lambda$. (U4a): if $c$ lies in $U_\lambda$, $c^{\ast}\tilde U \to \Delta^m$ is $\lambda$-small, so $\lVert c^{\ast}\tilde U\rVert < \lambda$ (Lemma 1.1); if $\beta$ lands in $U_\lambda$, $\beta^{\ast}\tilde U \to c^{\ast}\tilde U$ is $\lambda$-small over fewer than $\lambda$ simplices, so $\lVert \beta^{\ast}\tilde U\rVert < \lambda$. Conversely, if $\lVert c^{\ast}\tilde U\rVert < \lambda$ then $c$ is $\lambda$-small, so $c$ lies in $U_\lambda$ (K6); and for a $k$-simplex $z$ of $c^{\ast}\tilde U$ and $\theta : [j] \to [k]$, the fiber of $\beta(z)$'s representative over $\theta$ is the main fiber of $\beta(z\theta)$, a fiber of $\beta^{\ast}\tilde U \to c^{\ast}\tilde U$, so of size $< \lambda$; hence $\beta(z)$ is $\lambda$-small and lies in $U_\lambda$. (U4b): the same with $\kappa$. (U4c): first, a simplex $u$ of $U$ with $\lVert u^{\ast}\tilde U\rVert < \mu$ is (the representative of) an isomorphism class of well-ordered fibrations over some $\Delta^m$ of total size $< \mu$; each class has a member whose simplices form a subset of $\mu$, and its structure (faces, degeneracies, the map to $\Delta^m$, the well-orderings) is a function between sets of size at most $\mu$, so there are at most $\aleph_0 \cdot 2^{\mu} = 2^{\mu}$ such $u$. Next, a pair $(c, \beta)$ with $\rho(c, \beta) < \mu$ has $\lVert c^{\ast}\tilde U\rVert < \mu$, so at most $2^{\mu}$ choices of $c$; and $\beta$ is determined by its values on the fewer than $\mu$ simplices $z$ of $c^{\ast}\tilde U$, each a simplex $u = \beta(z)$ with $\lVert u^{\ast}\tilde U\rVert \le \aleph_0 \cdot \lVert \beta^{\ast}\tilde U\rVert < \mu$ (the fiber of $u^{\ast}\tilde U$ over $\theta$ is the fiber of $\beta^{\ast}\tilde U$ over $z\theta$, and $\mu$ is uncountable), so at most $(2^{\mu})^{\mu} = 2^{\mu}$ choices of $\beta$. In all at most $2^{\mu} < \kappa$, $\kappa$ being a strong limit. ∎

**Remark 1.5 (the universes of ACKS's simplicial model).** In ACKS §2.5.1 the outer level is the presheaf model over Grothendieck universes $M_0 \in M_1 \in \cdots$ and the inner universe at $j$ is the representing object of the inner types valued in $M_j$ (Hofmann–Streicher). Take $M_j = V_{\kappa_j}$ with $\kappa_j$ strongly Mahlo, and $U_\lambda :=$ the inner types valued in $V_\lambda$ for inaccessible $\lambda < \kappa_j$. For $\rho(G)$ take the rank of the whole diagram of $G = (c, \beta)$, in place of the cardinality of Lemma 1.4: the simplicial set $c^{\ast}\tilde U$ with its faces and degeneracies, and $\beta$ with the diagram of every $\beta(z)$. Then $V_\lambda$ is closed under the set-theoretic constructions of the formers (U3); $G$ lies in $F_\lambda$ iff $\rho(G) < \lambda$ (U4a), since a diagram of rank $< \lambda$ has its values in $V_\lambda$, and conversely for $G$ in $F_\lambda$ the diagram has fewer than $\lambda$ parts, each of rank $< \lambda$, and $\lambda$ is regular; $\rho(G) < \kappa_j$ likewise (U4b); and the $G$ with $\rho(G) < \mu$ lie in $V_\mu$, with $|V_\mu| < \kappa_j$ (U4c). ACKS's subsection gives Π, Σ, identity, empty, coproduct and natural-number types, not W-types. For (U2) take the W-type of KL Theorem 2.3.4, a Kan fibration (KL, citing van den Berg–Moerdijk, whose absolute Theorem 3.4 is read with its corrigendum), presented by one fixed construction: van den Berg–Moerdijk's hereditarily natural trees (their W-types paper, §2.2), the same construction under every reindexing. An arbitrary isomorphic presentation need not preserve set rank, which is why the construction is fixed. The grading is then local over each input simplex: for $G$ in $F_\lambda$, the whole diagram of $G$ has fewer than $\lambda$ arities, each of size $< \lambda$, so all are bounded by some $\eta < \lambda$; for an uncountable regular $\nu$ with $\eta < \nu < \lambda$, the stages of the trees through $\nu$ stay in $V_\lambda$, and $W_U(G)$ lies in $U_\lambda$. A global family valued in $V_\lambda$ over a large base need not have one common stopping stage below $\lambda$, so the claim is made simplex by simplex. This is our reading of their construction, on paper; ACKS state no grading.

**T1 (the model, assumed).** Agda's `--two-level` is read in a model of two-level type theory in simplicial sets as in ACKS §2.5.1: outer types are presheaves, outer Π, Σ and records are those of the presheaf topos, the strict equality `_≐_` is equality, and inner (fibrant) types are those whose display maps are Kan fibrations, closed under the outer 1, Σ, Π, empty, coproduct and natural-number types. Besides the universes $M_0 \in M_1 \in \cdots$ of the levels, the model has a further Grothendieck universe $M_\omega$ containing all of them, in which ACKS build the universal context that splits identity elimination compatibly with the change of size (ACKS §2.5.1, p. 16, following KL). Their footnote 9 avoids $M_\omega$ by tagging inner types with their size index; two tags of one type are then codes in different summands, with no path between them, so that universe is not univalent, and it is not used here. The fibrant universe `Set ℓ` is a graded universe at a strongly Mahlo $\kappa_\ell$, and Agda's fibrant formers at that level are its structures (U2). A closed outer type has as global elements its vertices; for an outer type of functions out of a fibrant type, a global element is a map of simplicial sets.

**T2 (soundness, assumed for Corollary C).** The Agda development behind `consistent-with-mahlo` (`--safe --without-K --two-level`, outer inductive families indexed by the fibrant strata) is sound for the model of T1, and its outer syntax, with a discrete fibrant index, is interpreted by its set-level initial algebra as a constant presheaf. This is an obligation of the kind Simplicial.md audits for its own cone; it is not checked here.

## 2. Families, operators and the parent's formers

Fix a graded universe $\pi : \tilde U \to U$ at $\kappa$.

**2.1 Families.** For an $m$-simplex $c$ of $U$ write $c^{\ast}\tilde U := \Delta^m \times_U \tilde U$; for $\theta : \Delta^k \to \Delta^m$ let $\hat\theta : (c\theta)^{\ast}\tilde U \to c^{\ast}\tilde U$, $(s, y) \mapsto (\theta(s), y)$. The simplicial set $F$ has as $m$-simplices the pairs $(c, \beta)$ with $c \in U_m$ and $\beta : c^{\ast}\tilde U \to U$ a map of simplicial sets; $\theta$ acts by $(c, \beta) \mapsto (c\theta, \beta \circ \hat\theta)$. This is the interpretation of `Family D` for the ambient family, $\Sigma_{c : U}\, (D\,c \to U)$.

**2.2 Operators.** $O := F^F$, the internal hom: an $n$-simplex of $O$ is a map $\sigma : \Delta^n \times F \to F$. Evaluation $\mathrm{ev} : O \times F \to F$ sends an $n$-simplex $(\sigma, G)$ to $\sigma_n(\iota_n, G)$, where $\iota_n$ is the top simplex of $\Delta^n$. This is `Operator D`.

**2.3 Formers.** The parent's formers are (U2). For an inaccessible $\lambda < \kappa$, $F_\lambda \subseteq F$ is as in (U3).

## 3. The step functor

Let $\mathcal S$ be the slice category of simplicial sets over $O \times U$: an object $A = (A, p, d)$ has $p : A \to O$ and $d : A \to U$, a morphism commutes with both. Only $p$ will ever be required to be a fibration; $d$ is the readout, the label of each code.

**3.1 Definition.** For $A$ in $\mathcal S$:

- **Decoded points.** $E_A := \lbrace (a, y) \in A \times \tilde U \mid d(a) = \pi(y) \rbrace$ dimensionwise, with $e_A : E_A \to A$. For an $n$-simplex $a$ of $A$, the pullback $a^{\ast}E_A$ is $(d \circ a)^{\ast}\tilde U$; we identify the two.
- **Families of the child.** $(F_A)_n$ is the set of pairs $(a, b)$ with $a \in A_n$ and $b : (d \circ a)^{\ast}\tilde U \to A$ a map with $p \circ b = (p \circ a) \circ \mathrm{pr}$, $\mathrm{pr}$ the projection to $\Delta^n$; $\theta$ acts by $(a, b) \mapsto (a\theta, b \circ \hat\theta)$. Put $p_F(a, b) := p(a)$.
- **Readout.** $J_A : F_A \to F$, $J_A(a, b) := (d \circ a, d \circ b)$. This is `map D (interpret Ψ)`.
- **Operator output.** $\mathrm{out}_A : F_A \to F$, $\mathrm{out}_A(a, b) := \mathrm{ev}(p(a), J_A(a, b))$, written $(c_{a,b}, \beta_{a,b})$.
- **Identity data.** $I_A := E_A \times_A E_A$: triples $(a, y, y')$ with $\pi(y) = \pi(y') = d(a)$.
- **Branch data.** $(B_A)_n$ is the set of pairs $((a, b), y)$ with $(a, b) \in (F_A)_n$, $y \in \tilde U_n$ and $\pi(y) = c_{a,b}$.
- **The step.** $H(A)$ is the coproduct of four copies of $O$ (tags $\mathbf 0$, $\mathbf 1$, $\mathbf 2$, $\mathbb N$), four copies of $F_A$ (tags $\Pi$, $\Sigma$, $W$, $\mathsf{res}$), $I_A$ (tag $\mathsf{Id}$) and $B_A$ (tag $\mathsf{br}$), with $p_H$ the identity on the $O$ summands, $p_F$ on the $F$ summands, $p \circ \mathrm{pr}_A$ on $I_A$ ($\mathrm{pr}_A(a, y, y') := a$) and $p_F \circ \mathrm{pr}$ on $B_A$ ($\mathrm{pr}$ the projection to $F_A$), and the readout $d_H$ displayed below.
- **On morphisms.** For $f : A \to A'$ in $\mathcal S$, $H(f)$ is the identity on the $O$ summands, $(a, b) \mapsto (f a, f \circ b)$ on the $F$ summands, $(a, y, y') \mapsto (f a, y, y')$ and $((a, b), y) \mapsto ((f a, f \circ b), y)$.

The readout of $H(A)$, with the four constants degenerated to the dimension of $o$:

$$
\begin{aligned}
d_H(\mathbf 0, o) &:= 0_U, \quad d_H(\mathbf 1, o) := 1_U, \quad d_H(\mathbf 2, o) := 2_U, \quad d_H(\mathbb N, o) := \mathbb N_U, \\
d_H(\Pi, (a, b)) &:= \Pi_U(J_A(a, b)), \quad \text{likewise } \Sigma \text{ and } W, \\
d_H(\mathsf{res}, (a, b)) &:= c_{a,b}, \\
d_H(\mathsf{Id}, (a, y, y')) &:= \mathrm{Id}_U(y, y'), \\
d_H(\mathsf{br}, ((a, b), y)) &:= \beta_{a,b}(\iota_n, y).
\end{aligned}
$$

**Lemma 3.2.** $H$ is an endofunctor of $\mathcal S$ and preserves monomorphisms.

*Proof.* $F_A$ is a simplicial set: $\theta^{\ast}(a, b)$ again satisfies $p \circ b \circ \hat\theta = (p \circ a\theta) \circ \mathrm{pr}$. $J_A$ and $\mathrm{out}_A$ are composites of simplicial maps. The readout $d_H$ is simplicial: for $\mathsf{res}$, $c_{\theta^{\ast}(a,b)} = \theta^{\ast}c_{a,b}$ because $\mathrm{out}_A$ is simplicial; for $\mathsf{br}$, $\beta_{\theta^{\ast}(a,b)} = \beta_{a,b} \circ \hat\theta$, so $d_H(\theta^{\ast}((a, b), y)) = \beta_{a,b}(\theta, y\theta) = \theta^{\ast}(\beta_{a,b}(\iota_n, y))$. For $f$ in $\mathcal S$, $d' \circ f = d$ gives $(d' \circ f \circ a)^{\ast}\tilde U = (d \circ a)^{\ast}\tilde U$, so $f \circ b$ has the right domain, and $J_{A'}(f a, f \circ b) = J_A(a, b)$; with $p' \circ f = p$ also $\mathrm{out}_{A'}(f a, f \circ b) = \mathrm{out}_A(a, b)$. So $H(f)$ preserves every label, every projection, and the condition $\pi(y) = c_{a,b}$: it is a morphism of $\mathcal S$. Functoriality is immediate. If $f$ is injective on simplices, so is $H(f)$ on each summand. ∎

**Lemma 3.3 (base change).** For $g : O' \to O$ let $\mathcal S'$ be the slice over $O' \times U$ and $H'$ its step functor built with the operator family $\mathrm{ev} \circ (g \times F) : O' \times F \to F$, that is, $\mathrm{out}'(a, b) := \mathrm{ev}(g(p'(a)), J(a, b))$. Pullback $g^{\ast} : \mathcal S \to \mathcal S'$, $g^{\ast}A := O' \times_O A$ with $d \circ \mathrm{pr}_2$, satisfies $g^{\ast}(H(A)) \cong H'(g^{\ast}A)$ naturally in $A$, compatibly with readouts.

*Proof.* Summand by summand. $g^{\ast}$ preserves coproducts and pullbacks. For families, an $n$-simplex $(o', (a, b))$ of $g^{\ast}F_A$ with $g(o') = p(a)$ corresponds to $((o', a), (o' \circ \mathrm{pr}, b))$ in $F'_{g^{\ast}A}$, with the same domain $(d \circ a)^{\ast}\tilde U$; the readouts agree, and $\mathrm{out}'$ uses $g(o') = p(a)$, so the labels agree. Identity and branch data likewise. Naturality in $A$ is clear. ∎

## 4. Fibrancy

**Lemma 4.1.** If $p : A \to O$ is a Kan fibration, so is $p_H : H(A) \to O$.

*Proof.* $e_A$ is the pullback of $\pi$ along $d$, a Kan fibration (U1). Let $Z := E_A \times_O A$, the pullback of $p$ along $p \circ e_A$, a Kan fibration over $E_A$. An $n$-simplex of the dependent product of $Z \to E_A$ along $e_A$, over an $n$-simplex $a$ of $A$, is a section of $Z$ over $(d \circ a)^{\ast}\tilde U$, that is, a map $b : (d \circ a)^{\ast}\tilde U \to A$ with $p \circ b = (p \circ a) \circ \mathrm{pr}$. So $F_A \to A$ is that dependent product, a Kan fibration by K4, and $F_A \to O$ is one as a composite. $I_A \to A$ is the composite $I_A \to E_A \to A$ of Kan fibrations, the first the pullback of $e_A$ along $e_A$, and $I_A \to O$ its composite with $p$; $B_A \to F_A$ is the pullback of $\pi$ along $(a, b) \mapsto c_{a,b}$, and $B_A \to O$ its composite with $p_F$; $O \to O$ is the identity. A coproduct of Kan fibrations over $O$ is one, since horns are connected. ∎

**Lemma 4.2.** A filtered colimit, over $O$, of Kan fibrations over $O$ is a Kan fibration over $O$.

*Proof.* A horn $\Lambda^n_k$ has finitely many non-degenerate simplices, so a map from it into a filtered colimit factors through a stage; lift there. ∎

## 5. The global chain

**5.1 Construction.** Define $A_\alpha$ in $\mathcal S$ for ordinals $\alpha$: $A_0 := \emptyset$; $A_{\alpha+1} := H(A_\alpha)$; $A_\delta := \operatorname{colim}_{\alpha<\delta} A_\alpha$ at a limit $\delta$. Transitions: $\iota_{0,1}$ is the unique map, $\iota_{\alpha+1,\beta+1} := H(\iota_{\alpha,\beta})$, and at a limit $\delta$ the colimit maps, with $\iota_{\delta,\delta+1}$ induced by the cocone $H(\iota_{\alpha,\delta}) : A_{\alpha+1} \to H(A_\delta)$, $\alpha < \delta$, since the $A_{\alpha+1}$ are cofinal below $\delta$.

**Lemma 5.2.** Every transition is a monomorphism, so $A_\delta = \bigcup_{\alpha<\delta} A_\alpha$; every $p_\alpha : A_\alpha \to O$ is a Kan fibration; every label $d(a)$ is a simplex of $U$.

*Proof.* Induction on $\beta$, for all transitions $\iota_{\alpha,\beta}$ with $\alpha \le \beta$. At a successor, $\iota_{\alpha+1,\beta+1} = H(\iota_{\alpha,\beta})$ is a mono by Lemma 3.2. At a limit $\delta$, the colimit maps of a chain of monos are monos, and $\iota_{\delta,\delta+1}$ is injective because every $H(\iota_{\alpha,\delta})$ is (Lemma 3.2) and the $A_{\alpha+1}$ exhaust $A_\delta$. Fibrancy: $\emptyset \to O$ has no horn to lift, Lemma 4.1 at successors, Lemma 4.2 at limits. ∎

**Lemma 5.3 (comparison).** Let $\delta$ be an uncountable regular cardinal and suppose $\lVert (d \circ a)^{\ast}\tilde U\rVert < \delta$ for every simplex $a$ of $A_\delta$. Then $\iota_{\delta,\delta+1} : A_\delta \to H(A_\delta)$ is an isomorphism, and so is $\iota_{\delta,\beta}$ for every $\beta \ge \delta$.

*Proof.* $\iota_{\delta,\delta+1}$ is the comparison $\operatorname{colim}_{\alpha<\delta} H(A_\alpha) \to H(A_\delta)$. It is injective: each $H(\iota_{\alpha,\delta})$ is (Lemmas 3.2, 5.2), and the colimit of a chain of monos into a common object is a union. It is surjective: an $n$-simplex of an $O$ summand already lies in $H(A_0)$; an $n$-simplex $(a, b)$ of an $F$ summand has $a$ in some $A_{\alpha_0}$ and $b$ with domain $(d \circ a)^{\ast}\tilde U$ of fewer than $\delta$ simplices, each sent into some stage, so, $\delta$ being regular, $b$ lands in one stage $A_{\alpha_1}$ as a simplicial map; then $(a, b)$ lies in $F_{A_\alpha}$ for $\alpha := \max(\alpha_0, \alpha_1)$. Identity and branch simplices carry no further data from $A$ (the condition $\pi(y) = c_{a,b}$ is the same computed in $A_\alpha$, since $\mathrm{out}$ commutes with $\iota$). Finally, if $\iota_{\beta,\beta+1}$ is an isomorphism then so is $\iota_{\beta+1,\beta+2} = H(\iota_{\beta,\beta+1})$; at a limit $\beta > \delta$ every transition from $\delta$ on is an isomorphism, so $A_\beta \cong A_\delta$ and $\iota_{\beta,\beta+1}$ corresponds to $\iota_{\delta,\delta+1}$. ∎

**Proposition 5.4.** Put $A := A_\kappa$ and $\theta := \iota_{\kappa,\kappa+1}^{-1} : H(A) \to A$. Then $(A, \theta)$ is an $H$-algebra in $\mathcal S$, and $p : A \to O$ is a Kan fibration.

*Proof.* Every label of $A$ is a simplex $c$ of $U$, and $\lVert c^{\ast}\tilde U\rVert < \kappa$ by (U1) and Lemma 1.1; $\kappa$ is regular and uncountable, so Lemma 5.3 applies with $\delta := \kappa$. $\theta$ is a morphism of $\mathcal S$, so $p \circ \theta = p_H$ and $d \circ \theta = d_H$. Lemma 5.2. ∎

**Proposition 5.5 (initiality).** $(A, \theta)$ is an initial $H$-algebra in $\mathcal S$. For every $g : O' \to O$, $g^{\ast}(A, \theta)$ is an initial $H'$-algebra in $\mathcal S'$, for the step functor $H'$ of Lemma 3.3.

*Proof.* Let $(X, \xi)$ be an $H$-algebra. Define morphisms $h_\alpha : A_\alpha \to X$ by $h_0 :=$ the empty map, $h_{\alpha+1} := \xi \circ H(h_\alpha)$, and at a limit $\delta$ the map induced by the $h_\alpha$, $\alpha < \delta$. By induction, $h_\beta \circ \iota_{\alpha,\beta} = h_\alpha$ for $\alpha \le \beta$: at successors $h_{\beta+1} \circ H(\iota_{\alpha,\beta}) = \xi \circ H(h_\beta \circ \iota_{\alpha,\beta}) = h_{\alpha+1}$; at a limit $\delta$, $h_{\delta+1} \circ \iota_{\delta,\delta+1}$ agrees with $h_\delta$ on each $A_{\alpha+1}$, $\alpha < \delta$, because $\iota_{\delta,\delta+1} \circ \iota_{\alpha+1,\delta} = H(\iota_{\alpha,\delta})$, and these exhaust $A_\delta$. Put $h := h_\kappa$. From $h_{\kappa+1} \circ \iota_{\kappa,\kappa+1} = h_\kappa$, $h \circ \theta = h_{\kappa+1} = \xi \circ H(h)$: $h$ is a morphism of algebras. If $k : A \to X$ is another, then $k \circ \iota_{\alpha,\kappa} = h_\alpha$ for every $\alpha \le \kappa$, by induction: $\iota_{\alpha+1,\kappa} = \theta \circ H(\iota_{\alpha,\kappa})$ gives $k \circ \iota_{\alpha+1,\kappa} = \xi \circ H(k \circ \iota_{\alpha,\kappa})$, and limits are colimits; at $\alpha = \kappa$, $k = h$. This is Adámek's argument, and it uses only that the chain starts at the initial object $\emptyset$ and that $\iota_{\kappa,\kappa+1}$ is an isomorphism. For $g$, $g^{\ast}A_\alpha$ is the chain of $H'$ compatibly with transitions (as in Lemma 6.1, by Lemma 3.3 and since $g^{\ast}$ preserves colimits), and $g^{\ast}\iota_{\kappa,\kappa+1}$ is an isomorphism, so the same argument applies. ∎

**Remark 5.6 (Mahlo/Heights).** [Heights/Regular](../Mahlo/Heights/Regular.agda) states the bound of Lemma 5.3 inside type theory, for stages indexed by trees instead of ordinals: a node is regular for an operator $\Phi$ when every code of its stage, together with a family of codes indexed by that code's decoding, lies below one child (the field `bound`). That is the surjectivity in the proof of Lemma 5.3: the head and the whole branch map lie in one stage. At a regular node the stage is a closure of the formers and $\Phi$, built by recursion on the height (`mahlo`), as $A_\delta$ is an $H$-algebra here; and a closure of $\Phi$ gives a regular height for $\Phi$'s stages (`regular`). So in type theory, under extensionality for families of types, the ambient rule holds exactly when every operator has a regular height. The two constructions are different objects: there the stages are indexed by trees and `inner-β` is an identification (`ap Φ (moved F)`), here they are indexed by ordinals and every law is an equality of maps. What they share is the bounding mechanism, not a carrier.

So the closure exists over the whole operator space at once, with every label literal, using only that $\kappa$ is inaccessible. What remains is that $A$ is small over $O$.

## 6. Local bounds

Fix an $n$-simplex $\sigma$ of $O$, that is, a map $\sigma : \Delta^n \times F \to F$. Let $\mathcal S^{\sigma}$ be the slice over $\Delta^n \times U$, $H^{\sigma}$ the step functor with operator family $\sigma$ (so $\mathrm{out}^{\sigma}(a, b) := \sigma_k(p(a), J(a, b))$ for a $k$-simplex $a$), and $A^{\sigma}_\alpha$ its chain (5.1).

**Lemma 6.1.** $\sigma^{\ast}A_\alpha \cong A^{\sigma}_\alpha$ naturally, compatibly with transitions; in particular $\sigma^{\ast}A \cong A^{\sigma}_\kappa$.

*Proof.* Induction on $\alpha$, by Lemma 3.3 with $g := \sigma$ ($\mathrm{ev} \circ (\sigma \times F)$ is $\sigma$, since $\sigma \circ t$ corresponds to $(s, G) \mapsto \sigma(t(s), G)$), and because $\sigma^{\ast}$ preserves colimits (the slice is a topos and $\sigma^{\ast}$ has a right adjoint). ∎

**Lemma 6.2 (literal size bound).** For every uncountable cardinal $\mu < \kappa$ let

$$
f(\mu) := \sup \lbrace \rho(\sigma_m(\theta, G)) \mid m \in \mathbb N,\ \theta : \Delta^m \to \Delta^n,\ G \in F_m,\ \rho(G) < \mu \rbrace.
$$

Then $f(\mu) < \kappa$.

*Proof.* By (U4c) there are fewer than $\kappa$ such $G$, and countably many pairs $(m, \theta)$; each value $\rho(\sigma_m(\theta, G))$ is $< \kappa$ by (U4b); $\kappa$ is regular. ∎

**Lemma 6.3 (closure points).** The set $C$ of uncountable limit cardinals $\lambda < \kappa$ with $f(\mu) < \lambda$ for every uncountable cardinal $\mu < \lambda$ is closed and unbounded in $\kappa$.

*Proof.* Unbounded: from $\xi < \kappa$ put $\xi_0 := \max(\xi, \aleph_1)$ and $\xi_{k+1} := (\max(\xi_k, \sup \lbrace f(\mu) \mid \mu \le \xi_k \text{ an uncountable cardinal} \rbrace))^{+}$, a cardinal below $\kappa$ by Lemma 6.2, the regularity of $\kappa$ (fewer than $\kappa$ values) and $\kappa$ being a limit cardinal. The $\xi_k$ increase strictly, so $\lambda := \sup_k \xi_k$ is an uncountable limit cardinal, below $\kappa$ since $\operatorname{cf} \kappa > \omega$; and an uncountable cardinal $\mu < \lambda$ has $\mu \le \xi_k$ for some $k$, so $f(\mu) < \xi_{k+1} \le \lambda$. Closed: if $\lambda = \sup_i \lambda_i$ with every $\lambda_i$ in $C$ and $\mu < \lambda$, then $\mu < \lambda_i$ for some $i$, and $f(\mu) < \lambda_i \le \lambda$. ∎

**Lemma 6.4 (literal closure; Mahlo).** There is an inaccessible $\lambda < \kappa$ such that $\sigma_m(\theta, G) \in F_\lambda$ for every $m$, $\theta : \Delta^m \to \Delta^n$ and $G \in (F_\lambda)_m$.

*Proof.* The inaccessibles below $\kappa$ are stationary ($\kappa$ is strongly Mahlo), so one lies in the club $C$ of Lemma 6.3. For $G \in (F_\lambda)_m$, $\rho(G) < \lambda$ by (U4a); $\mu := \max(\aleph_1, \rho(G)^{+}) < \lambda$ since $\lambda$ is a limit cardinal; so $\rho(\sigma_m(\theta, G)) \le f(\mu) < \lambda$, and $\sigma_m(\theta, G) \in F_\lambda$ by (U4a). ∎

This is the only use of the Mahlo property. Fix this $\lambda$. Note that it depends on $\sigma$, and nothing below needs it to vary continuously with $\sigma$: $\lambda$ is a witness in the proof that $A$ is small, not part of $A$.

**Lemma 6.5 (the local strict algebra).** $\Lambda := \Delta^n \times U_\lambda$, with $p := \mathrm{pr}_1$ and $d := (U_\lambda \subseteq U) \circ \mathrm{pr}_2$, carries an $H^{\sigma}$-algebra structure $s : H^{\sigma}(\Lambda) \to \Lambda$ in $\mathcal S^{\sigma}$.

*Proof.* A family $(a, b)$ of $\Lambda$ over a $k$-simplex has $a = (t, c)$ with $c \in U_\lambda$ and $b = (t \circ \mathrm{pr}, \beta)$ with $\beta : c^{\ast}\tilde U \to U_\lambda$; so $J(a, b) = (c, \beta)$ lies in $F_\lambda$. Put

$$
\begin{aligned}
s(\mathbf 0, t) &:= (t, 0_U), \quad \text{and likewise } \mathbf 1, \mathbf 2, \mathbb N, \\
s(\Pi, (a, b)) &:= (t, \Pi_U(c, \beta)), \quad \text{likewise } \Sigma, W, \\
s(\mathsf{res}, (a, b)) &:= (t, c'), \quad \text{where } (c', \beta') := \sigma_k(t, (c, \beta)), \\
s(\mathsf{Id}, (a, y, y')) &:= (t, \mathrm{Id}_U(y, y')), \\
s(\mathsf{br}, ((a, b), y)) &:= (t, \beta'(\iota_k, y)).
\end{aligned}
$$

Each value lies in $U_\lambda$: the constants and the formers by (U3), $c'$ and $\beta'$ by Lemma 6.4. By construction $d \circ s = d_H$ and $p \circ s = p_H$, and $s$ is simplicial because each clause is. ∎

**Lemma 6.6 (labels).** There are morphisms $h_\alpha : A^{\sigma}_\alpha \to \Lambda$ in $\mathcal S^{\sigma}$ with $h_\beta \circ \iota_{\alpha,\beta} = h_\alpha$. In particular every label of $A^{\sigma}_\alpha$ lies in $U_\lambda$, so $\lVert (d \circ a)^{\ast}\tilde U\rVert < \lambda$ for every simplex $a$ of every $A^{\sigma}_\alpha$.

*Proof.* $h_0$ is the empty map, $h_{\alpha+1} := s \circ H^{\sigma}(h_\alpha)$, and at limits the induced map; compatibility by induction. Since $d_\Lambda$ factors through $U_\lambda$, so does $d = d_\Lambda \circ h_\alpha$; then (U3) and Lemma 1.1. ∎

**Lemma 6.7 (local size).** $\lVert A^{\sigma}_\alpha\rVert < \lambda$ for every $\alpha < \lambda$.

*Proof.* By induction on $\alpha < \lambda$, in the form checked in Agda (`StrictMahlo/Growth`, `growth`; cubical Agda, not included in this release): it suffices that for every $\alpha < \lambda$ and every cardinal $\gamma < \lambda$, if $\lVert A^{\sigma}_\beta\rVert < \gamma$ for all $\beta < \alpha$ then $\lVert A^{\sigma}_\alpha\rVert < \lambda$; the regularity of $\lambda$ supplies such a $\gamma$ from the induction hypothesis, since fewer than $\lambda$ stages lie below $\alpha$.

- $\alpha = 0$: $\lVert \emptyset\rVert = 0$.
- $\alpha = \beta + 1$, $X := A^{\sigma}_\beta$, $\lVert X\rVert < \gamma$: by Lemma 6.6 every label of $X$ has $\lVert (d \circ a)^{\ast}\tilde U\rVert < \lambda$. The $O$ summands contribute $\lVert \Delta^n\rVert = \aleph_0$. A family $(a, b)$ is a simplex $a$ of $X$ and a map from $(d \circ a)^{\ast}\tilde U$ to $X$, so $\lVert F_X\rVert \le \sum_a \lVert X\rVert^{\lVert (d \circ a)^{\ast}\tilde U\rVert} < \lambda$: each term is below $\lambda$ because $\lambda$ is a strong limit, and the sum has fewer than $\lambda$ terms. $\lVert I_X\rVert \le \sum_a \lVert (d \circ a)^{\ast}\tilde U\rVert^2 < \lambda$. A branch simplex is a family with a point of $c_{a,b}^{\ast}\tilde U$, and $c_{a,b}$ lies in $U_\lambda$ (it is the label of a result code, Lemma 6.6), so $\lVert B_X\rVert < \lambda$ likewise.
- $\alpha$ a limit: $\lVert A^{\sigma}_\alpha\rVert \le |\alpha| \cdot \gamma < \lambda$.

∎

**Lemma 6.8 (local stabilization).** $\iota^{\sigma}_{\lambda,\lambda+1}$ is an isomorphism, and $A^{\sigma}_\kappa \cong A^{\sigma}_\lambda$, with $\lVert A^{\sigma}_\lambda\rVert \le \lambda$.

*Proof.* Every label of $A^{\sigma}_\lambda$ lies in $U_\lambda$ (Lemma 6.6), so Lemma 5.3 applies with $\delta := \lambda$. $A^{\sigma}_\lambda$ is the union of the $\lambda$ stages below it, each of size $< \lambda$ (Lemma 6.7). ∎

**Lemma 6.9 (stages below $\kappa$).** $\lVert A^{\sigma}_\alpha\rVert < \kappa$ for every $\alpha < \kappa$.

*Proof.* As Lemma 6.7, with $\kappa$ for $\lambda$ and $U$ for $U_\lambda$: every label of every stage is a simplex $c$ of $U$, so $\lVert c^{\ast}\tilde U\rVert < \kappa$ by (U1) and Lemma 1.1, and $\kappa$ is a regular strong limit. At $\alpha = 0$, $\lVert \emptyset\rVert = 0$. At $\alpha = \beta + 1$, with $X := A^{\sigma}_\beta$ and $\lVert X\rVert < \kappa$: the $O$ summands contribute $\aleph_0$; $\lVert F_X\rVert \le \sum_a \lVert X\rVert^{\lVert (d \circ a)^{\ast}\tilde U\rVert} < \kappa$, a sum of fewer than $\kappa$ terms each below $\kappa$; $\lVert I_X\rVert \le \sum_a \lVert (d \circ a)^{\ast}\tilde U\rVert^2 < \kappa$; a branch simplex is a family with a point of $c_{a,b}^{\ast}\tilde U$, and $c_{a,b}$ is a simplex of $U$, so $\lVert B_X\rVert < \kappa$. At a limit $\alpha < \kappa$, $A^{\sigma}_\alpha$ is the union of fewer than $\kappa$ stages, each of size $< \kappa$, and $\kappa$ is regular. ∎

**Remark 6.10 (what Mahlo does).** Lemma 6.9 uses neither $\lambda$ nor Lemma 6.4: every stage below $\kappa$ is $\kappa$-small because $\kappa$ is inaccessible. What the Mahlo property adds, through Lemmas 6.4, 6.5, 6.6 and 5.3, is that the chain of $\sigma$ stops at a stage below $\kappa$, at $\lambda$; without it the chain of $\sigma$ may stop only at $\kappa$, whose stage need not be $\kappa$-small. So Theorem 7.1 needs Lemma 6.8 only for $A^{\sigma}_\kappa \cong A^{\sigma}_\lambda$, and Lemma 6.9 for the size; Lemma 6.7 gives the sharper bound $\lVert A^{\sigma}_\lambda\rVert \le \lambda$, which Theorem 7.1 does not need.

### A second proof of the stop, without the grading

Lemmas 6.2–6.8 bound the operator's outputs in advance, through the grading (U3), (U4). The stop at a stage below $\kappa$ also follows by taking the closure point for the chain's own growth. This needs only (U1) and Lemma 6.9.

**Lemma 6.11 (closure point of the growth; Mahlo).** For $\alpha < \kappa$ let $\zeta(\alpha)$ be the supremum of $\lVert A^{\sigma}_\alpha\rVert$ and of $\lVert (d \circ a)^{\ast}\tilde U\rVert$ over the simplices $a$ of $A^{\sigma}_\alpha$ (a supremum: a family of fewer than $\kappa$ cardinals need not attain it). Then $\zeta(\alpha) < \kappa$, and there is an inaccessible $\lambda < \kappa$ with $\zeta(\alpha) < \lambda$ for every $\alpha < \lambda$.

*Proof.* By Lemma 6.9, $A^{\sigma}_\alpha$ has fewer than $\kappa$ simplices. Each label $d(a)$ is a simplex of $U$, so $\lVert (d \circ a)^{\ast}\tilde U\rVert < \kappa$ by (U1) and Lemma 1.1, and $\kappa$ is regular. So $\zeta(\alpha) < \kappa$.

The limit cardinals $\lambda < \kappa$ with $\zeta(\alpha) < \lambda$ for every $\alpha < \lambda$ form a club in $\kappa$:
- they are closed, by definition;
- they are unbounded: from $\xi < \kappa$ put $\xi_0 := \xi$ and $\xi_{k+1} := (\max(\xi_k, \sup_{\alpha \le \xi_k} \zeta(\alpha)))^{+}$, below $\kappa$ by regularity, and take $\lambda := \sup_k \xi_k < \kappa$, since $\operatorname{cf} \kappa > \omega$.

The inaccessibles below $\kappa$ are stationary, so one lies in this club. In the function form, `MahloOrdinals` at $\zeta$ gives it directly, as `StrictMahlo/Closure` uses it for $f$. ∎

**Lemma 6.12 (local stabilization, without the grading).** With $\lambda$ as in Lemma 6.11, $\iota^{\sigma}_{\lambda,\lambda+1}$ is an isomorphism, $A^{\sigma}_\kappa \cong A^{\sigma}_\lambda$, and $\lVert A^{\sigma}_\lambda\rVert \le \lambda$.

*Proof.* Let $x$ be a simplex of $H^{\sigma}(A^{\sigma}_\lambda)$. Its inputs from $A^{\sigma}_\lambda$ are at most a head $a$ and a branch map $b : (d \circ a)^{\ast}\tilde U \to A^{\sigma}_\lambda$; the points $y$, $y'$ of the identity and branch summands are not inputs.
- **The head.** $a$ lies in a stage $A^{\sigma}_\beta$ with $\beta < \lambda$, so $\lVert (d \circ a)^{\ast}\tilde U\rVert \le \zeta(\beta) < \lambda$.
- **The branch map.** Its domain has fewer than $\lambda$ simplices, each in a stage below $\lambda$, so, $\lambda$ being regular, $b$ lands in one stage $A^{\sigma}_\gamma$ with $\gamma < \lambda$.

So $x$ lies in $H^{\sigma}(A^{\sigma}_{\max(\beta, \gamma)})$, a stage below $\lambda$, and the comparison map is onto. It is a monomorphism (Lemma 5.2), so it is an isomorphism, and so is every later transition (as in Lemma 5.3). $A^{\sigma}_\lambda$ is the union of the stages below $\lambda$, each with at most $\zeta(\alpha) < \lambda$ simplices, so $\lVert A^{\sigma}_\lambda\rVert \le \lambda$. ∎

**Remark 6.13 (what the second proof drops).** Lemmas 6.9, 6.11 and 6.12 use only (U1), Lemma 1.1, and that $\kappa$ is strongly Mahlo. They give what Theorem 7.1 takes from Lemmas 6.4–6.8: an inaccessible $\lambda < \kappa$ with $A^{\sigma}_\kappa \cong A^{\sigma}_\lambda$.
- **Weaker hypotheses.** Theorem A holds for any Kan fibration $\pi : \tilde U \to U$ with (U1) and (U2) at a strongly Mahlo $\kappa$. The grading (U3), (U4) is used only by the first proof, Lemmas 6.2–6.8. So are Lemma 1.4's clauses (U3), (U4) and Remark 1.5's rank reading. A W-structure is still needed for (U2).
- **The fibrant reading.** Corollaries B and C read Theorem A through T1, so they also need $U$ to be a Kan complex, as KL's universe is (K3); (U1) alone does not give this. Univalence is a property of the chosen KL or T1 universe, not a consequence of (U1).
- **No bound in advance.** The operator's output sizes need not be bounded in advance: the closure point is taken for the growth that the operator drives.
- **The same strength.** At an inaccessible $\kappa$, a stationary set of regular cardinals contains a stationary set of inaccessibles, the strong limits being a club. So asking only for a regular $\lambda$ in Lemma 6.11 would not lower the assumption.
- **What is checked.** The first proof stays as written, with its cardinal logic checked against named hypotheses (`StrictMahlo/`, cubical Agda, not included in this release). The second proof's cardinal steps are the same two: a closure point from `MahloOrdinals`, and regularity.
- **Universal induction–recursion.** [UniversalIR.md](UniversalIR.md), §4, uses this proof for every description. Its Theorem U contains Theorem A at the descriptions `Ambient.description Ψ` (UniversalIR.md, §10).

## 7. Smallness, residence and the strict structure

**Theorem 7.1.** $p : A \to O$ is a $\kappa$-small Kan fibration.

*Proof.* Kan by Proposition 5.4. For an $n$-simplex $\sigma$ of $O$, $\sigma^{\ast}A \cong A^{\sigma}_\kappa \cong A^{\sigma}_\lambda$ (Lemmas 6.1, 6.8; or Lemmas 6.1, 6.12, without the grading), a stage below $\kappa$, so $\lVert \sigma^{\ast}A\rVert < \kappa$ by Lemma 6.9 (Lemmas 6.8 and 6.12 give the sharper $\lVert \sigma^{\ast}A\rVert \le \lambda$); $p$ is $\kappa$-small by Lemma 1.1. ∎

**Theorem 7.2 (residence and the strict structure).** Theorem A holds.

*Proof.* By (U1) there are $r : O \to U$ and an isomorphism $\varphi : R \to A$ over $O$, $R := r^{\ast}\tilde U$. With $i := d \circ \varphi$, $\varphi$ is an isomorphism $(R, p_R, i) \cong (A, p, d)$ in $\mathcal S$, so $H(\varphi)$ is one too, and $\theta_R := \varphi^{-1} \circ \theta \circ H(\varphi) : H(R) \to R$ is an $H$-algebra in $\mathcal S$ with $i \circ \theta_R = d_{H(R)}$. Its components are the operations:

$$
\begin{aligned}
e_0 &:= \theta_R \circ \mathrm{in}_{\mathbf 0} \quad \text{(a section of } R \to O \text{), and likewise } e_1, e_2, e_{\mathbb N}, \\
\mathsf{product} &:= \theta_R \circ \mathrm{in}_{\Pi}, \quad \mathsf{sum} := \theta_R \circ \mathrm{in}_{\Sigma}, \quad \mathsf{tree} := \theta_R \circ \mathrm{in}_{W}, \\
\mathsf{identity} &:= \theta_R \circ \mathrm{in}_{\mathsf{Id}}, \quad \mathsf{result} := \theta_R \circ \mathrm{in}_{\mathsf{res}}, \quad \mathsf{branch} := \theta_R \circ \mathrm{in}_{\mathsf{br}}.
\end{aligned}
$$

The equation $i \circ \theta_R = d_{H(R)}$, read on each summand, is the list of laws in Theorem A except the last: $i \circ e_0 = 0_U$, …, $i \circ \mathsf{product} = \Pi_U \circ J_R$, …, $i \circ \mathsf{identity} = \mathrm{Id}_U \circ (\mathrm{pr}_2, \mathrm{pr}_3)$, and moreover $i(\mathsf{result}(a, b)) = c_{a,b}$ and $i(\mathsf{branch}((a, b), y)) = \beta_{a,b}(\iota_n, y)$.

For $\mathsf{inner}$, let $(a, b)$ be an $n$-simplex of $F_R$, and put $x := \mathsf{result}(a, b)$. Its label is literally $c_{a,b}$, so its decoded points are $c_{a,b}^{\ast}\tilde U$, and

$$
b' : c_{a,b}^{\ast}\tilde U \to R, \qquad b'(t, y) := \mathsf{branch}(t^{\ast}(a, b), y)
$$

is a map over $\Delta^n$ with $p_R \circ b' = (p_R \circ a) \circ \mathrm{pr}$. Put $\mathsf{inner}(a, b) := (x, b')$, a simplex of $F_R$, natural in $\theta$. Then

$$
\begin{gathered}
J_R(\mathsf{inner}(a, b)) = (c_{a,b}, i \circ b'), \\
(i \circ b')(t, y) = \beta_{t^{\ast}(a,b)}(\iota, y) = (\beta_{a,b} \circ \hat t)(\iota, y) = \beta_{a,b}(t, y),
\end{gathered}
$$

so $J_R(\mathsf{inner}(a, b)) = (c_{a,b}, \beta_{a,b}) = \mathrm{out}_R(a, b) = \mathrm{ev}(p_F(a, b), J_R(a, b))$: the last law. No transport occurs: the label of the result code is $c_{a,b}$ itself, which is the principle that the returned decoding is the parent's, pulled back. ∎

**Corollary 7.3 (induction over child codes).** Let $q : P \to R$ be a map (for instance a Kan fibration, a family over the child codes), made an object of $\mathcal S$ by $p_R \circ q$ and $i \circ q$, and $\xi : H(P) \to P$ a morphism of $\mathcal S$ with $q \circ \xi = \theta_R \circ H(q)$: the methods, one for each constructor, giving a point of $P$ over the constructed code from its inputs and points of $P$ over them. Then there is exactly one morphism of algebras $s : (R, \theta_R) \to (P, \xi)$, and $q \circ s = \mathrm{id}_R$. The same holds after base change along every $g : O' \to O$.

*Proof.* $\varphi$ is an isomorphism of algebras $(R, \theta_R) \cong (A, \theta)$, so $(R, \theta_R)$ is initial (Proposition 5.5), and so is $g^{\ast}(R, \theta_R)$. $q$ is a morphism of algebras, so $q \circ s$ and $\mathrm{id}_R$ are both morphisms of algebras from $(R, \theta_R)$ to itself, hence equal. ∎

The equation $s \circ \theta_R = \xi \circ H(s)$ gives the computation rules as equalities of maps.

## 8. The corollaries

**Proof of Corollary B.** Under T1, `Operator D` is $O$, `Family D` is $F$, `Set ℓ` is $U$ with $\pi$, and the fields of `Strict-Mahlo` are read as maps: `carrier` as $r$; `interpret` as a map over $O$ out of $R = \Sigma_{\Psi}\, D(\mathsf{carrier}\,\Psi)$, that is $i$; `empty`, …, `natural` as sections $e_0, \ldots$; `product`, `sum`, `tree` as maps over $O$ out of $F_R$, the interpretation of `Family (Decode D (interpret Ψ))` over $\Psi$; `identity` out of $I_R$; `inner` as $F_R \to F_R$. Each law `(λ Ψ … → x) ≐ (λ Ψ … → y)` is the equality of the two corresponding maps, and `map D (interpret Ψ)` is $J_R$. Theorem A gives all of them. ∎

**Proof of Corollary C.** Under T1 with a graded universe at a strongly Mahlo cardinal for the level of each stratum, and the universe $M_\omega$ above them all, Corollary B gives the hypothesis of `consistent-with-mahlo` in the model; under T2 its conclusion is interpreted as a map from the constant presheaf of closed terms of empty into the empty Kan complex, so there is no such term. ∎

## 9. Discriminators

1. **The constant operator at a large contractible complex.** For $\mu < \kappa$ let $X_\mu$ be the nerve of the indiscrete groupoid on $\mu$ objects and $\Phi_\mu$ the constant operator at the family $(X_\mu, \mathrm{const}\, 0_U)$. The result code of any family has label $c = X_\mu$ itself, by the definition of $d_H$ on $\mathsf{res}$, and its branches are labelled $0_U$. Simplicial.md's carrier $U_\lambda$, constant on the path component of $\Phi_\mu$, fails this for $\mu \ge \lambda$.
2. **One carrier along paths.** The $\Phi_\mu$ for $\mu < \kappa$ lie in one path component of $O$, and their literal sizes are unbounded below $\kappa$. Here they are points of one Kan fibration $A \to O$; the $\lambda$ of Lemma 6.4 at each $\Phi_\mu$ grows with $\mu$, but it bounds a fiber, it does not choose one.
3. **No fibrancy of $d$.** The readout $d : A \to U$ is not asked to be a fibration. A $\kappa$-small $A$ with a fibration $A \to U$ containing the unit code would have a code over every $\kappa$-small contractible complex, $\kappa$ many vertices.
4. **No fibrant replacement.** Every constructor of $H$ is a point constructor whose parameter space is a Kan fibration over $O$; the paths between codes are those of the parameters. Lumsdaine–Shulman's problems for higher inductive types (fibrant replacement of path constructors, which does not keep fibers small; the induction principle) do not arise: there are no path constructors, and the induction principle holds strictly (Proposition 5.5, Corollary 7.3), although `Strict-Mahlo` asks for no eliminator.
5. **Unique names are not obtained.** The interpretation $i$ is not an embedding (two codes can decode alike), so this carrier serves `Strict-Mahlo`, not Mahlo/DS/Univalent's `Reflector`. The two strengthenings use different carriers.

## 10. Checked, cited, proved here

| Item | Status |
| --- | --- |
| Lemma 1.1, Definitions, §2–§5 (with Proposition 5.5), Lemmas 6.1, 6.5, 6.6, 6.8, 6.9, Theorems 7.1, 7.2, Corollaries 7.3, B | Proved here, on paper |
| Lemma 6.2 with (U4c), Lemma 6.3, Lemma 6.4: the literal bound, its closure point by Mahlo ordinals, the restriction of $\sigma$ to $F_\lambda$ | Checked in Agda (`StrictMahlo/Literal`, `Closure`; cubical Agda, not included in this release), from named hypotheses: the literal sizes, the counting cover, the characterization (U4a), and `MahloOrdinals` (the function form, which packages Lemma 6.3) |
| Lemma 6.3, and the function form from stationary inaccessibles | Checked in Agda (`StrictMahlo/Stationary`; cubical Agda, not included in this release), choice-free: the closure points of any $f$ above $\beta$ are the fixed points of a continuous step, so the linear generator's `Club.fixed` makes them a club, with its least and next points by $\omega$-iteration, and they are closed under suprema of inhabited small families. So `MahloOrdinals` follows from `Stationary`: every club closed under such suprema, with strict next points, has an inaccessible member. The closure under small suprema is needed (the ordinals of cofinality $\omega$ are closed under $\omega$-chains and contain no inaccessible), and so are strict next points (`StrictMahlo/Stationary/Discriminator`: with $\preceq$ the hypothesis is refuted) |
| Lemma 6.7, the induction with regularity (the sharper bound; Theorem 7.1 needs only Lemma 6.9) | Checked in Agda (`StrictMahlo/Growth`; cubical Agda, not included in this release), from `Inaccessible`'s regularity and the step bound, which is proved here on paper |
| `Literal`'s fields are jointly satisfiable | Checked (`StrictMahlo/Discriminator`; cubical Agda, not included in this release): the one-point instance of `Literal`. `MahloOrdinals` and `Inaccessible` stay inputs: `point-restricts` assumes Mahlo ordinals, `point-growth` an inaccessible. It says nothing about the simplicial model |
| Lemmas 6.11, 6.12 and Remark 6.13: the second proof of the stop, by the closure point of the chain's own growth, with (U1) alone | Proved here, on paper. Its cardinal steps are checked in Agda for $\zeta$ (`StrictMahlo/Measured`; cubical Agda, not included in this release), from named hypotheses: each simplex's stage, its support enumerated by a small well-order, and a growth function strictly above the support sizes. `MahloOrdinals` at it gives $\lambda$; regularity bounds a request's branches and, at a two-point order, joins them with the head below $\lambda$. The sharper $\lVert A^{\sigma}_\lambda\rVert \le \lambda$ is not checked |
| Theorem 7.2's reading of $\theta_R$: each law of `Strict-Mahlo` is the label equation on its summand, and `inner` pairs the result with its branches | Checked in Agda ([TwoLevel/Mahlo/StepAlgebra](../TwoLevel/Mahlo/StepAlgebra.agda) and its Discriminator): a labelled algebra of the step, with codes naming its carriers, gives `Strict-Mahlo` with every law strict in context, the complete `inner-β` included; an inductive–recursive universe inhabits the hypothesis; and, in LCTT (not yet released), labelled algebras at every stratum's level give `consistent-with-mahlo` |
| K1–K6 | Cited (KL, read) |
| Lemma 1.4 (KL's universe is graded) | Proved here from K1–K6; its clauses (U3), (U4) serve only the first proof |
| Remark 1.5 (ACKS's universes are graded, by rank; W-types from KL Theorem 2.3.4) | Our reading of ACKS §2.5.1, on paper |
| T1 (with ACKS's universe $M_\omega$), T2 | Assumed |
