# Universal induction–recursion in simplicial sets

Status: proof on paper, 2026-11-03. The Agda side is checked, with no extensionality, in [IR/Universal](../IR/Universal/README.md):

- the universal type, with its realized laws by refl at every code;
- the comparison with ordinary arguments;
- Dybjer–Setzer's induction rule.

This note interprets that type in simplicial sets, so that its realized laws hold as equalities of maps (Theorem U). It then argues that Dybjer–Setzer's own rules hold there as equalities too (Corollary V).

The conventions, cited facts and assumptions are those of [StrictMahlo.md](StrictMahlo.md) §1: Lemma 1.1 on sizes, K1–K6 from Kapulkin–Lumsdaine (KL), and T1, T2. Of its Definition 1.3, Theorem U uses only (U1), and Corollary S uses (U2) as well. No grading is used: the cardinal step takes closure points of the chain's own growth (§4). Steps whose proof is the same as in StrictMahlo.md are cited by number. The construction is StrictMahlo.md's, with the space of codes in place of the operator space and the argument functor of a code in place of its step functor $H$.

## 0. Results

Fix:

- a strongly Mahlo cardinal $\kappa$;
- a Kan fibration $\pi : \tilde U \to U$ satisfying (U1) at $\kappa$ (StrictMahlo.md, Definition 1.3): it is $\kappa$-small, and every $\kappa$-small Kan fibration over any base is a pullback of it, up to isomorphism (KL's $U_\kappa$, by K1 and K2);
- a Kan complex $D$, the type of outputs.

Let $C$ be the simplicial set of codes: the initial algebra of the polynomial functor of descriptions with arities in $U$ and outputs in $D$ (§1). For a code $\gamma$, write $\mathrm{Args}_\gamma(X, v)$ for the arguments of $\gamma$ over a family $X$ with labels $v : X \to D$, and $\mathrm{out}$ for their output (§2).

Theorem U uses $U$ only through (U1), and $C$ need not be a Kan complex. (U1) does not make $U$ a Kan complex: a non-Kan component with empty fibers can be adjoined to a universe without breaking (U1).

- **When $U$ and $D$ are Kan complexes**, as KL's $U_\kappa$ is (K3), $C$ is a Kan complex, and T1 reads the inner type `Desc {s = ℓ} D` as $C$.
- **That case carries the rest.** Corollary S, which takes $D := U$, and the univalence of the model's universes are statements about it, for KL's universe or T1's. Univalence is a property of that choice, not a consequence of (U1).

**Theorem U.** There are a map $u : C \to U$ and, writing $R := u^{\ast}\tilde U \to C$ for the pulled-back family:

- a map $\mathrm{value} : R \to D$ (the decoding);
- a map $\mathrm{intro} : \mathrm{Args}_R \to R$ over $C$, where $\mathrm{Args}_R \to C$ is the family of arguments of each code over $R$ with labels $\mathrm{value}$ (§2);

such that the following hold as equalities of maps of simplicial sets.

$$
\mathrm{value} \circ \mathrm{intro} = \mathrm{out} \qquad \text{(decoding)}
$$

For every Kan fibration $q : P \to R$ and every method $m$ (§6), there is a section $s$ of $q$ with

$$
s \circ \mathrm{intro} = m \circ (\mathrm{id}, \mathrm{calls}\, s) \qquad \text{(induction)}
$$

where $\mathrm{calls}\, s$ collects $s$ at the children of an argument. The data are stable under pullback along every map into $C$, and the decoding and induction equations survive pullback.

**Theorem U′ (outputs over a base).** Let $D \to B$ be a Kan fibration, a family of output types. Let $C_B \to B$ be the family of codes of its fibers (§1). The construction of Theorem U runs over $C_B$, with each label in the fiber of $D$ over the same point of $B$. It gives $u : C_B \to U$, $\mathrm{value}$, $\mathrm{intro}$ and induction, with the same equalities of maps, stable under pullback along every map $B' \to B$ (§5).

Applied to the generic family of output types, of which every other is a pullback, Theorem U′ interprets IR/Universal's quantification over the output type $D$.

Read through T1, extended by Theorem U′ for Agda's mutual definition in IR/Universal, the realized laws of that module are equalities of maps: `output-β`, `ind-β` and `root-β`.

**Corollary V (Dybjer–Setzer's rules).** In the model of Theorem U, the comparison and computation witnesses listed in Lemma 7.1 are interpreted by reflexivity (§7). The claim is about those witnesses only. Generic lemmas that accept an arbitrary identification, such as the private `pair-transport` or SPT's `transport-ap`, are not claimed to be reflexivity; only their applications in those witnesses are. So Dybjer–Setzer's decoding equation for ordinary arguments and his induction equation hold as equalities of maps:

$$
\begin{gathered}
\mathrm{value}\ \gamma\ (\mathrm{intro}\ \gamma\ a) = \mathrm{Mark}\ \gamma\ a, \\
\mathrm{ind}\ \gamma\ P\ m\ (\mathrm{intro}\ \gamma\ a) = m\ a\ (\text{std-calls} \ldots (\mathrm{ind}\ \gamma\ P\ m)\ a).
\end{gathered}
$$

**Corollary W (presheaf toposes).** Drop the Kan conditions. Take presheaves on a category in $V_\kappa$, for a strongly Mahlo $\kappa$, with the Hofmann–Streicher universe of the presheaves valued in $V_\kappa$. There the same construction interprets the universal type, with the same strict laws (§8).

**Corollary S (the strict ambient Mahlo rule).** Take $D := U$, and assume (U2) as well. At the codes of `Ambient.description` (Mahlo/DS/Ambient), Theorem U is StrictMahlo.md's Theorem A. Pulling it back along the map from operators to codes gives the carrier, the interpretation, the formers and `inner`, with every law an equality of maps in context (§10).

The Mahlo property is used once, in Lemma 4.2, to make the fibers $\kappa$-small. The global construction (§2–§3) needs only that $\kappa$ is inaccessible: closure is free, and Mahlo is residence.

## 1. Codes

$C \cong P(C)$ is the initial algebra of the polynomial functor of codes in simplicial sets: the colimit of its initial chain $P^\alpha(\emptyset)$. It exists for any $U$ and $D$. When $U$ and $D$ are Kan complexes, the polynomial's parameters are Kan fibrations between Kan complexes, and $C$ is a Kan complex (KL's W-types, as cited in K5). That is the case in which T1 reads the inner type `Desc {s = ℓ} D` as $C$. By Lambek's lemma, an $n$-simplex $\gamma$ of $C$ is exactly one of:

- **($\iota$)** $\iota\, e$, with $e$ an $n$-simplex of $D$;
- **($\sigma$)** $\sigma(A, H)$, with $A$ an $n$-simplex of $U$ and $H : A^{\ast}\tilde U \to C$ a map over the simplices of $\Delta^n$;
- **($\delta$)** $\delta(A, H)$, with $A$ an $n$-simplex of $U$ and $H$ a map from the $D$-valued families over $A^{\ast}\tilde U$ (maps $A^{\ast}\tilde U \to D$) to $C$, again over $\Delta^n$.

**Ranks.** Lambek's lemma gives this decomposition, not an induction across dimensions. For the induction, give each simplex of $C$ its first-appearance rank in the initial chain: the least $\alpha$ with $\gamma$ in $P^{\alpha+1}(\emptyset)$.

- **Restriction does not increase rank.** Each stage of the chain is a simplicial subset.
- **Continuations have strictly smaller rank.** This holds for $H(a)$ at $\sigma$ and $H(v \circ f)$ at $\delta$, after any restriction, because a constructor's parameters lie in the previous stage.

So the arguments of §2, their outputs and their restriction maps are defined together by well-founded induction on rank, across dimensions. The fibrancy proof (Lemma 2.2) inducts on the same rank, and the model's eliminator for codes computes on the three forms strictly.

**Partial paths.** Let $X \to \Delta^n$ carry labels $v : X \to D$. A partial path through $\gamma$ over $X$ is a finite sequence of steps from the root:

- at a $\sigma$-node, a point $a$ of its arity, continuing at $H\, a$;
- at a $\delta$-node, a child map $f$ from its arity into $X$, continuing at $H(v \circ f)$.

Its end is the node where it stops, and the arity there is its end arity. A complete argument (§2) is a partial path that ends at an $\iota$-node. Every partial path is finite, because the order is well founded.

## 2. Arguments, outputs and the step functor

Let $\mathcal S$ be the slice of simplicial sets over $C \times D$. An object $A = (A, p, d)$ has $p : A \to C$ and $d : A \to D$, the label of each element. Only $p$ will be required to be a fibration.

**2.1 Arguments.** Let $\gamma$ be an $n$-simplex of $C$ and $X \to \Delta^n$ a simplicial set over $\Delta^n$ with labels $v : X \to D$. Define the simplicial set $\mathrm{Args}_\gamma(X, v)$ over $\Delta^n$ by recursion on $\gamma$ (§1), as the interpretation of IR/Universal's `Args` (its `Body` under the single constructor `box`):

- $\mathrm{Args}_{\iota\, e}(X, v) := \Delta^n$;
- $\mathrm{Args}_{\sigma(A, H)}(X, v)$: pairs $(a, b)$, with $a$ a simplex of $A^{\ast}\tilde U$ over $\theta : \Delta^m \to \Delta^n$ and $b$ a simplex of $\mathrm{Args}_{H a}(\theta^{\ast}X, v)$;
- $\mathrm{Args}_{\delta(A, H)}(X, v)$: pairs $(f, b)$, with $f : \theta^{\ast}(A^{\ast}\tilde U) \to \theta^{\ast}X$ a map over $\Delta^m$ and $b$ a simplex of $\mathrm{Args}_{H(v \circ f)}(\theta^{\ast}X, v)$.

The output $\mathrm{out}_\gamma : \mathrm{Args}_\gamma(X, v) \to D$ is defined by the same recursion: it is $e$ at $\iota$, and passes to the continuation's argument at $\sigma$ and $\delta$. Both are simplicial, since each clause is.

**2.2 The step functor.** For $A$ in $\mathcal S$, let $H(A)$ have as $n$-simplices the pairs $(\gamma, b)$, where $\gamma \in C_n$ and $b$ is an $n$-simplex of $\mathrm{Args}_\gamma(\gamma^{\ast}A, d)$ over the top simplex of $\Delta^n$. Put $p_H(\gamma, b) := \gamma$ and $d_H(\gamma, b) := \mathrm{out}_\gamma\, b$. On a morphism $h : A \to A'$ of $\mathcal S$, $H(h)$ applies $h$ to the children: at $\delta$ it replaces each child map $f$ by $h \circ f$. Since $d' \circ h = d$, the labels $d' \circ h \circ f = d \circ f$ of the children, and with them the continuations they select, are unchanged.

**Lemma 2.1.**

1. $H$ is an endofunctor of $\mathcal S$.
2. $H$ preserves monomorphisms.
3. $H$ commutes with pullback along maps $g : C' \to C$, as in StrictMahlo.md Lemma 3.3.

*Proof.* Clause by clause on $\gamma$, as in StrictMahlo.md Lemmas 3.2 and 3.3. At $\delta$, a morphism of $\mathcal S$ keeps the labels, so the selected continuation is literally the same. ∎

**Lemma 2.2 (fibrancy).** If $p : A \to C$ is a Kan fibration, so is $p_H : H(A) \to C$.

*Proof.* A map is a Kan fibration if its pullback along every simplex of the base is one. Prove, by induction on the rank of the simplices $\gamma$ of $C$ (§1), that $\mathrm{Args}_\gamma(X, v) \to \Delta^n$ is a Kan fibration for every Kan fibration $X \to \Delta^n$ with labels:

- **$\iota$:** $\mathrm{Args}_{\iota\, e}(X, v)$ is the identity of $\Delta^n$.
- **$\sigma$:** $\mathrm{Args}_{\sigma(A, H)}(X, v)$ is a dependent sum over $A^{\ast}\tilde U \to \Delta^n$, which is a Kan fibration (K1). Over each simplex of $A^{\ast}\tilde U$, the summand is $\mathrm{Args}$ at the smaller code $H(a)$, Kan by induction.
- **$\delta$:** the child maps $f$ form the dependent product, along $A^{\ast}\tilde U \to \Delta^n$, of the pullback of $X \to \Delta^n$. It is a Kan fibration by K4, with KL Lemma 2.3.1 as cited there. Over each simplex $(\theta, f)$ of that space, the continuation is $\mathrm{Args}$ at the smaller code $H(v \circ f)$, Kan by induction.

So in each case the map is a composite of Kan fibrations. Applied over each simplex $\gamma$ of $C$, with $X := \gamma^{\ast}A$, this proves the lemma. ∎

Filtered colimits over $C$ of Kan fibrations over $C$ are Kan fibrations (StrictMahlo.md, Lemma 4.2).

## 3. The global chain

Define $A_0 := \emptyset$, $A_{\alpha+1} := H(A_\alpha)$, and colimits at limits, with transitions as in StrictMahlo.md 5.1. As in Lemma 5.2 there, every transition is a monomorphism and every $p_\alpha : A_\alpha \to C$ is a Kan fibration.

**Lemma 3.1 (comparison).** Let $\delta$ be an uncountable regular cardinal. Suppose that every arity $A$ at every node of every code reached by a simplex of $H(A_\delta)$ has $\lVert A^{\ast}\tilde U\rVert < \delta$. Then $\iota_{\delta,\delta+1} : A_\delta \to H(A_\delta)$ is an isomorphism, and so is every later transition.

*Proof.* As in StrictMahlo.md, Lemma 5.3.

- An element $(\gamma, b)$ of $H(A_\delta)$ is a complete path through $\gamma$ (§1).
- Its data from $A_\delta$ are the child maps at the finitely many $\delta$-nodes of that path.
- Each child map has a domain of fewer than $\delta$ simplices, so it lands in one stage, $\delta$ being regular.
- Finitely many stages have a common bound.

So $(\gamma, b)$ lies in $H(A_\alpha)$ for some $\alpha < \delta$. ∎

**Proposition 3.2.** Put $A := A_\kappa$ and $\theta := \iota_{\kappa,\kappa+1}^{-1}$. Then $(A, \theta)$ is an $H$-algebra in $\mathcal S$, $p : A \to C$ is a Kan fibration, and $(A, \theta)$ is an initial $H$-algebra.

*Proof.* Every arity of every code is a simplex of $U$, so it is $\kappa$-small (U1, Lemma 1.1). So Lemma 3.1 applies at $\kappa$. Then $H$ preserves the colimit of the initial chain at $\kappa$, and the colimit of such a chain is the initial algebra (Adámek). Fibrancy is Lemma 2.2 with the colimit lemma. ∎

So the universal type exists over the whole code space at once, with every label literal, using only that $\kappa$ is inaccessible. It remains to show that its fibers are small.

## 4. Local bounds

Fix an $n$-simplex $\sigma : \Delta^n \to C$, a code over $\Delta^n$. Pullback along $\sigma$ turns the chain into the chain $A^\sigma_\alpha$ of the local step functor (Lemma 2.1, as in StrictMahlo.md, Lemma 6.1). Its elements are the pairs $(\theta, b)$ of a simplex $\theta : \Delta^m \to \Delta^n$ and a complete argument $b$ of the code $\sigma\theta$.

**Lemma 4.1 (small stages).** For every $\alpha < \kappa$, $A^\sigma_\alpha$ has fewer than $\kappa$ simplices, and fewer than $\kappa$ partial paths run over it.

*Proof.* By induction on $\alpha$. Let $X$ be a stage with fewer than $\kappa$ simplices. Count the partial paths over $X$ by their length.

- **The choices at a node.** Its arity $A$ is a simplex of $U$, so $A^{\ast}\tilde U$ has fewer than $\kappa$ simplices (U1, Lemma 1.1). At a $\sigma$-node a choice is one of these points. At a $\delta$-node it is a map from them into $X$, and there are fewer than $\kappa$ of those, $\kappa$ being a strong limit.
- **Each length.** By induction on the length, fewer than $\kappa$ partial paths have length $k$, $\kappa$ being regular.
- **All lengths.** There are countably many lengths, and countably many simplices $\theta$ of $\Delta^n$.

So fewer than $\kappa$ partial paths run over $X$. The complete arguments are among them, so $H(X)$ has fewer than $\kappa$ simplices. At a limit $\alpha < \kappa$, the stage is a union of fewer than $\kappa$ stages, each with fewer than $\kappa$ simplices, and $\kappa$ is regular. ∎

**The growth function.** For $\alpha < \kappa$, let $\zeta(\alpha)$ be the supremum of $\lVert A^\sigma_\alpha\rVert$ and of the sizes $\lVert A^{\ast}\tilde U\rVert$ of the end arities $A$ of the partial paths over $A^\sigma_\alpha$. A family of fewer than $\kappa$ cardinals need not attain its supremum, hence a supremum and not a maximum. By Lemma 4.1, $\kappa$ being regular, $\zeta(\alpha) < \kappa$.

**Lemma 4.2 (closure point; Mahlo).** There is an inaccessible $\lambda < \kappa$ with $\zeta(\alpha) < \lambda$ for every $\alpha < \lambda$.

*Proof.* The limit cardinals $\lambda < \kappa$ with $\zeta(\alpha) < \lambda$ for every $\alpha < \lambda$ form a club in $\kappa$. They are closed by definition, and unbounded since $\zeta$ maps $\kappa$ to $\kappa$, with $\kappa$ regular. The inaccessibles below $\kappa$ are stationary, $\kappa$ being strongly Mahlo, so one lies in this club. In the function form, `Hartogs.Cardinal`'s `MahloOrdinals` at $\zeta$ gives it directly, as `StrictMahlo/Closure` uses it (both cubical Agda, not included in this release). ∎

**Lemma 4.3 (stabilization).** $\iota^\sigma_{\lambda,\lambda+1}$ is an isomorphism, and $A^\sigma_\kappa \cong A^\sigma_\lambda$, which has at most $\lambda$ simplices.

*Proof.* Let $(\theta, b)$ be an element of $H^\sigma(A^\sigma_\lambda)$, with child maps $f_1, \ldots, f_k$ into $A^\sigma_\lambda$ at the $\delta$-nodes of $b$, in order. Find, by induction on $i$, stages $\beta_i < \lambda$ such that $f_1, \ldots, f_i$ land in $A^\sigma_{\beta_i}$, with $\beta_0 := 0$.

- **The arity.** The arity at the $i$-th $\delta$-node is the end arity of a partial path over $A^\sigma_{\beta_{i-1}}$. So its pullback has at most $\zeta(\beta_{i-1}) < \lambda$ simplices.
- **The child map.** So $f_i$ has a domain of fewer than $\lambda$ simplices. Each of them lands in a stage below $\lambda$, and $\lambda$ is regular, so $f_i$ lands in one stage $\gamma_i < \lambda$ (as `StrictMahlo/Growth` uses `Inaccessible.regular`).
- **The next stage.** Put $\beta_i := \max(\beta_{i-1}, \gamma_i)$.

So $b$ is an argument over $A^\sigma_{\beta_k}$, and $(\theta, b)$ lies in $A^\sigma_{\beta_k + 1}$, with $\beta_k + 1 < \lambda$. The comparison map is therefore onto. It is a monomorphism (Lemma 2.1), so it is an isomorphism, and so is every later transition (StrictMahlo.md, Lemma 5.3). Finally $A^\sigma_\lambda$ is the union of the stages below $\lambda$, so it has at most $\sum_{\alpha<\lambda} \zeta(\alpha) \le \lambda$ simplices. ∎

Nothing here uses a grading of $U$ or a size of $D$. The output type enters only through the labels, which select continuations, and Lemma 4.1 counts choices, not continuations.

## 5. Smallness and residence

**Theorem 5.1.** $p : A \to C$ is a $\kappa$-small Kan fibration.

*Proof.* As in StrictMahlo.md, Theorem 7.1. Over each simplex $\sigma$ of $C$, $\sigma^{\ast}A \cong A^\sigma_\kappa \cong A^\sigma_\lambda$ has at most $\lambda < \kappa$ simplices (Lemmas 2.1 and 4.3), and Lemma 1.1 applies. ∎

By (U1) there are $u : C \to U$ and an isomorphism $\varphi : R \to A$ over $C$, where $R := u^{\ast}\tilde U$. Put $\mathrm{value} := d \circ \varphi$, and transfer $\theta$ along $\varphi$. This gives $\mathrm{intro} : H(R) \to R$ with $\mathrm{value} \circ \mathrm{intro} = d_H = \mathrm{out}$ on every simplex. That is the decoding equation of Theorem U, and no transport occurs: the label of an introduced element is literally the output of its argument.

The argument family $\mathrm{Args}_R$ of Theorem U is $H(R) \to C$.

**Theorem 5.2 (Theorem U′, outputs over a base).** Let $D \to B$ be a Kan fibration. Let $C_B \to B$ be the initial algebra of the polynomial functor of codes in the slice over $B$, fiberwise the codes with outputs in $D_b$. The data of Theorem U exist over $C_B$, with the same equalities of maps, and they are stable under pullback along every map $B' \to B$.

*Proof.* Replace $C$ by $C_B$, and $\mathcal S$ by the slice over $C_B \times_B D$: a label lies in the fiber of $D$ over the image in $B$ of its code. The proofs go through unchanged, for these reasons:

- **The step functor (Lemmas 2.1, 2.2).** It is defined clause by clause on codes. The labels select continuations within one fiber of $D$, and fibrancy uses only the arities, which are simplices of $U$.
- **The chain and local bounds (§3, §4).** These count choices at nodes, points of arities and child maps into stages, never labels. So $D$ may be large, and the fibers over $B$ never enter the counts.
- **Classification and induction (§5, §6).** (U1) classifies over any base, and initiality holds in every slice.
- **Pullback along $B' \to B$.** It pulls back $C_B$, the slice and the chain, by Lemma 2.1(3), so the construction for the pulled-back family is the pullback of this one.

For the generic family of output types every other family is a pullback, which gives the uniformity in $D$ of IR/Universal. ∎

## 6. Induction

A method over a Kan fibration $q : P \to R$ is a map

$$
m : \Sigma_{(\gamma, b) \in H(R)}\, \mathrm{Hyp}(b) \to P, \qquad q \circ m = \mathrm{intro} \circ \mathrm{pr}_1.
$$

Here $\mathrm{Hyp}(b)$ is the family of points of $P$ over the children of $b$. At a $\delta$-node it is the dependent product of $q$'s fibers over the child map, as in IR/Universal's `Hyp`.

**Lemma 6.1.** $H(P)$, with the projection and labels of $R$, is isomorphic over $H(R)$ to $\Sigma_{b \in H(R)}\, \mathrm{Hyp}(b)$.

*Proof.* At a $\delta$-node, a child map into $P$ is a child map into $R$ together with a point of $P$ over each child. These are the same simplices, so the isomorphism holds on simplices, clause by clause. ∎

So $m$ is an $H$-algebra structure on $P$, with $q$ a morphism of $H$-algebras. By initiality (Proposition 3.2, transferred along $\varphi$) there is a unique algebra map $s : R \to P$. Then $q \circ s$ is an algebra map $R \to R$, hence the identity, so $s$ is a section of $q$. That $s$ is an algebra map is the computation law of Theorem U, which is IR/Universal's `ind-β`. For the motive with constant fiber $\mathrm{Args}$, it is `root-β`.

Stability: pullback along $g : \Gamma \to C$ turns the chain into the chain of the pulled-back functor (Lemma 2.1), so it keeps the initial algebra. An eliminator over $\Gamma$ is the unique algebra map there, so pullbacks of eliminators coincide by uniqueness.

## 7. Corollary V: Dybjer–Setzer's rules

**Lemma 7.1.** Let $t$ be one of the following identifications:

- from IR/Universal: `from-to`, `to-from`, `output-to`, `hyp-to`, `calls-to`;
- from IR/Universal/Induction: `method-β`, `ind-β`, `recover-β`, `root-β`.

In the model of Theorem U, $t$ is interpreted by reflexivity at every simplex.

*Proof.*

- **What $t$ is built from.** Each such $t$ is a closed term of book type theory without postulates, extensionality or univalence. It is built from refl by recursion on codes and on arguments, `ap`, `_∙_`, `_⁻¹`, `transport` and `apd`. The half-adjoint coherence is built from these as well.
- **Identity premises.** Every identification to which $t$ applies J is itself such a term. No identification enters as a free variable.
- **What the model provides.** The inductive types involved are codes, arguments, $\Sigma$, `Lift` and `𝟙`. Each is a strict initial algebra, so at a simplex its elements are constructor applications, and its eliminator computes on them strictly. Identity types are KL's, with J computing strictly on refl.
- **The induction.** Induct on the code tree at the simplex (§1), then on the argument's constructors. Each such term evaluates to reflexivity.

A section of a path object that is reflexivity at every simplex has equal endpoints. ∎

So in this model, Dybjer–Setzer's introduction `intro γ a := intro (to a)` decodes strictly to `Mark γ a`, by Theorem U and `output-to`. Its induction equation holds strictly, by `Induction.ind-β`. Together with Theorems U and U′, this interprets Dybjer–Setzer induction–recursion with outputs in $D$, type-valued when $D = U$, every rule as an equality of maps. For KL's universe, or T1's, the model's fibrant universes are univalent (KL Theorem 3.4.1). It is conditional on T1 for the remaining type formers.

## 8. Corollary W: presheaf toposes

Take presheaves on a category $\mathcal C$ that lies in $V_\kappa$, for a strongly Mahlo $\kappa$. Use the Hofmann–Streicher universe of the presheaves valued in $V_\kappa$, which classifies $\kappa$-small families strictly. This is the size convention of Hofmann and Streicher, *Lifting Grothendieck universes*. Drop Lemma 2.2 and every Kan condition.

- **The size convention matters.** $\mathcal C \in V_\kappa$ replaces the countably many simplices $\theta$ of Lemmas 3.1 and 4.1 by the fewer than $\kappa$ arrows of $\mathcal C$, and the closure point of Lemma 4.2 is chosen above the number of those arrows.
- **Pointwise smallness is not enough.** With $\kappa$ parallel arrows, an exponential of pointwise small families can have $2^\kappa$ sections.
- §1, §3 and §4 use only the slice, colimits, pullbacks and the sizes of presheaves.
- §5 uses the universe's strict classification of $\kappa$-small families.
- §6 uses initiality.

So the universal type, and with Lemma 7.1 Dybjer–Setzer's rules, are interpreted there with strict laws. Kubánek (MSc thesis, Chalmers 2025) states that "there is currently no presheaf model for induction-recursion", and that normalization of Mahlo universes by gluing would need one. This construction is a candidate.

## 9. Discriminators

1. **Child maps are kept.** In [IR/Universal/Discriminator](../IR/Universal/Discriminator.agda) two child maps decode alike as whole functions, yet give distinct parents. In the model the simplices of $R$ are argument trees with their literal child maps: no quotient and no fibrant replacement identifies them.
2. **No fibrancy of the decoding.** $\mathrm{value} : R \to D$ is not asked to be a fibration (StrictMahlo.md, §9.3).
3. **No unique names.** $\mathrm{value}$ is not an embedding. This universal type gives Dybjer–Setzer's rules, not Shulman's univalent universe of codes; that is Mahlo/DS/Univalent's, from unique names.
4. **Mahlo only for smallness.** Without Lemma 4.2, Proposition 3.2 still gives the universal type over $C$, but its fibers need not be $\kappa$-small: the type exists one universe up, raised.
5. **Outputs in any type.** $D$ may be any Kan complex, a large one included. The counts of Lemma 4.1 and the bound $\zeta$ involve only arities, which are simplices of $U$, and child maps into stages. The output type enters only through the labels. Internally, Mahlo/DS reaches outputs in any type through a two-sorted family (`Naming.outputs`), under extensionality.

## 10. Corollary S: the strict ambient Mahlo rule

Take $D := U$, and assume (U2): the parent's formers. Let $O$ be the simplicial set of operators (StrictMahlo.md, §2.2). Let $d : O \to C$ interpret `Ambient.description` of Mahlo/DS/Ambient (T1). This is the code `σ Tag (branch Ψ)`, with a branch for each former of the ambient family and two for $\Psi$: its index and its member.

**Corollary S.** Pulling Theorem U back along $d$ gives StrictMahlo.md's Theorem A, with carrier $r := u \circ d$ and interpretation $i := \mathrm{value}$ over $d$.

*Proof.* Pull $\mathrm{value}$ and $\mathrm{intro}$ back along $d$, to $R_d := d^{\ast}R$ over $O$. Each field of Theorem A is $\mathrm{intro}$ at one branch. Each law is the decoding equation of Theorem U at that branch, read through $\mathrm{out}$.

- $e_0$, $e_1$, $e_2$ and $e_{\mathbb N}$ are $\mathrm{intro}$ at the four nullary branches. Their outputs are $0_U$, $1_U$, $2_U$ and $\mathbb N_U$.
- For a family $(a, b)$ of $R_d$ over $\Psi$, $\mathsf{product}(a, b)$ is $\mathrm{intro}$ at the product branch, with first child $a$ and second child map $b$. The branch's second arity is the decoding of its first child, which is $\mathrm{value}\, a$, literally, so $b$ has the right type. Its output is $\Pi_U(\mathrm{value}\, a, \mathrm{value} \circ b) = \Pi_U(J(a, b))$. Sum and tree likewise.
- $\mathsf{identity}(a, y, y')$ is $\mathrm{intro}$ at the identity branch, with output $\mathrm{Id}_U(y, y')$.
- For a family $(a, b)$, the index code is $\mathrm{intro}$ at the index branch, with output $c := \mathrm{pr}_1(\Psi(J(a, b)))$. The member branch's $\sigma$-arity is that same type $c$, written by the description itself. So a point $y$ over the index code's decoding is literally a point of the arity. The member code at $y$ is $\mathrm{intro}$ at the member branch, with output $\mathrm{pr}_2(\Psi(J(a, b)))\, y$. Put $\mathsf{inner}(a, b) := (\text{the index code}, y \mapsto \text{the member code at } y)$. Then $J(\mathsf{inner}(a, b)) = \Psi(J(a, b))$, with no transport.

All of these are maps over $O$, so the laws hold in context, as Theorem A requires. ∎

The two step functors are canonically isomorphic, with labels matching exactly. Their presentations are not literally equal: the argument functor keeps singleton-indexed child maps, trailing units and the boxes of the arguments. Evaluating and removing that packaging keeps every label. Summand by summand, StrictMahlo.md's $H$ corresponds to:

- its $O$ summands, to the nullary branches;
- its four $F_A$ summands, to the product, sum, tree and index branches;
- $I_A$, to the identity branch;
- $B_A$, to the member branch.

So StrictMahlo.md's chain (§5 there) is isomorphic to this note's chain (§3) pulled back along $d$, compatibly with labels. That suffices for the strict field equations above.

Internally, Mahlo/DS/Ambient's `closure` builds a closure from a small algebra of the same description. There the member's point is read along the index law (`cast`), and in this model that cast is the identity. Ambient's `inner-β` uses a supplied extensionality, and is not among the witnesses of Lemma 7.1. The strict equation for `inner` is the one constructed above, directly.

## 11. Checked, cited, proved here

| Item | Status |
| --- | --- |
| The universal type, its realized laws by refl, the comparisons, Dybjer–Setzer induction, the discriminators | Checked in Agda ([IR/Universal](../IR/Universal/README.md)) |
| §1–§6: the step functor, fibrancy, the chain and its initial algebra, local bounds, smallness, induction | Proved here, on paper, citing StrictMahlo.md's lemmas where the steps coincide |
| Lemmas 4.1–4.3: small stages, the growth function's closure point, stabilization | On paper. The cardinal steps are those checked against named hypotheses in `StrictMahlo/` (cubical Agda, not included in this release): the closure point from `MahloOrdinals` (`Closure`) and regularity (`Growth`). The counting of Lemma 4.1 is on paper |
| Lemma 7.1 and Corollary V | On paper; an argument about the specific proof terms |
| Theorem U′ (Theorem 5.2): outputs over a base, uniform in $D$ | On paper; the same slice and counting arguments over $C_B$ |
| Corollary W, with the category in $V_\kappa$ | On paper |
| Corollary S: Theorem U contains StrictMahlo.md's Theorem A | On paper (§10); the step functors agree summand by summand |
| K1–K6, KL Theorem 3.4.1 | Cited (KL, read) |
| T1, T2 | Assumed, as in StrictMahlo.md |
