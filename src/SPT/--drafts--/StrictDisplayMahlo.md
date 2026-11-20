# The strict Mahlo rule for the universe of displays in simplicial sets

Status: proof on paper, 2026-11-03. It extends [StrictMahlo.md](StrictMahlo.md), whose conventions, cited facts (K1–K6), assumptions (T1, T2) and numbered results are used throughout, always cited with its name; unqualified numbers refer to this note. It proves only what is new. No step of it is checked in Agda; its cardinal steps are those of `StrictMahlo/Closure` and `StrictMahlo/Growth` (cubical Agda, not included in this release), applied to a second chain and not rechecked for it. It was independently audited, which confirmed the direct construction; its corrections are applied: the fiber points in Lemma 2.3, the hypotheses (U2₁) of Theorem D, and the dependence of Lemma 1.1 on the constructed carrier.

Purpose. LCTT's display model takes as hypothesis `StrictDisplayMahlo`: the ambient Mahlo rule for the universe of displays, every decoding law a strict equality in context. Its operators are display maps, an ambient operator (the base part) with a fiber part over it, so its child has base codes, depending on the base part alone, and fiber codes over them. Its base half is `Strict-Mahlo` (`ambient` there), the hypothesis of StrictMahlo.md's Theorem A. This note gives the fiber half by the same construction, run a second time over Theorem A's carrier.

The construction, as in StrictMahlo.md, reads Mahlo as resident operator dynamics: a fiber code's family is the parent's fiber family pulled back, never a rebuilt one, and residence names its base by a parent code.

## 0. Results

Fix a strongly Mahlo cardinal $\kappa$ and a Kan fibration $\pi : \tilde U \to U$ with (U1) and (U2) of StrictMahlo.md's Definition 1.3; no grading is used (StrictMahlo.md, Remark 6.13). Take from StrictMahlo.md: the families $F$, the operators $O := F^F$ with evaluation $\mathrm{ev}$ (StrictMahlo.md §2), and Theorem A's data, the base codes $p_R : R = r^{\ast}\tilde U \to O$ with interpretation $i : R \to U$, their families $F_R$, identity data $I_R$, branch data $B_R$, readout $J_R$, decoded points $E_R$ (StrictMahlo.md §3.1, for $A := R$, $d := i$), and the operations $e_0, e_1, e_2, e_{\mathbb N}$, $\mathsf{product}$, $\mathsf{sum}$, $\mathsf{tree}$, $\mathsf{identity}$, $\mathsf{result}$, $\mathsf{branch}$, $\mathsf{inner}$ (proof of StrictMahlo.md's Theorem 7.2). The new ingredients are defined in §1:

- the fiber data $\mathrm{Fib} \to F$ over a family, and the fiber operators $O_1 \to O$, each an operator $\sigma$ with a fiber part $\varphi$ over it, with evaluation $\mathrm{ev}_1$;
- the fiber formers (U2₁): for a family with fiber data, a family over the decoded points of its Σ, Π and W codes; for two points with fiber points over them, a family over the decoded points of their identity code; and the unit code $1_U$ for the constants;
- the base of the fiber codes, $R_1 := R \times_O O_1$: a base code together with a fiber part over its operator.

**Theorem D.** Given, besides (U1) and (U2), the fiber formers (U2₁) of §1.3, there are a map $r_1 : R_1 \to U$ and, writing $Q := r_1^{\ast}\tilde U \to R_1$ for the fiber codes and $F^Q$, $I^Q$, $B^Q$, $K_Q$ for their fiber data and fiber readout (§2):

- a map $k : Q \times_R E_R \to U$ (the reading: over a fiber code above a base code $x$, a family over the decoded points of $x$);
- maps $\varepsilon_0, \varepsilon_1, \varepsilon_2, \varepsilon_{\mathbb N} : O_1 \to Q$ over $(e_c \circ \mathrm{pr}, \mathrm{id}) : O_1 \to R_1$ (fiber codes over the constant base codes);
- maps $\mathsf{product}_1, \mathsf{sum}_1, \mathsf{tree}_1 : F^Q \to Q$, $\mathsf{identity}_1 : I^Q \to Q$ and $\mathsf{inner}_1 : F^Q \to F^Q$, each over the corresponding base operation;

such that the following are equalities of maps of simplicial sets, for $f = ((a, b), \tau, s, t)$ in $F^Q$, $g = ((a, y, y'), \tau, s, w, w')$ in $I^Q$, and $z$ a decoded point of the base code in question:

$$
\begin{gathered}
k(\varepsilon_c(\tau), z) = 1_U \quad (c = 0, 1, 2, \mathbb N), \\
k(\mathsf{sum}_1(f), z) = \Sigma_1(J_R(a, b), K_Q(f), z), \quad \text{likewise } \Pi_1, W_1, \\
k(\mathsf{identity}_1(g), z) = \mathrm{Id}_1((i(a), y, y'), k(s, \cdot), w, w', z), \\
K_Q(\mathsf{inner}_1(f)) = \mathrm{ev}_1(\tau, J_R(a, b), K_Q(f)).
\end{gathered}
$$

With Theorem A's laws for the base operations, these are the laws of `StrictDisplayMahlo`: each of its laws is a pair, Theorem A's law with the matching law above over it.

**Corollary D′.** In a model of two-level type theory in simplicial sets as in T1, whose fibrant universe at level $\ell$ satisfies (U1) and (U2) at a strongly Mahlo $\kappa$ and is a Kan complex, with (U2₁) the glued fiber maps as which T1 reads `sumFibers`, `productFibers`, `treeFibers` and `identityFibers` (§1.3), the outer type `StrictDisplayMahlo ℓ` has a global element, and `ambient` sends it to the global element of `Strict-Mahlo (Ambient.formers ℓ)` of StrictMahlo.md's Corollary B.

**Corollary E** (conditional on T2). Under the cardinal assumptions of StrictMahlo.md's Corollary C (a strongly Mahlo cardinal for the level of every stratum, and an inaccessible above them all), the syntax of LCTT with every rule has no closed term of empty in the display model (`consistent-with-Mahlo`), relative to ZFC with those cardinals.

The Mahlo property is used once more, in Lemma 3.4, to stop the fiber chain of each fiber operator simplex below $\kappa$. As before, the closure is free (§3, using only that $\kappa$ is inaccessible) and Mahlo is residence. What is new beyond StrictMahlo.md is one fact about the base: Theorem A's carrier is the disjoint union of its constructor tags (Lemma 1.1), which is what makes the fiber chain a Kan fibration over the base codes.

## 1. Fiber data, fiber operators and the base of the fiber codes

**1.1 Fiber data.** For an $m$-simplex $G = (c, \beta)$ of $F$, a fiber datum over $G$ is a pair $(P, P')$ of maps
$$
P : c^{\ast}\tilde U \to U, \qquad P' : P^{\ast}\tilde U \times_{c^{\ast}\tilde U} \beta^{\ast}\tilde U \to U,
$$
a family over the index and, over an index point $z$, a point $w$ of $P(z)$ and a point $v$ of the member $\beta(z)$, a family $P'(z, w, v)$. The simplicial set $\mathrm{Fib}$ has as $m$-simplices the triples $(G, P, P')$; $\theta$ acts by precomposition with $\hat\theta$ and its pullbacks; $\mathrm{pr} : \mathrm{Fib} \to F$ forgets $(P, P')$. This is `Σ F (Fibers F)`, with `Fibers` of LCTT's display model.

**1.2 Fiber operators.** An $n$-simplex of $O_1$ is a pair $\tau = (\sigma, \varphi)$ with $\sigma$ an $n$-simplex of $O$, that is $\sigma : \Delta^n \times F \to F$, and $\varphi : \Delta^n \times \mathrm{Fib} \to \mathrm{Fib}$ with $\mathrm{pr} \circ \varphi = \sigma \circ (\Delta^n \times \mathrm{pr})$: a fiber part over $\sigma$. Evaluation $\mathrm{ev}_1$ sends an $n$-simplex $(\tau, G, P, P')$ to $\varphi_n(\iota_n, (G, P, P'))$, fiber data over $\mathrm{ev}(\sigma, G)$. This is `Σ (Ambient.Operator ℓ) FiberOperator`; $\mathrm{pr} : O_1 \to O$ forgets $\varphi$.

**1.3 The fiber formers (U2₁).** Maps of simplicial sets
$$
\Sigma_1 : \mathrm{Fib} \times_F \Sigma_U^{\ast}\tilde U \to U, \qquad \Pi_1 : \mathrm{Fib} \times_F \Pi_U^{\ast}\tilde U \to U, \qquad W_1 : \mathrm{Fib} \times_F W_U^{\ast}\tilde U \to U,
$$
giving, for a family with fiber data, a family over the decoded points of its Σ, Π or W code, and $\mathrm{Id}_1$, giving, for two points $y, y'$ over a code $c$, a family $P$ over $c^{\ast}\tilde U$ and points $w, w'$ of $P$ over $y, y'$, a family over the decoded points of $\mathrm{Id}_U(y, y')$. The construction below uses only that they are maps of simplicial sets. Under T1 they are the interpretations of `sumFibers`, `productFibers`, `treeFibers` and `identityFibers` of LCTT's display model, read through the pairing, abstraction, `sup` and reflexivity structures of (U2).

**1.4 The base of the fiber codes.** $R_1 := R \times_O O_1$, with $q_0 : R_1 \to R$ and $q_1 : R_1 \to O_1$: a base code $x$ with a fiber operator $\tau$ over its operator $p_R(x)$.

**Lemma 1.1 (the tags of the base).** $R$ is the disjoint union of ten sub-simplicial sets, one for each tag of StrictMahlo.md's step functor $H$, each a union of connected components of $R$: the images of $e_0, e_1, e_2, e_{\mathbb N}$ (each isomorphic to $O$), of $\mathsf{product}$, $\mathsf{sum}$, $\mathsf{tree}$, $\mathsf{result}$ (each isomorphic to $F_R$), of $\mathsf{identity}$ ($\cong I_R$) and of $\mathsf{branch}$ ($\cong B_R$). The same holds for $R_1$, each part fibered over $O_1$.

*Proof.* $\theta_R : H(R) \to R$ is an isomorphism (proof of StrictMahlo.md's Theorem 7.2: $\theta$ is the inverse of $\iota_{\kappa,\kappa+1}$, its Proposition 5.4), and $H(R)$ is a coproduct of the ten summands (StrictMahlo.md §3.1), each a union of components since a coproduct of simplicial sets is a disjoint union. The operations are $\theta_R$ composed with the summand inclusions. Pullback along $p_R$ preserves coproducts, which gives $R_1$. ∎

Lemma 1.1 is a fact about the carrier constructed in StrictMahlo.md's Theorem 7.2, with its isomorphism $\theta_R : H(R) \cong R$. Theorem A's statement alone, or an arbitrary inhabitant of `Strict-Mahlo`, does not supply this decomposition; a formal record of the construction must retain $\theta_R$.

## 2. The fiber step functor

Let $\mathcal T$ be the category of simplicial sets $Y$ with $q : Y \to R_1$ and a reading $k : Y \times_R E_R \to U$, where $Y \times_R E_R$ pairs a simplex $s$ of $Y$ over $(x, \tau)$ with a decoded point $z$ of $x$; morphisms commute with $q$ and $k$. Only $q$ will be required to be a fibration. For $s$ in $Y$ write $k(s, \cdot)$ for its family over the decoded points of its base code.

**2.1 Definition.** For $Y$ in $\mathcal T$, writing $P(y)$, for a family $P$ over the decoded points of a code and an $n$-simplex $y$ of $\tilde U$ over that code, for $P$ at the decoded point $(\iota_n, y)$, as StrictMahlo.md writes $\beta_{a,b}(\iota_n, y)$:

- **Fiber points.** $E^Y := \lbrace (s, z, w) \mid z \in E_R \text{ over } q_0 q(s),\ w \in \tilde U,\ \pi(w) = k(s, z) \rbrace$, the points of the families.
- **Fiber data over a family.** $(F^Y)_n$ is the set of quadruples $((a, b), \tau, s, t)$ with $(a, b) \in (F_R)_n$, $\tau \in (O_1)_n$ over $p_R(a)$, $s \in Y_n$ over $(a, \tau)$, and $t$ a map from the fiber points of $s$, $\lbrace (z, w) \rbrace$, to $Y$ with $q(t(z, w)) = (b(z), \tau \circ \mathrm{pr})$: over each index point and each point of its family, a fiber code over the branch. This is `CodeFibers`.
- **Fiber readout.** $K_Y((a, b), \tau, s, t) := (k(s, \cdot), (z, w, v) \mapsto k(t(z, w), v))$, fiber data over $J_R(a, b)$. This is `mapFibers`.
- **Fiber data over two points.** $(I^Y)_n$: tuples $((a, y, y'), \tau, s, w, w')$ with $(a, y, y') \in (I_R)_n$, $\tau$ over $p_R(a)$, $s$ over $(a, \tau)$, and $w, w' \in \tilde U_n$ with $\pi(w) = k(s, y)$, $\pi(w') = k(s, y')$.
- **Fiber data at a branch.** $(B^Y)_n$: triples $(f, y, w)$ with $f = ((a, b), \tau, s, t) \in (F^Y)_n$, $y \in \tilde U_n$ with $\pi(y) = c_{a,b}$ (so that $((a, b), y) \in (B_R)_n$), and $w \in \tilde U_n$ with $\pi(w) = P(y)$, where $(P, P') := \mathrm{ev}_1(\tau, J_R(a, b), K_Y(f))$: a branch point with a point of the operator's fiber value over it.
- **The step.** $H_1(Y)$ is the coproduct of four copies of $O_1$ (tags $\mathbf 0, \mathbf 1, \mathbf 2, \mathbb N$), four copies of $F^Y$ (tags $\Pi, \Sigma, W, \mathsf{res}$), $I^Y$ (tag $\mathsf{Id}$) and $B^Y$ (tag $\mathsf{br}$), over $R_1$ by: $\tau \mapsto (e_c(\mathrm{pr}\,\tau), \tau)$ on the constants; $f \mapsto (\mathsf{product}(a, b), \tau)$, $(\mathsf{sum}(a, b), \tau)$, $(\mathsf{tree}(a, b), \tau)$, $(\mathsf{result}(a, b), \tau)$; $g \mapsto (\mathsf{identity}(a, y, y'), \tau)$; $(f, y, w) \mapsto (\mathsf{branch}((a, b), y), \tau)$.
- **The reading of the step**, at a decoded point $z$ of the base code:

$$
\begin{aligned}
k_H((\mathbf c, \tau), z) &:= 1_U, \\
k_H((\Sigma, f), z) &:= \Sigma_1(J_R(a, b), K_Y(f), z), \quad \text{likewise } \Pi, W, \\
k_H((\mathsf{Id}, g), z) &:= \mathrm{Id}_1((i(a), y, y'), k(s, \cdot), w, w', z), \\
k_H((\mathsf{res}, f), z) &:= P(z), \\
k_H((\mathsf{br}, (f, y, w)), v) &:= P'(y, w, v),
\end{aligned}
$$

with $(P, P') := \mathrm{ev}_1(\tau, J_R(a, b), K_Y(f))$. Each is well typed because of Theorem A's laws, which are literal: the decoded points of $\mathsf{sum}(a, b)$ are those of $\Sigma_U(J_R(a, b))$, those of $\mathsf{result}(a, b)$ are those of $c_{a,b}$, the index of $\mathrm{ev}(\sigma, J_R(a, b))$, and those of $\mathsf{branch}((a, b), y)$ are those of $\beta_{a,b}(\iota, y)$, the member at $y$ over which $P'(y, w, \cdot)$ lives.
- **On morphisms**, as for $H$: identity on the constants, $t \mapsto f \circ t$ and $s \mapsto f(s)$ elsewhere.

**Lemma 2.2.** $H_1$ is an endofunctor of $\mathcal T$ and preserves monomorphisms; it commutes with base change along every $g : O_1' \to O_1$, compatibly with readings.

*Proof.* As StrictMahlo.md's Lemmas 3.2 and 3.3, summand by summand: $K_Y$ and $\mathrm{ev}_1$ are simplicial; a morphism of $\mathcal T$ preserves $q$ and $k$, hence fiber points, $K_Y$ and every reading; pullback preserves coproducts and pullbacks. ∎

**Lemma 2.3 (fibrancy).** If $q : Y \to R_1$ is a Kan fibration, so is $q_H : H_1(Y) \to R_1$.

*Proof.* By Lemma 1.1 it suffices to show that each summand is a Kan fibration over its tag part of $R_1$, through the isomorphism of that part with $O_1$, $F_R \times_O O_1$, $I_R \times_O O_1$ or $B_R \times_O O_1$; the inclusion of a union of components is a Kan fibration (a horn is connected), and a coproduct over $R_1$ of Kan fibrations is one. Constants: the identity of $O_1$. $F^Y$: the fiber points $E^Y \to Y$ are the composite $E^Y \to Y \times_R E_R \to Y$ of two Kan fibrations, the first the pullback of $\pi$ along the reading $k$, the second the pullback of $E_R \to R$, itself a pullback of $\pi$ (U1); so the maps $t$ over $(a, b, \tau, s)$ form the dependent product, along the Kan fibration of fiber points of $s$, of the Kan fibration $Y \to R_1$ pulled back along $(z, w) \mapsto (b(z), \tau)$; it is a Kan fibration by K4, and so is its composite with the choice of $s$, a pullback of $q$. $I^Y$: two pulled-back families of points of $\pi$, over the pullback of $q$ that chooses $s$. $B^Y$: the pullback of the fibration $F^Y \to R_1$, followed by the family of points of the evaluated $P(y)$, a pullback of $\pi$. ∎

Filtered colimits over $R_1$ of Kan fibrations are Kan fibrations, as in StrictMahlo.md's Lemma 4.2.

## 3. The fiber chain, its stop, and the strict structure

**3.1 Construction.** $Y_0 := \emptyset$, $Y_{\alpha+1} := H_1(Y_\alpha)$, colimits at limits, with transitions as in StrictMahlo.md §5.1. As there (Lemma 5.2), every transition is a monomorphism, every $q_\alpha : Y_\alpha \to R_1$ is a Kan fibration (Lemma 2.3), and every reading is a map into $U$.

**Lemma 3.1 (comparison).** Let $\delta$ be an uncountable regular cardinal, and suppose that for every simplex $s$ of $Y_\delta$ over $(x, \tau)$ the decoded points of $x$ and the fiber points of $s$ have fewer than $\delta$ simplices. Then $Y_\delta \to H_1(Y_\delta)$ is an isomorphism, and so is every later transition.

*Proof.* As StrictMahlo.md's Lemma 5.3. A simplex of $H_1(Y_\delta)$ draws from $Y_\delta$ at most a head $s$ and a map $t$ out of the fiber points of $s$; these have fewer than $\delta$ simplices, each in some stage, so $t$ lands in one stage by the regularity of $\delta$. The base data $(a, b)$, $(a, y, y')$, $\tau$ and the points $w, w'$ are not drawn from $Y$. ∎

**Proposition 3.2.** Put $Y := Y_\kappa$ and $\theta_1 := \iota_{\kappa,\kappa+1}^{-1} : H_1(Y) \to Y$. Then $(Y, \theta_1)$ is an $H_1$-algebra in $\mathcal T$, initial, also after base change along every $g : O_1' \to O_1$, and $q : Y \to R_1$ is a Kan fibration.

*Proof.* The decoded points of a base code and the fiber points of a fiber code are pulled back from $\pi$ along maps into $U$, so they have fewer than $\kappa$ simplices ((U1), StrictMahlo.md's Lemma 1.1, and part (2) of that lemma for the fiber points over the decoded points); Lemma 3.1 applies with $\delta := \kappa$. Initiality is Adámek's argument, as in StrictMahlo.md's Proposition 5.5. ∎

Fix an $n$-simplex $\tau = (\sigma, \varphi)$ of $O_1$, let $R^\sigma := \sigma^{\ast}R$, and let $Y^{\tau}_\alpha$ be the chain of the step functor built over $\tau^{\ast}R_1 \cong R^{\sigma}$ with the fiber operator $\tau$. By Lemma 2.2, $\tau^{\ast}Y_\alpha \cong Y^{\tau}_\alpha$ compatibly with transitions, as in StrictMahlo.md's Lemma 6.1.

**Lemma 3.3 (stages below $\kappa$).** $\lVert Y^{\tau}_\alpha \rVert < \kappa$ for every $\alpha < \kappa$.

*Proof.* As StrictMahlo.md's Lemma 6.9. $R^{\sigma}$ is $\kappa$-small (StrictMahlo.md's Theorem 7.1), so it and its families $F_{R^\sigma}$, identity data and branch data have fewer than $\kappa$ simplices ($\kappa$ a regular strong limit, every decoded-point space $\kappa$-small). At a successor, with $\lVert Y^{\tau}_\beta \rVert < \kappa$: the constants contribute $\aleph_0$; a simplex of $F^{Y}$ is a base family, a head and a map from fewer than $\kappa$ fiber points into $Y^{\tau}_\beta$, so there are fewer than $\kappa$ of them; $I^Y$ and $B^Y$ add points of fibers of $\pi$, each with fewer than $\kappa$ simplices. Limits below $\kappa$ by regularity. ∎

**Lemma 3.4 (closure point of the growth; Mahlo).** For $\alpha < \kappa$ let $\zeta_1(\alpha)$ be the supremum of $\lVert Y^{\tau}_\alpha \rVert$ and, over the simplices $s$ of $Y^{\tau}_\alpha$, of the numbers of decoded points of their base codes and of fiber points of $s$. Then $\zeta_1(\alpha) < \kappa$, and there is an inaccessible $\lambda < \kappa$ with $\zeta_1(\alpha) < \lambda$ for every $\alpha < \lambda$.

*Proof.* StrictMahlo.md's Lemma 6.11, with Lemma 3.3 for the stages and (U1) for the decoded and fiber points. ∎

**Lemma 3.5 (local stabilization).** With $\lambda$ as in Lemma 3.4, $Y^{\tau}_\lambda \to H_1(Y^{\tau}_\lambda)$ is an isomorphism, so $Y^{\tau}_\kappa \cong Y^{\tau}_\lambda$, and $\lVert Y^{\tau}_\lambda \rVert \le \lambda$.

*Proof.* StrictMahlo.md's Lemma 6.12: a simplex of $H_1(Y^{\tau}_\lambda)$ draws a head $s$ from a stage $\beta < \lambda$, whose fiber points number at most $\zeta_1(\beta) < \lambda$, and a map $t$ out of them, which lands in one stage below $\lambda$ by the regularity of $\lambda$. ∎

**Theorem 3.6.** $q : Y \to R_1$ is a $\kappa$-small Kan fibration.

*Proof.* Kan by Proposition 3.2. Over an $n$-simplex $(x, \tau)$ of $R_1$, the fiber of $q$ lies in $\tau^{\ast}Y \cong Y^{\tau}_\kappa \cong Y^{\tau}_\lambda$, a stage below $\kappa$, of size $< \kappa$ by Lemma 3.3; StrictMahlo.md's Lemma 1.1. ∎

**Theorem 3.7 (residence and the strict structure).** Theorem D holds.

*Proof.* By (U1) there are $r_1 : R_1 \to U$ and an isomorphism $\psi : Q := r_1^{\ast}\tilde U \to Y$ over $R_1$; put $k := k_Y \circ (\psi \times_R E_R)$, so that $\psi$ is an isomorphism in $\mathcal T$, and $\theta_Q := \psi^{-1} \circ \theta_1 \circ H_1(\psi)$ is an $H_1$-algebra with $k \circ \theta_Q = k_{H(Q)}$. The operations are $\theta_Q$ on the summands: $\varepsilon_c := \theta_Q \circ \mathrm{in}_{\mathbf c}$, $\mathsf{product}_1 := \theta_Q \circ \mathrm{in}_{\Pi}$, …, $\mathsf{identity}_1 := \theta_Q \circ \mathrm{in}_{\mathsf{Id}}$, $\mathsf{result}_1 := \theta_Q \circ \mathrm{in}_{\mathsf{res}}$, $\mathsf{branch}_1 := \theta_Q \circ \mathrm{in}_{\mathsf{br}}$, each over the base operation of its tag, by the definition of $q_H$. The equation $k \circ \theta_Q = k_{H(Q)}$, read on each summand, is the list of laws of Theorem D except the last, and moreover $k(\mathsf{result}_1(f), z) = P(z)$ and $k(\mathsf{branch}_1(f, y, w), v) = P'(y, w, v)$, with $(P, P') = \mathrm{ev}_1(\tau, J_R(a, b), K_Q(f))$.

For $\mathsf{inner}_1$, let $f = ((a, b), \tau, s, t)$ be an $n$-simplex of $F^Q$, and recall $\mathsf{inner}(a, b) = (\mathsf{result}(a, b), b')$ with $b'(u, y) = \mathsf{branch}(u^{\ast}(a, b), y)$ for a decoded point $(u, y)$ of $c_{a,b}$, $u$ a simplex of $\Delta^n$ (proof of StrictMahlo.md's Theorem 7.2). Put $s' := \mathsf{result}_1(f)$, over $(\mathsf{result}(a, b), \tau)$, and for a point $w$ of $P$ over $(u, y)$
$$
t'((u, y), w) := \mathsf{branch}_1(u^{\ast}f, y, w), \quad \text{over } (b'(u, y), \tau u),
$$
so that $\mathsf{inner}_1(f) := (\mathsf{inner}(a, b), \tau, s', t')$ is a simplex of $F^Q$, natural in $\theta$. The value of $\mathrm{ev}_1$ is natural, $\mathrm{ev}_1(\tau u, J_R(u^{\ast}(a, b)), K_Q(u^{\ast}f)) = u^{\ast}(P, P')$, as $\mathrm{ev}$ is in the computation of StrictMahlo.md's Theorem 7.2, $\beta_{u^{\ast}(a,b)}(\iota, y) = \beta_{a,b}(u, y)$. So
$$
\begin{gathered}
k(s', (u, y)) = P(u, y), \qquad k(t'((u, y), w), v) = (u^{\ast}P')(y, w, v) = P'((u, y), w, v), \\
K_Q(\mathsf{inner}_1(f)) = (P, P') = \mathrm{ev}_1(\tau, J_R(a, b), K_Q(f)),
\end{gathered}
$$
the last law. No transport occurs: the reading of the result fiber code is $P$ itself, and that of each branch fiber code is $P'$ at its point, over base codes whose labels are, by Theorem A, $c_{a,b}$ and $\beta_{a,b}(u, y)$ themselves. ∎

**Corollary 3.8 (induction over fiber codes).** $(Q, \theta_Q)$ is an initial $H_1$-algebra, also after base change; so the model has strict induction over fiber codes, with its computation rules equalities of maps, as StrictMahlo.md's Corollary 7.3. `StrictDisplayMahlo` does not ask for it.

## 4. The corollaries

**Proof of Corollary D′.** Under T1, `Ambient.Operator ℓ` is $O$, `Σ (Ambient.Operator ℓ) FiberOperator` is $O_1$, `Fibers` is $\mathrm{Fib}$ over $F$, and the glued fibers are the maps (U2₁) (§1.3). The fields of `StrictDisplayMahlo` are read as maps: `carrier`, `interpret` and the base operations as in StrictMahlo.md's proof of Corollary B; `fibers` as $r_1$, a map out of $R_1$, the interpretation of the context of an operator, a fiber part over it and a base code; `read` as $k$; `emptyFiber`, …, `naturalFiber` as $\varepsilon_c$; `productFiber`, `sumFiber`, `treeFiber` as maps out of $F^Q$, the interpretation of `CodeFibers`; `identityFiber` out of $I^Q$; `innerFiber` as $\mathsf{inner}_1$. Each law of `StrictDisplayMahlo` is an equality of pairs (`Split`, `SplitFamily`), a base function with a fiber function over it; under T1 it is the equality of the two base maps, Theorem A's law, together with the equality of the two fiber maps over them, the matching law of Theorem D. The base fields are Theorem A's, so `ambient` gives the element of StrictMahlo.md's Corollary B. ∎

**Proof of Corollary E.** As StrictMahlo.md's proof of Corollary C, with Corollary D′ for the hypothesis of the display model's `consistent-with-Mahlo`. ∎

## 5. Remarks and discriminators

1. **Indexed induction–recursion, here strict.** A fiber code's children are fiber codes over other base codes ($s$ over $a$, $t(z, w)$ over $b(z)$): the fiber codes are an indexed induction–recursion over the base codes, with outputs in families of types. That already follows from the ambient Mahlo rule in book type theory: [Mahlo/DS](../Mahlo/DS/README.md)'s Polynomial derives indexed polynomial induction–recursion (Ghani, McBride, Nordvall Forsberg and Spahn's PN codes, which contain indexed Dybjer–Setzer codes) from smallness, equivalently the ambient rule, with no induction–recursion in its cone, and Polynomial/Outputs allows outputs in families of types. So with Theorem A the display universe's rule holds in this model up to identity. Those derivations prove their decoding laws under extensionality for families of information over the arities, which this model does not interpret by reflexivity (contrast [UniversalIR.md](UniversalIR.md)'s Lemma 7.1, whose witnesses are built from refl), and the strict route through a realization is blocked in two-level Agda. `StrictDisplayMahlo` asks for equalities of maps, which §2–§3 give directly. UniversalIR.md's Theorems U and U′ give strict laws for codes that are not indexed. [IndexedUniversalIR.md](IndexedUniversalIR.md)'s Theorem P gives them for indexed codes, and Theorem D is its instance at the display fiber schemes (Corollary F there), with the fiber chain of §3 its local chain.
2. **The fiber chain is needed.** Theorem A alone names no fiber code for the fiber part's outputs: two fiber operators over one base operator, constant at different fiber data, have one base carrier and different fiber codes. That is why $Q$ lies over $R_1 = R \times_O O_1$ and not over $R$, matching the obstruction found in Agda (an ambient operator sees only decoded types).
3. **The constant fiber operator at a large family.** For $\mu < \kappa$ and $X_\mu$ the nerve of the indiscrete groupoid on $\mu$ objects, let $\tau_\mu$ be the fiber operator over any $\sigma$ whose fiber part is constant at fiber data with $P$ constant at $X_\mu$. The result fiber code of any family reads $X_\mu$ itself (§2.1, $k_H$ on $\mathsf{res}$), as in StrictMahlo.md's discriminator 1; a carrier chosen in advance would need to contain it.
4. **Why the tags matter.** Without Lemma 1.1 the summands of $H_1$ would not be Kan fibrations over $R_1$: the constant fiber codes lie over the constant base codes alone, and a fiber code over one base code with no fiber code over a base code joined to it by a path would break lifting. The base codes of different tags lie in different components, so each summand is a fibration over its own part.
5. **No fibrant replacement, no unique names.** As in StrictMahlo.md's discriminators 4 and 5: every constructor of $H_1$ is a point constructor with Kan parameters, and the reading $k$ is not an embedding.

The hypothesis is also inhabited inside Agda with induction–recursion (checked; a vacuity check, not part of this model).

## 6. Checked, cited, proved here

| Item | Status |
| --- | --- |
| §1–§4: Lemma 1.1, Lemmas 2.2, 2.3, 3.1, 3.3, 3.5, Proposition 3.2, Theorems 3.6, 3.7, Corollaries 3.8, D′, E | Proved here, on paper, by StrictMahlo.md's arguments with the new points stated |
| Lemma 3.4, the closure point of the fiber chain's growth | On paper; its cardinal steps, a closure point from `MahloOrdinals` and regularity over a request's support, are checked for one-level requests in `StrictMahlo/Measured` (cubical Agda, not included in this release), whose record a fiber code with its fiber points instantiates; not instantiated for $\zeta_1$ in Agda |
| Theorem 3.7's reading of $\theta_Q$: each law of `StrictDisplayMahlo` is the label law on its summand, base and fiber together, and $\mathsf{inner}_1$ pairs the result fiber code with its branch fiber codes | Checked in Agda (LCTT's display model, not yet released): a labelled algebra of the fiber step gives `StrictDisplayMahlo` with the complete `inner-β`, base and fiber; an inductive–recursive family of fiber codes inhabits the hypothesis; such algebras at every stratum's level give the display model's `consistent-with-Mahlo` |
| Theorem A, Lemma 1.1 of StrictMahlo.md, K1–K6, T1, T2 | As in StrictMahlo.md |
| The Agda side: `StrictDisplayMahlo`, its base half (`ambient`), I1′ from it and `consistent-with-Mahlo` in the display model | Checked in Agda (LCTT's display model, not yet released) |
