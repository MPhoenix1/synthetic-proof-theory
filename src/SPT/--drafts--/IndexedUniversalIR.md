# Indexed induction–recursion in simplicial sets

Status: proof on paper, 2026-11-03. The Agda side is checked in [IR/Indexed](../IR/Indexed/README.md): one induction–recursive family for all schemes of indexed polynomial induction–recursion, with its realized laws by refl and no extensionality, and its comparison with ordinary arguments and their induction under extensionality at products. This note builds that family in simplicial sets, every realized law an equality of maps (Theorem P, the indexed counterpart of [UniversalIR.md](UniversalIR.md)'s Theorem U). It then shows that [StrictDisplayMahlo.md](StrictDisplayMahlo.md)'s Theorem D, the fiber codes of LCTT's display model, is its instance at one family of schemes (Corollary F). It was independently audited. Theorem P and Corollary O stand, with three points now explicit: the bound that stops the code chain (§1.1), the chosen transport (§0, §2.1), and contexts rooted at the rule codes (§2.2, §4). Corollary F's scheme took its argument types from (U2), which fixes no decodings; it is repaired by classifying them through (U1) (§8). Corollary Q, the presheaf case of §9's remark 6, was checked step by step; the changes to the proof are in §11.

The conventions, cited facts and assumptions are those of [StrictMahlo.md](StrictMahlo.md) §1: Lemma 1.1 on sizes, K1–K6 from Kapulkin–Lumsdaine (KL), and T1, T2. Of its Definition 1.3, Theorem P uses only (U1). The construction is UniversalIR.md's, with two changes: the pairs of a scheme and an index replace the codes, and arguments are trees of dependent sums and products rather than paths. Steps that are the same as there are cited by number; unqualified numbers refer to this note.

## 0. Results

Fix a strongly Mahlo cardinal $\kappa$ and a Kan fibration $\pi : \tilde U \to U$ with (U1) at $\kappa$: the small types, for indices and arities. Fix also a Kan fibration $\pi' : \tilde U' \to U'$ with Σ- and Π-structures, containing $U$ as a sub-simplicial set with $\pi$ the restriction of $\pi'$: the large types, for information and data. It also carries an identity structure with a chosen transport of points along its paths, the identity at reflexivity; bare Σ- and Π-structures do not name this datum. KL's universe at an inaccessible $\kappa' > \kappa$ is one (K5, K6), its transport given by J, which computes strictly on reflexivity. No size condition is put on $\pi'$. The new ingredients are defined in §1:

- **codes.** For an index type $I$, a simplex of $U$, and data $D : I^{\ast}\tilde U \to U'$, the codes over $(I, D)$, each indexed by its information type in $U'$. There are four kinds: an index ($\mathsf{var}$), a constant ($\mathsf{con}$), a dependent sum whose continuation reads the information of its first part ($\mathsf{sigma}$), and a dependent product ($\mathsf{pi}$). Each carries an identification of its index with the information its former computes. These are IR/Polynomial's codes.
- **schemes.** The simplicial set $\mathcal S$ of schemes $s = (I, D, \rho)$. Here $\rho$ gives, at each index point $i$, a code $c_i$ and an output $\mathrm{out}_i$ from the points of its information type to those of $D(i)$.
- **indices and labels.** The simplicial set $\mathbb I \to \mathcal S$ of a scheme with an index point, and the labels $\mathbb D \to \mathbb I$, the points of $D(i)$.

**Theorem P.** There are a map $u : \mathbb I \to U$ and, writing $T := u^{\ast}\tilde U \to \mathbb I$ for the universal family:

- a map $\mathrm{value} : T \to \mathbb D$ over $\mathbb I$, the readout;
- an isomorphism $\mathrm{intro} : \mathrm{Args}_T \to T$ over $\mathbb I$. Here $\mathrm{Args}_T \to \mathbb I$ is the family of arguments of each index's code over $T$ at the same scheme, with labels $\mathrm{value}$ (§2), and $\mathrm{info}$ is their information.

The following hold as equalities of maps of simplicial sets:

$$
\mathrm{value} \circ \mathrm{intro} = \mathrm{out} \circ \mathrm{info} \qquad \text{(decoding)}
$$

and, for every Kan fibration $\varpi : M \to T$ and every method $m$ (§6), there is a section $\bar m$ of $\varpi$ with

$$
\bar m \circ \mathrm{intro} = m \circ (\mathrm{id}, \mathrm{calls}\, \bar m) \qquad \text{(induction)}
$$

where $\mathrm{calls}\, \bar m$ collects $\bar m$ at the children of an argument. The data are stable under pullback along every map $\mathcal S' \to \mathcal S$.

These are IR/Indexed's realized laws, `output-β`, `ind-β`, `root-β` and `section`; `info-sigma` and `info-pi` are clauses of §2.1. That reading uses T1 with two extensions:
- to inner inductive families whose constructors target a variable index, which IR/Polynomial's codes are (§1.4);
- to Agda's mutual definitions, as in UniversalIR.md.

**Corollary O (ordinary arguments).** In this model the arguments of a code are defined once, for every family with labels (§2.1). So the ordinary arguments over the universal family are the native ones:
- $\mathrm{intro}$ is introduction on ordinary arguments, with its decoding equation an equality of maps;
- induction's hypotheses are computed at the children of the argument itself (§7).

The Agda terms of Indexed/Comparison and Indexed/Induction take the extensionality hypothesis, and are not claimed to be read by reflexivity.

**Corollary F (the display fiber codes).** Assume (U2) and (U2₁) of StrictDisplayMahlo.md, and that $U$ is a Kan complex classified by a vertex of $U'$ (for KL's universes, by K2 and K3). The scheme's argument types are classified by (U1), with their classification isomorphisms kept; (U2) and (U2₁) supply only its output labels (§8). Let $\varsigma : O_1 \to \mathcal S$ send a fiber operator to the scheme of the display fiber codes (§8):
- the index type is the base codes at its base operator;
- the data are the families over their decoded points;
- each base code gets the code of its tag.

Pulling Theorem P back along $\varsigma$ gives StrictDisplayMahlo.md's Theorem D, with every law an equality of maps.

**Corollary Q (presheaf toposes).** Let $\mathcal C$ be a category in $V_\kappa$, and $\kappa' > \kappa$ inaccessible. In presheaves on $\mathcal C$, take for $\pi$ the Hofmann–Streicher universe of the $V_\kappa$-valued presheaves, and for $\pi'$ that of the $V_{\kappa'}$-valued ones, whose transport is the identity at its equalities. Then Theorem P and Corollary O hold with every Kan condition dropped; the motive $\varpi$ of the induction equation may be any map into $T$. This is remark 6 of §9; §11 lists the changes to the proof.

The Mahlo property is used once, in Lemma 4.2, to make each scheme's fibers $\kappa$-small; the global construction (§2, §3) uses only that $\kappa$ is inaccessible. The information and the data may be large. The counts involve only arities, which are simplices of $U$, and children. They never involve information or labels.

## 1. Codes and schemes

**1.1 Codes.** Let $\mathcal P$ be the simplicial set of parameters. Its $n$-simplices are pairs $(I, D)$ of an $n$-simplex $I$ of $U$ and a map $D : I^{\ast}\tilde U \to U'$, and $\theta$ acts by restriction. The codes $\mathrm{Code} \to \mathcal P$, with their information types $\mathrm{Inf} : \mathrm{Code} \to U'$, are the initial algebra of an endofunctor of the slice over $\mathcal P \times U'$. Its $n$-simplices over $(I, D)$ and an $n$-simplex $W$ of $U'$, the index, are:

- $\mathsf{var}(i, e)$, for an $n$-simplex $i$ of $I^{\ast}\tilde U$ over the top simplex;
- $\mathsf{con}(A, e)$, for an $n$-simplex $A$ of $U$;
- $\mathsf{sigma}(c, h, e)$, for a code $c$ and a map $h$ from the points of $\mathrm{Inf}(c)$ to codes;
- $\mathsf{pi}(A, h, e)$, for an $n$-simplex $A$ of $U$ and a map $h$ from $A^{\ast}\tilde U$ to codes.

In each, $e$ is an $n$-simplex of the identity type of $U'$ from the information the former computes to $W$. The information computed is $D(i)$, $A$, $\Sigma_{U'}(\mathrm{Inf}(c), \mathrm{Inf} \circ h)$ and $\Pi_{U'}(A, \mathrm{Inf} \circ h)$ respectively, and $\mathrm{Inf}$ of the code is $W$.

This is IR/Polynomial's `Poly`, with `var-along`, `con-along`, `sigma-along` and `pi-along`. Its codes with $e$ reflexivity are `var`, `con`, `sigma` and `pi`, the only ones Agda writes. From §2 on, where only the information depends on $e$, a code is written by its former alone, as $\mathsf{var}(j)$, $\mathsf{con}(A)$, $\mathsf{sigma}(c, h)$ and $\mathsf{pi}(A, h)$. It is the colimit of its initial chain, which stops at a regular cardinal $\mu'$ chosen above $\kappa$ and above the number of simplices of every fiber of $\pi'$. Such a $\mu'$ exists because $\pi'$ is a map of simplicial sets; for KL's universe at $\kappa'$, take $\mu' := \kappa'$. Every arity, the points of a simplex of $U$ or of $U'$, then has fewer than $\mu'$ simplices (StrictMahlo.md's Lemma 1.1). This bound only constructs the codes; it is not the Mahlo bound of §4. By Lambek's lemma an $n$-simplex of $\mathrm{Code}$ is exactly one of the four forms.

**1.2 Ranks.** As in UniversalIR.md §1, give each code its first-appearance rank in the initial chain. Restriction does not increase rank. After any restriction, $c$, $h(x)$ and $h(a)$ have smaller rank than $\mathsf{sigma}(c, h)$ and $\mathsf{pi}(A, h)$. Everything in §2 is defined by well-founded induction on rank, across dimensions, together with its restriction maps.

**1.3 Schemes.** A description over $(I, D)$ at an index point $i$ is a pair $(c, \mathrm{out})$, over the same simplex: a code $c$, and a map $\mathrm{out}$ from the points of $\mathrm{Inf}(c)$ to those of $D(i)$. The $n$-simplices of $\mathcal S$ are the triples $s = (I, D, \rho)$ with $(I, D) \in \mathcal P_n$ and $\rho$ assigning to every simplex $i$ of $I^{\ast}\tilde U$ a description $\rho(i) = (c_i, \mathrm{out}_i)$ at $i$, naturally in restriction. This is `Scheme ℓ κ`. Two derived simplicial sets:
- $\mathbb I$ is the pullback of $\pi$ along $s \mapsto I$, whose simplices are pairs $(s, i)$. So $\mathbb I \to \mathcal S$ is a $\kappa$-small Kan fibration.
- $\mathbb D$ is the pullback of $\pi'$ along $(s, i) \mapsto D(i)$, whose simplices are triples $(s, i, e)$ with $e$ a point of $D(i)$.

**1.4 The identifications make the codes fibrant.** Suppose $U$ and $U'$ are Kan complexes, as KL's universes are. Each summand of the endofunctor of §1.1 is a Kan fibration over $\mathcal P \times U'$:
- it pairs data that are Kan over $\mathcal P$, or over the codes by induction, with a point of an identity type of $U'$ ending at the index $W$;
- that identity type is a path fibration, Kan over $W$.

So, by the argument of Lemma 2.2 and the colimit lemma, $\mathrm{Code} \to \mathcal P \times U'$ is a Kan fibration.

This is why the index is a variable. With a computed index, `var i : Poly (D i)`, the family would not be a Kan fibration. Take:
- $I$ a vertex of $U$ with one point, which exists by (U1);
- $D$ constant at a vertex $X_0$ of $U'$;
- a 1-simplex $e$ of $U'$ from $X_0$ to a vertex $X_1 \ne X_0$. For KL's universe, take $X_0 := 1$ and $X_1$ the nerve of the indiscrete groupoid on two objects, which is equivalent to it.

A 1-simplex of codes over constant parameters starting at $\mathsf{var}(\star)$ would have to be a $\mathsf{var}$ code. Its information is $D$ at a 1-simplex of $I^{\ast}\tilde U$, hence degenerate. So $e$ has no lift at $\mathsf{var}(\star)$. With the identification, $\mathsf{var}(\star, e)$ is the lift.

So T1 reads IR/Polynomial's inner family `Poly ℓ κ D X` as $\mathrm{Code}$, once extended to inner inductive families whose constructors target a variable index. Such a family is read as an initial algebra in the slice, which is a fibration by the argument above. Agda's matching on `refl` is read through J, which in KL's model computes strictly on reflexivity. The construction below does not use the fibrancy of $\mathrm{Code}$, just as Theorem U does not use that of $C$; the reading of the Agda module does.

## 2. Arguments, information and the step functor

**2.1 Arguments.** Let $c$ be a code over $(I, D)$ at an $n$-simplex. Let $X \to I^{\ast}\tilde U$ carry labels $v$, with $v(x)$ a point of $D(j)$ for $x$ over $j$. By recursion on rank, define $\mathrm{Args}_c(X, v) \to \Delta^n$ and, over $\Delta^n$, $\mathrm{info} : \mathrm{Args}_c(X, v) \to \mathrm{Inf}(c)^{\ast}\tilde U'$:

- $\mathsf{var}(j, e)$: the elements of $X$ over $j$, that is $j^{\ast}X$, with $\mathrm{info}$ the label $v$;
- $\mathsf{con}(A, e)$: the points $A^{\ast}\tilde U$, with $\mathrm{info}$ the inclusion;
- $\mathsf{sigma}(c', h, e)$: pairs $(a, b)$, with $a$ a simplex of $\mathrm{Args}_{c'}(X, v)$ over $\theta : \Delta^m \to \Delta^n$ and $b$ a simplex of $\mathrm{Args}_{h(\mathrm{info}\, a)}(\theta^{\ast}X, v)$. Here $\mathrm{info}(a, b)$ is the pair $(\mathrm{info}\, a, \mathrm{info}\, b)$, through the Σ-structure.
- $\mathsf{pi}(A, h, e)$: the dependent product, along $A^{\ast}\tilde U \to \Delta^n$, of the family whose fiber over a point $a$ is $\mathrm{Args}_{h(a)}(X, v)$. Here $\mathrm{info}\, f$ is the abstraction of $a \mapsto \mathrm{info}\, f(a)$, through the Π-structure.

In each case the information so computed lies in the computed type, and $\mathrm{info}$ is its transport along $e$ into $W$, by the transport chosen in §0, the identity at reflexivity. The arguments themselves do not depend on $e$. These interpret IR/Indexed's `Args` and `info`, and IR/Polynomial's `Args` and `info` over any family. Those match the codes with $e$ reflexivity, and Agda's matching is J. The **children** of an argument are the simplices of $X$ at its $\mathsf{var}$ nodes. Its **positions** form a well-founded tree: one at $\mathsf{var}$, none at $\mathsf{con}$, those of $a$ and of $b$ at $\mathsf{sigma}$, and those of every $f(a)$ at $\mathsf{pi}$.

**2.2 Contexts.** A context over $(X, v)$, from a code $c$, is a finite sequence of steps:
- at $\mathsf{sigma}(c', h)$, either into $c'$, or past a complete argument $a$ of $c'$ over $(X, v)$ into $h(\mathrm{info}\, a)$;
- at $\mathsf{pi}(A, h)$, at a simplex $a$ of the arity, into $h(a)$.

The code where it ends is its end code. Ranks decrease along steps, so contexts are finite. A context records exactly what selects the codes below it: the first parts read so far and the points chosen. Contexts replace UniversalIR.md's partial paths.

The contexts of a scheme are those rooted at its rule codes $c_i$, for the simplices $i$ of $I^{\ast}\tilde U$, and at their restrictions. Only these are counted (§4). Rooting matters: contexts from every code would include the empty context at every code, already as many as the codes.

**2.3 The step functor.** Let $\mathcal E$ be the category of simplicial sets $Y$ with $p : Y \to \mathbb I$ and labels $d : Y \to \mathbb D$ over $\mathbb I$; morphisms commute with both. Only $p$ will be required to be a fibration. For an $n$-simplex $s$ of $\mathcal S$, write $Y_s := s^{\ast}Y \to I^{\ast}\tilde U$ for the elements at the indices of $s$. Let $H(Y)$ have as $n$-simplices the triples $(s, i, b)$, with $(s, i) \in \mathbb I_n$ and $b$ an $n$-simplex of $\mathrm{Args}_{c_i}(Y_s, d)$ over the top simplex. Put

$$
p_H(s, i, b) := (s, i), \qquad d_H(s, i, b) := \mathrm{out}_i(\mathrm{info}\, b).
$$

On a morphism, $H$ applies it to the children. Labels are kept, so informations and the continuations they select are unchanged.

**Lemma 2.1.**

1. $H$ is an endofunctor of $\mathcal E$ that preserves monomorphisms.
2. $H$ commutes with pullback along every map $g : \mathcal S' \to \mathcal S$.

*Proof.* Clause by clause on codes, as in UniversalIR.md's Lemma 2.1. A child at $\mathsf{var}(j)$ lies over another index $j$ of the same scheme. So $H$ is local in the scheme, not in the index, and it commutes with base change in $\mathcal S$. ∎

**Lemma 2.2 (fibrancy).** If $p : Y \to \mathbb I$ is a Kan fibration, so is $p_H$.

*Proof.* A map is a Kan fibration if its pullback along every simplex of the base is one. By induction on rank, $\mathrm{Args}_c(Y_s, d) \to \Delta^n$ is a Kan fibration for every code $c$ over an $n$-simplex $s$:

- $\mathsf{var}(j)$: $j^{\ast}Y_s$ is the pullback of $p$ along $(s, j) : \Delta^n \to \mathbb I$;
- $\mathsf{con}(A)$: $A^{\ast}\tilde U$ is a pullback of $\pi$;
- $\mathsf{sigma}(c', h)$: the pairs map to $\mathrm{Args}_{c'}$ by a map whose pullback along each simplex $(\theta, a)$ is $\mathrm{Args}_{h(\mathrm{info}\, a)}$. That is Kan by induction, and so is its composite with $\mathrm{Args}_{c'} \to \Delta^n$.
- $\mathsf{pi}(A, h)$: the dependent product, along the Kan fibration $A^{\ast}\tilde U \to \Delta^n$, of a map that is Kan over each simplex of the arity by induction. It is Kan by K4.

The information only selects continuations; no fibration condition on it is used. ∎

Filtered colimits over $\mathbb I$ of Kan fibrations are Kan fibrations (StrictMahlo.md, Lemma 4.2).

## 3. The global chain

Define $Y_0 := \emptyset$, $Y_{\alpha+1} := H(Y_\alpha)$ and colimits at limits, with transitions as in StrictMahlo.md 5.1. Every transition is a monomorphism and every $p_\alpha$ is a Kan fibration (Lemma 2.2).

**Lemma 3.1 (comparison).** Let $\delta$ be an uncountable regular cardinal. Suppose every arity at every $\mathsf{pi}$ node reached by an argument of $H(Y_\delta)$ has fewer than $\delta$ simplices. Then $Y_\delta \to H(Y_\delta)$ is an isomorphism, and so is every later transition.

*Proof.*
- **Few children.** By induction on rank, an argument has fewer than $\delta$ children. $\mathsf{sigma}$ joins two sets of fewer than $\delta$, and $\mathsf{pi}$ unites fewer than $\delta$ of them, $\delta$ being regular.
- **One stage.** Each child lies in a stage below $\delta$, so all lie in one stage $\beta < \delta$.
- **Same continuations.** Transitions keep labels, so the argument has the same information over $Y_\beta$, hence the same continuations. It lies in $H(Y_\beta) = Y_{\beta+1}$. ∎

**Proposition 3.2.** Put $Y := Y_\kappa$ and $\theta := \iota_{\kappa,\kappa+1}^{-1}$. Then $(Y, \theta)$ is an initial $H$-algebra in $\mathcal E$, also after base change along every $\mathcal S' \to \mathcal S$, and $p : Y \to \mathbb I$ is a Kan fibration.

*Proof.* Every arity is a simplex of $U$, so it is $\kappa$-small by (U1) and StrictMahlo.md's Lemma 1.1, and Lemma 3.1 applies at $\kappa$. Initiality is Adámek's argument. Fibrancy is Lemma 2.2 with the colimit lemma. ∎

So the universal family exists over all schemes and indices at once, every label literal, using only that $\kappa$ is inaccessible.

## 4. Local bounds

Fix an $n$-simplex $\sigma : \Delta^n \to \mathcal S$, a scheme over $\Delta^n$, with index type $I$. By Lemma 2.1, $\sigma^{\ast}Y_\alpha \cong Y^\sigma_\alpha$, the chain of the step functor $H^\sigma$ of this scheme. It lies over $I^{\ast}\tilde U$, which has fewer than $\kappa$ simplices.

**Lemma 4.1 (small stages).** For every $\alpha < \kappa$, $Y^\sigma_\alpha$ has fewer than $\kappa$ simplices, and fewer than $\kappa$ contexts of the scheme, rooted at its rule codes (§2.2), run over it.

*Proof.* By induction on $\alpha$. Let $X$ be a stage with fewer than $\kappa$ simplices.

- **Arguments.** By induction on rank, every code has fewer than $\kappa$ argument simplices over $X$:
  - $\mathsf{var}$ takes simplices of $X$;
  - $\mathsf{con}$ takes points of $A^{\ast}\tilde U$, fewer than $\kappa$ by (U1);
  - $\mathsf{sigma}$ takes pairs: fewer than $\kappa$ first parts, each with fewer than $\kappa$ second parts;
  - $\mathsf{pi}$ takes maps from an arity of fewer than $\kappa$ simplices into fewer than $\kappa$, $\kappa$ being a strong limit.
- **The step.** $H^\sigma(X)$ consists of the arguments at the fewer than $\kappa$ index simplices, over the countably many simplices of $\Delta^n$.
- **Contexts.** A rooted context starts at one of the fewer than $\kappa$ rule codes $c_i$ and their restrictions. Each step chooses among fewer than $\kappa$ complete arguments or arity simplices. By induction on the length, fewer than $\kappa$ contexts have length $k$, and there are countably many lengths.

At a limit $\alpha < \kappa$ the stage is a union of fewer than $\kappa$ stages, $\kappa$ being regular. ∎

**The growth function.** For $\alpha < \kappa$, let $\zeta(\alpha)$ be the supremum of two families of cardinals:
- $\lVert Y^\sigma_\alpha \rVert$;
- the sizes $\lVert A^{\ast}\tilde U \rVert$ of the arities $A$ of the $\mathsf{pi}$ end codes of rooted contexts over $Y^\sigma_\alpha$.

It is a supremum, not a maximum. By Lemma 4.1, $\kappa$ being regular, $\zeta(\alpha) < \kappa$.

**Lemma 4.2 (closure point; Mahlo).** There is an inaccessible $\lambda < \kappa$ with $\zeta(\alpha) < \lambda$ for every $\alpha < \lambda$.

*Proof.* As in UniversalIR.md's Lemma 4.2. ∎

**Lemma 4.3 (stabilization).** $Y^\sigma_\lambda \to H^\sigma(Y^\sigma_\lambda)$ is an isomorphism. So $Y^\sigma_\kappa \cong Y^\sigma_\lambda$, which has at most $\lambda$ simplices.

*Proof.* Prove by induction on the rank of $c$: for every rooted context $\Gamma$ over a stage $Y^\sigma_\beta$ with $\beta < \lambda$ and end code $c$, the children of every argument $b$ of $c$ over $Y^\sigma_\lambda$ lie in one stage below $\lambda$.

- **$\mathsf{var}$.** The child is a simplex of $Y^\sigma_\lambda$, which is the union of the stages below $\lambda$.
- **$\mathsf{con}$.** There are no children.
- **$\mathsf{sigma}(c', h)$, with $b = (a, b')$.**
  - By induction, with $\Gamma$ extended into $c'$, the children of $a$ lie in a stage $\gamma_1 < \lambda$.
  - So $a$ is an argument over $Y^\sigma_{\gamma_1}$ with the same information, since transitions keep labels.
  - Then $\Gamma$ extended past $a$ is a context over $Y^\sigma_{\max(\beta, \gamma_1)}$ ending at $h(\mathrm{info}\, a)$, and induction gives a stage $\gamma_2 < \lambda$ for $b'$.
- **$\mathsf{pi}(A, h)$, with $b = f$.**
  - The code is the end code of $\Gamma$, a context over $Y^\sigma_\beta$, so its arity has at most $\zeta(\beta) < \lambda$ simplices.
  - For each of them, $\Gamma$ extended at that point is a context over $Y^\sigma_\beta$, and induction gives a stage below $\lambda$ for that branch of $f$.
  - There are fewer than $\lambda$ such stages, all below $\lambda$, so they have an upper bound below $\lambda$, $\lambda$ being regular.

Applied to the empty context at each index, every element of $H^\sigma(Y^\sigma_\lambda)$ lies in some $H^\sigma(Y^\sigma_\gamma) = Y^\sigma_{\gamma+1}$ with $\gamma < \lambda$. So the comparison map is onto. It is a monomorphism, hence an isomorphism, and so is every later transition. Finally $Y^\sigma_\lambda$ has at most $\sum_{\alpha<\lambda}\zeta(\alpha) \le \lambda$ simplices. ∎

The information and the labels enter only through the continuations they select; the counts are of choices, arities and children.

## 5. Smallness and residence

**Theorem 5.1.** $p : Y \to \mathbb I$ is a $\kappa$-small Kan fibration.

*Proof.* Take an $n$-simplex $(s, i)$ of $\mathbb I$. The fiber over it lies in $s^{\ast}Y \cong Y^s_\kappa \cong Y^s_\lambda$, which has at most $\lambda < \kappa$ simplices (Lemmas 2.1 and 4.3). Conclude by StrictMahlo.md's Lemma 1.1. ∎

By (U1) there are $u : \mathbb I \to U$ and an isomorphism $\varphi : T := u^{\ast}\tilde U \to Y$ over $\mathbb I$. Put $\mathrm{value} := d \circ \varphi$ and $\mathrm{intro} := \varphi^{-1} \circ \theta \circ H(\varphi)$. Since $H(\varphi)$ keeps labels, $\mathrm{value} \circ \mathrm{intro} = d_H \circ H(\varphi) = \mathrm{out} \circ \mathrm{info}$ on every simplex. This is the decoding equation of Theorem P, and no transport occurs: the label of an introduced element is literally the output of its argument's information. The family $\mathrm{Args}_T \to \mathbb I$ of Theorem P is $H(T) \to \mathbb I$.

## 6. Induction

A method over a Kan fibration $\varpi : M \to T$ is a map

$$
m : \Sigma_{b \in H(T)} \mathrm{Hyp}(b) \to M, \qquad \varpi \circ m = \mathrm{intro} \circ \mathrm{pr}_1
$$

where $\mathrm{Hyp}(b)$ is the family of points of $M$ over the children of $b$: a point over the child at $\mathsf{var}$, pairs at $\mathsf{sigma}$, and dependent products at $\mathsf{pi}$. This is IR/Indexed's `Hyp`.

**Lemma 6.1.** $H(M)$, with the projection and labels of $T$, is isomorphic over $H(T)$ to $\Sigma_{b \in H(T)} \mathrm{Hyp}(b)$.

*Proof.* Clause by clause on codes. The labels of $M$ are those of $T$, so an argument over $M$ maps to one over $T$ with the same information. It therefore has the same continuations, and at $\mathsf{var}$ a child in $M$ is a child in $T$ with a point of $M$ over it. ∎

So $m$ is an $H$-algebra on $M$, and $\varpi$ is a morphism of $H$-algebras.
- **The section.** Initiality (Proposition 3.2, transferred along $\varphi$) gives a unique algebra map $\bar m : T \to M$. Then $\varpi \circ \bar m$ is an algebra map $T \to T$, hence the identity, so $\bar m$ is a section.
- **The laws.** That $\bar m$ is an algebra map is the induction equation, IR/Indexed's `ind-β`. For the motive whose fiber is the arguments, it is `root-β`, and $\mathrm{intro}$ is an isomorphism (`section`).
- **Stability.** Pullback along $\mathcal S' \to \mathcal S$ keeps the initial algebra (Lemma 2.1), so eliminators are stable.

## 7. Corollary O: ordinary arguments

§2.1 defines the arguments of a code for every family with labels. The ordinary arguments of IR/Polynomial over the universal family are the arguments of the code over $(T, \mathrm{value})$. So in this model they are literally $\mathrm{Args}_T$, with the same information. Hence:
- $\mathrm{intro}$ is introduction on them, and its decoding equation is an equality of maps;
- the induction of §6 is induction on them, with hypotheses at the children of the argument itself.

In Agda the two argument families are separate recursions, and Indexed/Comparison identifies them only under extensionality at $\mathsf{pi}$. Here they coincide by the function extensionality of set theory, at the level of simplicial sets. So the Agda terms `make-β`, `method-β` and `Induction.ind-β` are not claimed to be read by reflexivity: their witness `kept` applies the extensionality hypothesis at $\mathsf{pi}$, and the reading depends on how the model reads that hypothesis. This is the difference from UniversalIR.md's Lemma 7.1, whose witnesses are closed terms with no extensionality.

## 8. Corollary F: the display fiber codes

We use StrictDisplayMahlo.md's setting and notation:
- (U2) and (U2₁);
- Theorem A's base codes $p_R : R \to O$, with interpretation $i : R \to U$ and data $F_R$, $I_R$, $B_R$, $J_R$, $E_R$;
- the fiber operators $O_1$, with $\mathrm{ev}_1$, and $R_1 := R \times_O O_1$;
- its Lemma 1.1, by which $R$ is the disjoint union of its ten tag parts.

Write $\ulcorner U \urcorner$ for a vertex of $U'$ classifying $U$. A point of $\Pi_{U'}(i(x), \ulcorner U \urcorner)$ is then a family over the decoded points of $x$.

**Argument types by (U1).** (U2) supplies only maps and vertices: nothing makes the designated $1_U$ decode to one point, or $\Sigma_U$ to actual pairs. So the arities of the scheme are classified by (U1), once, over generic bases, keeping the classification isomorphisms:
- a vertex $1^\circ$ of $U$ with an isomorphism $\chi_1 : (1^\circ)^{\ast}\tilde U \cong \Delta^0$, classifying the terminal fibration;
- a map $S : G \to U$, where $G$ is the simplicial set of pairs $(x, P)$ of a simplex $x$ of $R$ and a point $P$ of $\Pi_{U'}(i(x), \ulcorner U \urcorner)$, with an isomorphism $\chi_\Sigma$ over $G$ from $S^{\ast}\tilde U$ to the dependent sum of the decoded points $z$ of $x$ and the points of $P(z)$. That dependent sum is a $\kappa$-small Kan fibration over $G$, the composite of two pullbacks of $\pi$, so (U1) classifies it.

The points of $S(x, P)$ are read through $\chi_\Sigma$ as pairs $(z, w)$. The supplied $1_U$ and the maps (U2₁) are used only as output labels.

**8.1 The scheme map.** For an $n$-simplex $\tau = (\sigma, \varphi)$ of $O_1$, define $\varsigma(\tau) := (I, D, \rho)$:

- $I := r(\sigma)$, so that $I^{\ast}\tilde U \cong \sigma^{\ast}R$, the base codes over $\sigma$;
- $D(x) := \Pi_{U'}(i(x), \ulcorner U \urcorner)$, the families over the decoded points of the base code $x$;
- $\rho(x)$ given by the tag of $x$, through the isomorphisms of that Lemma 1.1, in the table below.

The table uses one code at a family $(a, b)$ of $F_R$:

$$
\Phi(a, b) := \mathsf{sigma}\bigl(\mathsf{var}(a),\ P \mapsto \mathsf{pi}(S(a, P),\ (z, w) \mapsto \mathsf{var}(b(z)))\bigr),
$$

with $(z, w)$ read through $\chi_\Sigma$.

Its information is a pair $(P, T')$, read as the fiber data $\hat K := (P, (z, w, v) \mapsto T'(z, w)(v))$ over $J_R(a, b)$. Write $(P_{\mathrm{ev}}, P'_{\mathrm{ev}}) := \mathrm{ev}_1(\tau, J_R(a, b), \hat K)$.

| Tag of $x$ | Code $c_x$ | Output at the information |
| --- | --- | --- |
| $e_c(\sigma)$, for $c = 0, 1, 2, \mathbb N$ | $\mathsf{con}(1^\circ)$ | the constant family at $1_U$ |
| $\mathsf{sum}(a, b)$; likewise $\mathsf{product}$, $\mathsf{tree}$ | $\Phi(a, b)$ | $\Sigma_1(J_R(a, b), \hat K, \cdot)$; likewise $\Pi_1$, $W_1$ |
| $\mathsf{result}(a, b)$ | $\Phi(a, b)$ | $P_{\mathrm{ev}}$ |
| $\mathsf{identity}(a, y, y')$ | $\mathsf{sigma}(\mathsf{var}(a), P \mapsto \mathsf{sigma}(\mathsf{con}(P(y)), w \mapsto \mathsf{con}(P(y'))))$ | $\mathrm{Id}_1((i(a), y, y'), P, w, w', \cdot)$ at $(P, (w, w'))$ |
| $\mathsf{branch}((a, b), y)$ | $\mathsf{sigma}(\Phi(a, b), (P, T') \mapsto \mathsf{con}(P_{\mathrm{ev}}(y)))$ | $v \mapsto P'_{\mathrm{ev}}(y, w, v)$ at $((P, T'), w)$ |

Each clause is simplicial in $(\tau, x)$, so $\varsigma$ is a map of simplicial sets $O_1 \to \mathcal S$, and the pullback of $\mathbb I$ along it is $R_1$. StrictDisplayMahlo.md's Lemma 1.1 is used here and only here: a map out of $R$ may be given on each tag part.

**8.2 The step functors agree.** Take an object $Y$ of StrictDisplayMahlo.md's $\mathcal T$, with $q : Y \to R_1$ and reading $k$. It is an object of $\mathcal E$ pulled back along $\varsigma$: the label of a fiber code $s$ over a base code $x$ is the family $k(s, \cdot)$, a point of $D(x)$. Under this reading, $H$ pulled back along $\varsigma$ and that note's $H_1$ agree summand by summand, with equal labels:

- **At a constant.** An argument of $\mathsf{con}(1^\circ)$ is the one point of $(1^\circ)^{\ast}\tilde U$, through $\chi_1$, matching the constant summand $O_1$ of $H_1$. Its label is the constant family at $1_U$, as $k_H$ gives.
- **At $\mathsf{sum}(a, b)$.** An argument of $\Phi(a, b)$ is a pair $(s, t)$, which is $F^Y$'s quadruple:
  - $s$ is a fiber code over $a$, whose information is $P = k(s, \cdot)$;
  - $t$ is a map from the points of $S(a, P)$, read through $\chi_\Sigma$ as the fiber points $(z, w)$ of $s$, to fiber codes over the $b(z)$.

  Its information is $K_Y(f)$, and its label is $k_H((\Sigma, f), \cdot)$. Likewise at $\Pi$, $W$ and $\mathsf{res}$.
- **At $\mathsf{identity}(a, y, y')$.** The argument is $(s, w, w')$, which is $I^Y$'s tuple.
- **At $\mathsf{branch}((a, b), y)$.** The argument is $(f, w)$, which is $B^Y$'s triple.

The presentations differ only in packaging, by isomorphisms that keep every label: points of $S$ against pairs, through $\chi_\Sigma$; abstraction through the Π-structure of $\pi'$; and one-point arguments at the constants, through $\chi_1$. As in UniversalIR.md §10, removing the packaging keeps every label. So StrictDisplayMahlo.md's chain $Y_\alpha$ (§3 there) and the chain of §3 here pulled back along $\varsigma$ are isomorphic, compatibly with readings.

**Proof of Corollary F.** By 8.2, StrictDisplayMahlo.md's Proposition 3.2 and Theorems 3.6 and 3.7 are this note's Proposition 3.2 and Theorem 5.1, pulled back along $\varsigma$:
- $r_1$ is $u$ composed with the map $R_1 \to \mathbb I$ over $\varsigma$, and $Q$ is the pullback of $T$;
- $k$ is $\mathrm{value}$, uncurried;
- $\varepsilon_c$, $\mathsf{product}_1$, $\mathsf{sum}_1$, $\mathsf{tree}_1$, $\mathsf{identity}_1$, $\mathsf{result}_1$ and $\mathsf{branch}_1$ are $\mathrm{intro}$ at the tags.

The laws:
- **All but the last.** Each of Theorem D's laws except the last is the decoding equation at one tag.
- **$\mathsf{inner}_1$.** It and its law are built from $\mathsf{result}_1$ and $\mathsf{branch}_1$ exactly as in StrictDisplayMahlo.md's proof of Theorem 3.7, which uses only their two laws and the naturality of $\mathrm{ev}_1$.
- **Local bounds.** That note's Lemmas 3.3–3.5, the local bounds of its fiber chain, are Lemmas 4.1–4.3 here at the schemes $\varsigma(\tau)$. ∎

So Theorem D needs no chain of its own. Its Lemma 2.3, fibrancy through the tags, is replaced by Lemma 2.2 here, which needs no tags. The tags are needed only to write the scheme.

## 9. Remarks and discriminators

1. **Children and their families are kept.** In [IR/Indexed/Discriminator](../IR/Indexed/Discriminator.agda), two codes of the unit type decode alike by refl yet stay distinct, as do the sums over them, and root recovery returns the literal family. In the model the simplices of $T$ are argument trees with their literal children: no quotient and no fibrant replacement identifies them.
2. **No fibrancy of the readout, no unique names.** $\mathrm{value} : T \to \mathbb D$ is not asked to be a fibration, and it is not an embedding. This is UniversalIR.md §9, items 2 and 3.
3. **Mahlo only for smallness.** Without Lemma 4.2, Proposition 3.2 still gives the universal family over $\mathbb I$, one universe up.
4. **Large information and data.** The information types and the data may be any simplices of $U'$. The counts of §3 and §4 never see them: they enter only through the continuations they select.
5. **The index of a code is a variable.** See §1.4. With a computed index the codes would not be fibrant over their information. With the identification they are, and T1, extended to such families, reads IR/Polynomial's codes.
6. **Presheaf toposes.** Apart from Lemma 2.2, the construction uses only the slice, colimits, pullbacks, sizes, the classification of (U1) and initiality. It therefore runs in presheaves on a category in $V_\kappa$, with the Hofmann–Streicher universe and no Kan conditions, as UniversalIR.md's Corollary W does: the closure point of Lemma 4.2 is chosen above the number of arrows. It is stated as Corollary Q (§0), with the changes to the proof in §11.
7. **Why Corollary F's argument types come from (U1).** The scheme first used $\mathsf{con}(1_U)$ and $\Sigma_U$ themselves. (U2) permits a $1_U$ that decodes to the empty set. Then every constant clause has no argument, and every other clause starts with a recursive $\mathsf{var}$, so the chain stays empty, while StrictDisplayMahlo.md's step functor has inhabited constant summands. A $\Sigma_U$ that decodes to the empty set likewise leaves no pairs to evaluate at. The audit found this. Classifying the argument types by (U1) keeps the corollary at the generality of (U1), (U2) and (U2₁). Requiring genuine unit and Σ-structures, as KL's universe and T1 provide, would also repair it, but would narrow that generality.

## 10. Checked, cited, proved here

| Item | Status |
| --- | --- |
| The universal family, its realized laws by refl, the comparison and ordinary induction under extensionality, the discriminator | Checked in Agda ([IR/Indexed](../IR/Indexed/README.md)) |
| §1–§6: codes, the step functor and its fibrancy, the chain and its initial algebra, local bounds, smallness, induction | Proved here, on paper, citing UniversalIR.md where the steps coincide. New: tree-shaped arguments, contexts in the growth function, children at other indices |
| Lemmas 4.1–4.3 | On paper, with contexts rooted at the rule codes (§2.2). Lemma 4.3's induction is checked in Agda ([IR/Polynomial/Factorization](../IR/Polynomial/Factorization.agda)): over stages with a join and a bounding function for small families, and literal ranks, every argument of a code whose rooted paths over each stage request small arities lies in one stage, with its information kept (no transport); the finite stages discriminate. The stage structure below $\lambda$, the ranks and the growth bound (Lemmas 4.1, 4.2) stay hypotheses |
| §1.4: the codes, with their identifications, are fibrant over their information; with computed indices they would not be | On paper, with the counterexample there. The identifications are checked in Agda: IR/Polynomial's `var-along`, `con-along`, `sigma-along`, `pi-along`, its refl codes as pattern synonyms, and every dependent unchanged and rechecked |
| Corollary O | On paper; the Agda comparison terms are not claimed strict |
| Corollary Q: presheaf toposes on a category in $V_\kappa$ | On paper (§11), checked step by step: Kan conditions dropped, the size lemma at regular cardinals above the number of arrows, the closure point chosen above it |
| Corollary F: Theorem D as the instance at the display fiber schemes | On paper (§8); the step functors agree summand by summand, by label-preserving isomorphisms. Argument types classified by (U1), labels from (U2) and (U2₁): repaired after the audit (§9, item 7) |
| Reading IR/Indexed through T1 | On paper, with T1 extended to inner inductive families with variable indices (§1.4) and to Agda's mutual definitions, as UniversalIR.md extends it |
| K1–K6, T1, T2, Theorem A, StrictDisplayMahlo.md's setting | As in StrictMahlo.md and StrictDisplayMahlo.md |

## 11. Corollary Q: presheaf toposes

Work in presheaves on a category $\mathcal C$ in $V_\kappa$, with $\pi$ and $\pi'$ as in Corollary Q. Read "simplex" as "element of a presheaf", $\Delta^n$ as a representable $y\,c$, and $\theta : \Delta^m \to \Delta^n$ as an arrow $d \to c$ of $\mathcal C$. A map is $\mu$-small when each of its fibers, a presheaf on a slice $\mathcal C/c$, has fewer than $\mu$ elements in total. Every step of §1–§7 then goes through, with these changes.

- **Dropped.** §1.4, Lemma 2.2 with the colimit lemma after it, and the fibrancy of motives in §6. The construction never uses them (§1.4, last paragraph). The identity type of $U'$ is equality, so a code's identification $e$ is reflexivity and the transport of §0 is the identity.
- **The size lemma.** StrictMahlo.md's Lemma 1.1 holds for every regular $\mu$ above the number of arrows of $\mathcal C$, by the same proof: the countably many simplices $x\theta$ of $\Delta^m$ become the fewer than $\mu$ arrows into $c$. At $\mu = \kappa$ this needs $\mathcal C \in V_\kappa$. A $\kappa$-small family is then isomorphic to a $V_\kappa$-valued one, which the Hofmann–Streicher universe classifies: this is (U1), with the isomorphism $\varphi$ of §5. Pointwise smallness would not suffice: with $\kappa$ parallel arrows, a dependent product over a pointwise small arity can have $2^\kappa$ sections (UniversalIR.md §8).
- **§1.1.** $\mu' := \kappa'$ bounds every fiber of $\pi'$, since $\mathcal C \in V_{\kappa'}$.
- **Lemma 3.1.** Read "uncountable regular" as "regular and above the number of arrows of $\mathcal C$". Its three steps then use only that bound, the total sizes of the arities, and the labels kept by the transitions. Proposition 3.2 takes $\delta := \kappa$.
- **Lemma 4.1.** "The countably many simplices of $\Delta^n$" become the fewer than $\kappa$ arrows into $c$. At $\mathsf{pi}$, an argument is a natural family over all elements of the arity, at every stage into $c$; there are fewer than $\kappa$ such families, $\kappa$ being a strong limit.
- **Lemma 4.2.** The closure points of $\zeta$ above the number of arrows of $\mathcal C$ still form a club in $\kappa$, and the inaccessibles below $\kappa$ are stationary, so $\lambda$ is chosen above that number and the size lemma holds at $\lambda$ as well. Lemma 4.3 and Theorem 5.1 are unchanged.
- **Kept.** Lemma 2.1 and the stability in §3 and §6: dependent sums and products along maps of presheaves satisfy Beck–Chevalley, and colimits of presheaves are universal, so $H$ and its chain commute with pullback along every $\mathcal S' \to \mathcal S$. Adámek's argument and Lemma 6.1 are unchanged, and initiality gives a section for every map $M \to T$. Corollary O holds, its function extensionality being that of set theory.
- **Not claimed.** Corollary F, whose setting (StrictDisplayMahlo.md) is simplicial. Reading IR/Indexed in presheaves uses the presheaf counterpart of T1, as the simplicial reading uses T1.

So a presheaf topos on a category in $V_\kappa$, for $\kappa$ strongly Mahlo with an inaccessible above it, has one family for all schemes of indexed polynomial induction–recursion, with decoding and induction as equalities of maps, stable under substitution. Kubánek (MSc thesis, Chalmers 2025) writes that "there is currently no presheaf model for induction-recursion and in order to prove normalization of Mahlo by gluing one would be needed". Gluing for normalization works over presheaves on a category of renamings, which is countable and so lies in $V_\kappa$. His metatheory states induction–recursion in Dybjer–Setzer's general indexed form. Those codes are schemes of these codes ([IR/Description/Indexed](../IR/Description/Indexed.agda)), and their formation, introduction, decoding and elimination rules follow from the universal family with no extensionality, every identification built from refl by induction on the code ([IR/Indexed/General](../IR/Indexed/General.agda)). In presheaves each such identity is an equality of maps; for the simplicial reading the argument of UniversalIR.md's Lemma 7.1 applies to them (on paper). His reducibility predicate itself is checked as an instance ([IR/Indexed/General/Reducibility](../IR/Indexed/General/Reducibility.agda)): its decoding clauses and the computation equations of its eliminator hold by refl. No novelty claim is made.
