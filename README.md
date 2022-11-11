# complete integral domains

Let's call a ring *complete*, if we can equip it with a total order that is both translation invariant and compatible with the ring multiplication, such that some completeness property (*i.e.*, similar to the completeness of the field of the real numbers) is satisfied.

The goal here is to prove that under a mild completeness hypothesis (namely, that any bounded increasing sequence converges, see https://en.wikipedia.org/wiki/Completeness_of_the_real_numbers#Monotone_convergence_theorem), the only complete integral domains are (up to isomorphism) $\mathbb{Z}$ and $\mathbb{R}$.

## axioms

Let $R$ be a set, equipped with two binary operators $+$ and $\times$, a unary operator $-$, and a binary relation $\lt$. Two elements of $R$ are distinguished, and denoted by $0$ and $1$.

We assume that the following fifteen axioms are satisfied, where $x$, $y$ and $z$ are arbitrary elements of $R$:

$$\begin{aligned}
(R_1)&: x \not\lt x\\
(R_2)&: (x < y\wedge y < z) \Rightarrow x < z\\
(R_3)&: x < 0 ∨ 0 = x ∨ 0 < x\\
(R_4)&: x < y \Rightarrow x + z < y + z\\
(R_5)&: (0 < x \wedge 0 < y) \Rightarrow 0 < x y\\
(R_6)&: 0 + x = x\\
(R_7)&: 0x = 0\\
(R_8)&: 1x = x\\
(R_9)&: x + y = y + x\\
(R_{10})&: xy = yx\\
(R_{11})&: (x + y) + z = x + (y + z)\\
(R_{12})&: (x y) z = x (y z)\\
(R_{13})&: x (y + z) = x  y + x  z\\
(R_{14})&: x + (-x) = 0\\
(R_{15})&: \forall u: \mathbb{N} \rightarrow R,\ (\forall n\in \mathbb{N},\ u_n < u_{n + 1}) \wedge (\exists A\in R,\ \forall n\in \mathbb{N},\ u_n < A) \Rightarrow (\exists L\in R,\ \forall \varepsilon\gt 0,\ \exists N\in\mathbb{N}, \forall n > N,\ L + (-\varepsilon) \lt u_n \lt L + \varepsilon)
\end{aligned}$$

Axioms $(R_6)$ to $(R_{14})$ are standard for a (commutative) ring with unity, while axioms $(R_1)$ to $(R_5)$ ensure that $R$ is an *ordered* ring and, by $(R_5)$, an *integral domain*, as long as $0\neq 1$.

As it's stated using $\lt$ instead of $\le$, axiom $(R_{15})$ is weaker than the more usual *monotone convergence theorem/axiom*, but is enough for our goals, provided $(H')$ is true (see below).

If $0=1$, then $R$ is a zero ring: all elements are equal to $0$ by $(R_7)$ and $(R_8)$. This is checked using ``lean`` in the file ``case1_singleton.lean``.

If $0\neq 1$, then $0\lt 1$; this is checked in ``base.lean``.

If $(H)$ there is no element of $R$ in the interval $(0,1)$, then $R$ is isomorphic to $\mathbb{Z}$. This is checked in ``case2_integers.lean``,where we take $(H)$ as an additional axiom.

If $(H')$ there is at least one element of $R$ between $0$ and $1$, then $(R,+,\times,0,1,\lt)$ is isomorphic to the field $\mathbb{R}$ of the real numbers. In particular, $R$ is a field. This is checked in ``case3_reals.lean``, where we take $(H')$ as an additional axiom.

## lean version

We use ``lean`` version 3 with ``propext`` and some *classical* extensions (``classical.choice``, ``quot.sound``).

``mathlib`` isn't used, and this drastically reduces the available tactics.

## motivation

My goal was to confirm that the set of axioms $(R_1)$-$(R_{15})$, together with $(H')$, could be used as a feasible foundation for proving the major results in first or second year algebra and analysis, in particular to define the usual functions and constants, the integral, some complex analysis, and prove the fundamental theorem of algebra.

Working with axioms can be tricky, as corner cases are easily overlooked. Hence the choice of a theorem prover for the first steps; the remaining steps are done, but aren't checked with ``lean`` (yet?).

During my exploration of axioms $(R_1)$-$(R_{15})$, I noticed that with $(H')$ false, $R$ would be equal to $\mathbb{Z}$, and I added that.

I don't know of any reference, and didn't try to find some. Everything was built on snippets of memory, "white-room" like. The reference given at the start of ``case2_integers.lean`` was found later, while searching for a way to remove $(R_{15})$ in the $(H)$ case.




