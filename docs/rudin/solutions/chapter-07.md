<a id="chapter-07"></a>

# Chapter 7 — Sequences and Series of Functions

[All chapters](../solutions.md) · [Previous chapter](chapter-06.md) · [Next chapter](chapter-08.md)

**Exercises:** [1](#r07e01) · [2](#r07e02) · [3](#r07e03) · [4](#r07e04) · [5](#r07e05) · [6](#r07e06) · [7](#r07e07) · [8](#r07e08) · [9](#r07e09) · [10](#r07e10) · [11](#r07e11) · [12](#r07e12) · [13](#r07e13) · [14](#r07e14) · [15](#r07e15) · [16](#r07e16) · [17](#r07e17) · [18](#r07e18) · [19](#r07e19) · [20](#r07e20) · [21](#r07e21) · [22](#r07e22) · [23](#r07e23) · [24](#r07e24) · [25](#r07e25) · [26](#r07e26)

Positive series indices below correspond to Lean indices shifted by one where indicated in the source.

<a id="r07e01"></a>
### 7.1 — A common bound for a uniformly convergent sequence
**Lean source:** [Exercise01.lean](../../../Math/Rudin/Chapter07/Exercise01.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $E$ be any subset of a set $X$, and let $f_n:X\to V$, where $V$ is a normed additive commutative group. Suppose $f_n\to f$ uniformly on $E$ and, for each $n$, there is a real number $M_n$ such that $\|f_n(x)\|\le M_n$ for every $x\in E$. Then there is one real number $M$ such that $\|f_n(x)\|\le M$ for all $n$ and $x\in E$. This includes real and complex functions and the empty domain.

**Proof.** Choose $N$ such that $\|f_n(x)-f(x)\|<1$ whenever $n\ge N$ and $x\in E$. Taking $n=N$ gives $\|f(x)\|\le M_N+1$, hence $\|f_n(x)\|\le M_N+2$ for $n\ge N$. For the finitely many earlier indices, use their individual bounds. With indices starting at zero, the single choice

$$
M=2+|M_N|+\sum_{i<N}|M_i|
$$

works in both cases. If $E$ is empty, all the required inequalities are vacuous.

**Lean declarations:** `exercise01_uniform_bound`.

<a id="r07e02"></a>
### 7.2 — Uniform limits of sums and products
**Lean source:** [Exercise02.lean](../../../Math/Rudin/Chapter07/Exercise02.lean).
**Inventory status:** Verified as stated.

**Statement.** If $f_n\to f$ and $g_n\to g$ uniformly on an arbitrary set $E$, with values in a normed additive commutative group, then $f_n+g_n\to f+g$ uniformly on $E$. If the values lie in a normed ring and each $f_n$ and $g_n$ is bounded on $E$, then $f_ng_n\to fg$ uniformly there. The product result includes real and complex functions; the ring need not be commutative.

**Proof.** The sum estimate is

$$
\|(f+g)-(f_n+g_n)\|\le \|f-f_n\|+\|g-g_n\|.
$$

Make both terms less than $\varepsilon/2$, uniformly on $E$.

For products, Exercise 7.1 gives nonnegative common bounds $A$ and $B$ for $\|f_n\|$ and $\|g_n\|$. Pointwise passage to the limit gives $\|g\|\le B$. The identity

$$
fg-f_ng_n=(f-f_n)g+f_n(g-g_n)
$$

yields

$$
\|fg-f_ng_n\|\le B\|f-f_n\|+A\|g-g_n\|.
$$

Make both errors less than $\delta=\varepsilon/(A+B+1)$. The last expression is at most $(A+B)\delta<\varepsilon$. No initial common bound was assumed.

**Lean declarations:** `exercise02_sums`, `exercise02_products`.

<a id="r07e03"></a>
### 7.3 — Products can fail to converge uniformly
**Lean source:** [Exercise03.lean](../../../Math/Rudin/Chapter07/Exercise03.lean).
**Inventory status:** Verified as stated.

**Statement.** On $\mathbb R$, set $f_n(x)=x$ and $g_n(x)=1/(n+1)$ for $n\ge0$. Both sequences converge uniformly, respectively to $x$ and $0$. Their product converges pointwise to zero but has no uniform limit on $\mathbb R$.

**Proof.** The first sequence is constant in $n$. The error for the second is $1/(n+1)$, independent of $x$, and tends to zero. At any fixed $x$, the product $x/(n+1)$ tends to zero. However, at $x=n+1$ the product equals $1$, so its error cannot eventually be less than $1/2$ everywhere. Any uniform limit would also be a pointwise limit and would therefore equal zero. Thus no alternative uniform limit exists.

**Lean declarations:** `exercise03_unbounded_product_example`, `exercise03_first_uniform`, `exercise03_second_uniform`, `exercise03_pointwise`, `exercise03_not_uniform`, `exercise03_no_uniform_limit`.

<a id="r07e04"></a>
### 7.4 — A positive series near a singular parameter
**Lean source:** [Exercise04.lean](../../../Math/Rudin/Chapter07/Exercise04.lean).
**Inventory status:** Verified as stated.

**Statement.** For real $x$, consider

$$
S_N(x)=\sum_{n=1}^{N}\frac1{1+n^2x^2}.
$$

The series converges absolutely exactly when $x\ne0$; write its sum as $S(x)$ on that domain. Its partial sums have a uniform limit on a set $E\subseteq\mathbb R$ if and only if

$$
\text{there is }\delta>0\text{ such that }|x|\ge\delta\quad(x\in E).
$$

When this holds, the limit is $S$ on $E$. Consequently, this criterion classifies every interval: the empty interval is allowed, a singleton works exactly when its point is nonzero, and any interval containing or approaching zero fails. The sum is continuous throughout $\mathbb R\setminus\{0\}$ and is unbounded above on that domain.

**Proof.** For $|x|\ge\delta>0$,

$$
0\le\frac1{1+n^2x^2}\le\frac1{\delta^2n^2}.
$$

The convergent reciprocal-square series gives absolute convergence at every nonzero point and uniform convergence on every such $E$ by the Weierstrass test. At zero, $S_N(0)=N$, so there is no finite limit.

Conversely, suppose the partial sums converge uniformly on $E$. Their uniform Cauchy condition, with error $1/2$, gives an index $N$ for which

$$
|S_{N+1}(x)-S_N(x)|<\frac12\qquad(x\in E).
$$

If $(N+1)|x|\le1$, the left side is $1/(1+(N+1)^2x^2)\ge1/2$, a contradiction. Thus $E$ is bounded away from zero. In particular, failure is equivalent to the condition that, for every $\delta>0$, some $x\in E$ has $|x|<\delta$. This also handles empty sets and degenerate intervals without exceptions.

Each term is continuous because its denominator is positive. Near any nonzero $x_0$, restrict to the open neighborhood $|x|>|x_0|/2$; convergence there is uniform. The uniform-limit theorem gives continuity at $x_0$.

Finally, at $x=1/(N+1)$ each of the first $N$ terms is at least $1/2$. Hence

$$
S\left(\frac1{N+1}\right)\ge\frac N2.
$$

Choosing $N>2M$ gives a nonzero point with $S(x)>M$, for any prescribed real $M$.

**Scope.** The Lean expression for the infinite sum is defined at every real number, but it represents the series sum only at nonzero arguments. No value at zero is used to claim convergence or continuity there.

**Lean declarations:** `exercise04_absolute_domain`, `exercise04_pointwise`, `exercise04_zero_partialSum`, `exercise04_zero_diverges`, `exercise04_uniform_iff`, `exercise04_uniform_intervals`, `exercise04_no_uniform_limit_iff`, `exercise04_uniform_empty`, `exercise04_uniform_singleton_iff`, `exercise04_continuousAt`, `exercise04_continuity`, `exercise04_large_value`, `exercise04_unbounded`.

<a id="r07e05"></a>
### 7.5 — Shrinking supports and failure of uniform convergence
**Lean source:** [Exercise05.lean](../../../Math/Rudin/Chapter07/Exercise05.lean).
**Inventory status:** Verified as stated.

**Statement.** For $n\ge1$, define on $\mathbb R$

$$
f_n(x)=
\begin{cases}
\sin^2(\pi/x),&1/(n+1)\le x\le1/n,\\
0,&\text{otherwise}.
\end{cases}
$$

Both support endpoints are included. Each $f_n$ is continuous, and $f_n(x)\to0$ at every real point. The limit is continuous, but the sequence has no uniform limit on $\mathbb R$. The series $\sum_{n\ge1}f_n(x)$ converges absolutely at every real $x$, while its ordered partial sums have no uniform limit on $\mathbb R$.

**Proof.** At each support endpoint, $\pi/x$ is an integer multiple of $\pi$, so the interior expression is zero. It therefore joins continuously to the zero function outside the support. In particular, $f_n(0)=0$.

If $x\le0$, every term vanishes. If $x>0$, then eventually $1/n<x$, so every sufficiently late term vanishes. Thus the sequence tends pointwise to the continuous zero function, and each numerical series has only finitely many nonzero terms. This proves absolute convergence as well as ordinary partial-sum convergence.

For every $n\ge1$, the point $x_n=1/(n+1/2)$ lies inside the support and satisfies

$$
f_n(x_n)=\sin^2\bigl((n+1/2)\pi\bigr)=1.
$$

Therefore $f_n$ does not tend uniformly to zero. Pointwise uniqueness excludes any other uniform limit. If the series partial sums were uniformly convergent, their consecutive differences $f_n$ would tend uniformly to zero by the uniform Cauchy condition. The same peak values contradict this, regardless of the proposed limit of the partial sums.

**Lean declarations:** `exercise05_endpoints`, `exercise05_term_continuous`, `exercise05_pointwise_limit`, `exercise05_limit_continuity`, `exercise05_sequence_not_uniform`, `exercise05_sequence_no_uniform_limit`, `exercise05_series_absolute`, `exercise05_series_pointwise`, `exercise05_series_no_uniform_limit`, `exercise05_series_not_uniform`.

<a id="r07e06"></a>
### 7.6 — Locally uniform but nowhere absolute convergence
**Lean source:** [Exercise06.lean](../../../Math/Rudin/Chapter07/Exercise06.lean).
**Inventory status:** Verified as stated.

**Statement.** The real series

$$
\sum_{n=1}^{\infty}(-1)^n\frac{x^2+n}{n^2}
$$

converges in its displayed order at every $x\in\mathbb R$, uniformly on every bounded subset of $\mathbb R$. This includes all bounded intervals, empty or degenerate. It converges absolutely at no real point.

**Proof.** Split each term as

$$
(-1)^n\frac{x^2+n}{n^2}=x^2\frac{(-1)^n}{n^2}+\frac{(-1)^n}{n}.
$$

The first coefficient series is absolutely convergent; call its sum $A$. The second has an ordinary ordered limit $b$ by the alternating-series test. On $|x|\le R$, the first subseries has the summable uniform majorant $R^2/n^2$. The second is constant as a function of $x$, so its numerical convergence is uniform on any domain. Adding their partial sums proves uniform convergence to the same function $Ax^2+b$ on every bounded set. Singleton sets give pointwise convergence.

For every real $x$,

$$
\left|(-1)^n\frac{x^2+n}{n^2}\right|=\frac{x^2+n}{n^2}\ge\frac1n.
$$

The harmonic series diverges, so the nonnegative absolute partial sums have no finite limit.

**Scope.** Convergence of the alternating harmonic part means convergence in the natural order, not unconditional summability. The file does not assert uniform convergence on the whole real line.

**Lean declarations:** `exercise06_harmonic_converges`, `exercise06_uniform_on_bounded_sets`, `exercise06_local_uniform`, `exercise06_pointwise`, `exercise06_nowhere_absolute`.

<a id="r07e07"></a>
### 7.7 — Uniform convergence does not preserve derivative limits
**Lean source:** [Exercise07.lean](../../../Math/Rudin/Chapter07/Exercise07.lean).
**Inventory status:** Verified as stated.

**Statement.** For $n\ge1$ and $x\in\mathbb R$, let

$$
f_n(x)=\frac{x}{1+nx^2}.
$$

Then $f_n\to f=0$ uniformly on all of $\mathbb R$. Every $f_n$ is differentiable, with

$$
f_n'(x)=\frac{1-nx^2}{(1+nx^2)^2}.
$$

For $x\ne0$, $f_n'(x)\to0=f'(x)$. At zero, every $f_n'(0)=1$, whereas $f'(0)=0$.

**Proof.** The quotient rule applies since $1+nx^2>0$. To bound the functions, use $(\sqrt n\,|x|-1)^2\ge0$, which implies $\sqrt n\,|x|\le1+nx^2$. Thus

$$
|f_n(x)|\le\frac1{\sqrt n}
$$

for all real $x$, proving global uniform convergence. Also $|1-nx^2|\le1+nx^2$, so

$$
|f_n'(x)|\le\frac1{1+nx^2}.
$$

For a fixed nonzero $x$ the right side tends to zero. At $x=0$, direct substitution gives $f_n'(0)=1$ for every $n$. The constant limit function has derivative zero everywhere, establishing both the agreement off zero and the failure at zero.

**Lean declarations:** `exercise07_hasDerivAt`, `exercise07_norm_bound`, `exercise07_uniform_limit`, `exercise07_derivative_nonzero`, `exercise07_derivative_zero`.

<a id="r07e08"></a>
### 7.8 — An absolutely convergent series of step functions
**Lean source:** [Exercise08.lean](../../../Math/Rudin/Chapter07/Exercise08.lean).
**Inventory status:** Verified as stated.

**Statement.** Put $I(t)=0$ for $t\le0$ and $I(t)=1$ for $t>0$. Let $p_n$ be distinct points of $(a,b)$, and let $c_n$ be complex coefficients, or vectors in a complete real normed space, such that the ordinary partial sums of $\sum_n\|c_n\|$ have a finite limit. Then

$$
F(x)=\sum_n I(x-p_n)c_n
$$

is a uniformly convergent series on $[a,b]$, in fact on all of $\mathbb R$. It is continuous at every $x\in[a,b]$ unequal to all $p_n$, including endpoints and accumulation points of the jumps.

**Proof.** The $n$th term is $c_n$ when $p_n<x$ and zero otherwise, including when $x=p_n$. Its norm is at most $\|c_n\|$. The Weierstrass test in a complete normed space proves global uniform convergence. Nonnegativity of $\|c_n\|$ identifies its ordinary finite-sum convergence with the summability needed in that test.

Fix $x\ne p_n$ for every $n$. Each individual step function is constant on some neighborhood of $x$, hence continuous at $x$. Every finite partial sum is therefore continuous there. To prove continuity of $F$, approximate it uniformly within $\varepsilon/3$ by one such partial sum, then use continuity of that partial sum to control its change by $\varepsilon/3$. The triangle inequality controls the change in $F$ by $\varepsilon$. No common neighborhood for infinitely many terms is needed, so accumulation points cause no difficulty. This is continuity in the whole real line, not only relative continuity at the endpoints.

**Scope.** The global uniform-convergence theorem permits arbitrary jump points; distinctness and membership in $(a,b)$ are retained in the source-form statements. The piecewise formulation also works in any complete normed additive commutative group, without scalar multiplication.

**Lean declarations:** `exercise08_step_zero`, `exercise08_source_term`, `exercise08_uniform_global`, `exercise08_uniform_series`, `exercise08_continuity_off_jumps`.

<a id="r07e09"></a>
### 7.9 — Limits along moving points and a false converse
**Lean source:** [Exercise09.lean](../../../Math/Rudin/Chapter07/Exercise09.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $E$ be a subset of a metric space $X$, and let $f_n:X\to Y$ take values in a metric space $Y$. Suppose each $f_n$ is continuous on $E$ and $f_n\to f$ uniformly on $E$. If $x_n\in E$ and $x_n\to x\in E$, then $f_n(x_n)\to f(x)$. The converse fails even for continuous real functions on $\mathbb R$.

**Proof.** The uniform-limit theorem makes $f$ continuous on $E$, so $f(x_n)\to f(x)$. Moreover,

$$
d\bigl(f_n(x_n),f(x)\bigr)
\le d\bigl(f_n(x_n),f(x_n)\bigr)+d\bigl(f(x_n),f(x)\bigr).
$$

The first term tends to zero by uniform convergence and the second by relative continuity.

For the converse, take $f_n(t)=t/(n+1)$ on $\mathbb R$. Each is continuous. For any convergent real sequence $x_n\to x$, the sequence $x_n$ is bounded, so $x_n/(n+1)\to0$. Thus every required moving-point limit holds with $f=0$. But $f_n(n+1)=1$, which excludes uniform convergence to zero.

**Lean declarations:** `exercise09_moving_points`, `exercise09_counterexample_continuous`, `exercise09_counterexample_moving`, `exercise09_converse`.

<a id="r07e10"></a>
### 7.10 — A series with exactly the rational discontinuities
**Lean source:** [Exercise10.lean](../../../Math/Rudin/Chapter07/Exercise10.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $\{t\}=t-\lfloor t\rfloor$ and define the real function

$$
F(x)=\sum_{n=1}^{\infty}\frac{\{nx\}}{n^2}.
$$

The series converges uniformly on $\mathbb R$. Its discontinuities are exactly the rational numbers, including zero and negative rationals. They form a countable dense set. For every $a\le b$, $F$ has a Riemann integral on $[a,b]$, equal to its interval Lebesgue integral.

**Proof.** Since $0\le\{nx\}<1$, the summable majorant $1/n^2$ proves uniform convergence and the bound $|F(x)|\le\sum_{n\ge1}1/n^2$. If $x$ is irrational, $nx$ is not an integer for any positive integer $n$. Every summand is continuous at $x$, and uniform convergence gives continuity there.

For any real $x$, define

$$
L_n(x)=\begin{cases}
1/n^2,&nx\in\mathbb Z,\\
\{nx\}/n^2,&nx\notin\mathbb Z.
\end{cases}
$$

This is the left limit of the $n$th summand at $x$. The same majorant permits passage of the left limit through the sum, giving

$$
\lim_{y\uparrow x}F(y)=\sum_{n\ge1}L_n(x).
$$

For a rational $x=p/q$, with $q\ge1$, each $L_n(x)$ is at least the corresponding summand of $F(x)$, and the inequality is strict for $n=q$: the values are $1/q^2$ and $0$. Both series converge, so the left limit is strictly greater than $F(x)$. Thus $F$ is discontinuous at every rational point.

Countability and density now follow from those properties of $\mathbb Q$. On any closed bounded interval, $F$ is bounded and its discontinuity set has measure zero. The Lebesgue criterion for Riemann integrability gives an actual Darboux integral, and the Riemann–Lebesgue agreement theorem identifies its value with the interval integral. When $a=b$, that integral is zero.

**Lean declarations:** `fractionalSeries_uniform`, `fractionalSeries_continuousAt`, `fractionalSeries_leftLimit`, `fractionalSeries_not_continuousAt_rat`, `exercise10_discontinuities`, `exercise10_countability`, `exercise10_density`, `exercise10_riemann_integrability`.

<a id="r07e11"></a>
### 7.11 — The uniform Dirichlet test
**Lean source:** [Exercise11.lean](../../../Math/Rudin/Chapter07/Exercise11.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $E\subseteq X$, let $f_n:X\to V$ take values in a complete real normed space, and let $g_n:X\to\mathbb R$. Assume that there is a real bound $B$ such that

$$
\left\|\sum_{i=0}^{N-1}f_i(x)\right\|\le B
\quad\text{for every }N\text{ and }x\in E,
$$

that $g_n\to0$ uniformly on $E$, and that $g_n(x)$ is nonincreasing in $n$ at each $x\in E$. Then the ordered partial sums of $\sum_{n\ge0}g_n(x)f_n(x)$ converge uniformly on $E$. In particular, $V$ may be $\mathbb C$; the multipliers $g_n$ remain real.

**Proof.** Replace $B$ by $\max(B,0)$. Since each decreasing numerical sequence $g_n(x)$ has limit zero, all its terms are nonnegative. Write $A_N(x)=\sum_{i<N}f_i(x)$. For $m<n$, summation by parts gives

$$
\sum_{i=m}^{n-1}g_i f_i
=g_{n-1}A_n-g_mA_m
+\sum_{i=m}^{n-2}(g_i-g_{i+1})A_{i+1}.
$$

The triangle inequality, $\|A_j\|\le B$, and monotonicity give

$$
\left\|\sum_{i=m}^{n-1}g_i(x)f_i(x)\right\|
\le B\left(g_{n-1}(x)+g_m(x)+\sum_{i=m}^{n-2}(g_i(x)-g_{i+1}(x))\right)
=2B g_m(x).
$$

For a prescribed $\varepsilon>0$, uniform convergence of $g_m$ makes $g_m(x)<\varepsilon/[2(B+1)]$ for all sufficiently large $m$ and all $x\in E$. The tail estimate then gives the uniform Cauchy condition. Completeness yields the pointwise limits, and the uniform Cauchy condition makes convergence to them uniform. An empty $E$ imposes no condition on the chosen limit outside $E$.

**Scope.** The three source conditions are hypotheses. No convergence of $\sum f_n$ is assumed, and the conclusion concerns ordered convergence, not absolute or unconditional summability.

**Lean declarations:** `exercise11_tail_bound`, `exercise11_uniform_dirichlet_bound`, `exercise11_uniform_dirichlet`.

<a id="r07e12"></a>
### 7.12 — Convergence of dominated improper Riemann integrals
**Lean source:** [Exercise12.lean](../../../Math/Rudin/Chapter07/Exercise12.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $g:(0,\infty)\to\mathbb R$ and let $f_n:(0,\infty)\to\mathbb R$, or $f_n:(0,\infty)\to\mathbb C$. Suppose $g$ and every $f_n$ are Riemann integrable on each $[a,b]$ with $0<a<b$, that

$$
|f_n(x)|\le g(x)\qquad(n\ge0,\ x>0),
$$

and that $f_n\to f$ uniformly on every compact subset of $(0,\infty)$. In the complex case, $|\cdot|$ denotes the complex norm. Suppose also that the improper Riemann integral of $g$ is finite. Then $f$ is locally Riemann integrable, the improper integrals of every $f_n$ and of $f$ converge absolutely, and

$$
\lim_{n\to\infty}\int_0^\infty f_n(x)\,dx
=\int_0^\infty f(x)\,dx.
$$

Here an improper integral is the sum of two separate limits,

$$
\lim_{a\downarrow0}\int_a^1 h(x)\,dx
+\lim_{b\to\infty}\int_1^b h(x)\,dx,
$$

not a limit in which the two endpoints are coupled. Integrability on singleton intervals is automatic.

**Proof.** Uniform convergence on singleton compact sets gives pointwise convergence. The domination hypothesis implies $g\ge0$ and, on taking limits, $|f|\le g$.

First consider real functions. Local Riemann integrability implies measurability on the positive ray: use the countable cover $[1/(k+1),k+1]$. A nonnegative locally integrable function with finite improper endpoint limits is Lebesgue integrable on $(0,\infty)$. Indeed, its integrals on the increasing truncated intervals are bounded by the two endpoint limits; monotone convergence identifies their finite supremum with its integral on the whole ray. Thus $g$ is integrable. Measurability and domination give absolute Lebesgue integrability of each $f_n$ and of its pointwise limit $f$. The dominated convergence theorem gives convergence of their integrals.

It remains to retain the Riemann conclusions rather than merely Lebesgue conclusions. Fix $0<a\le b$. The approximating functions have proper Riemann integrals and converge uniformly on $[a,b]$. Their integral values converge to the integral of $f$, by dominated convergence on that interval. For any tagged partition, replacing $f$ by a uniformly close $f_n$ changes its tagged sum by at most

$$
(b-a)\sup_{[a,b]}|f-f_n|.
$$

Choose $n$ so that this error and the difference of integral values are each less than $\varepsilon/3$, and choose a partition controlling the tagged sums for $f_n$ within $\varepsilon/3$. The triangle inequality proves proper Riemann integrability of $f$. Absolute values of locally Riemann integrable real functions are again locally Riemann integrable. Absolute Lebesgue integrability, together with these proper Riemann witnesses, then gives both endpoint limits for $f_n$, $f$, $|f_n|$, and $|f|$. Their improper values equal their Lebesgue integrals, so the already proved integral limit is the required improper Riemann limit.

For complex functions, apply the real argument to the real and imaginary parts. Each is bounded in absolute value by $|f_n|\le g$, and each inherits compact uniform convergence. Combining their proper tagged integrals proves proper complex Riemann integrability of the limit. The norm of a locally complex Riemann integrable function is locally real Riemann integrable. Domination gives absolute integrability of the norms; the separate complex endpoint limits follow from integrability. Finally, dominated convergence for the complex integral proves the displayed limit.

**Scope.** Both the real and complex statements are present. Measurability, absolute integrability, and proper Riemann integrability of the limit are derived, not extra hypotheses.

**Lean declarations:** `exercise12_bridges`, `exercise12_improper_existence`, `exercise12_integral_limit`, `exercise12_complex`.

<a id="r07e13"></a>
### 7.13 — Selection for bounded monotone functions
**Lean source:** [Exercise13.lean](../../../Math/Rudin/Chapter07/Exercise13.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $f_n:\mathbb R\to\mathbb R$ be nondecreasing in the real argument, with $0\le f_n(x)\le1$ for every $n,x$. There are strictly increasing indices $k_n$ and a nondecreasing function $g:\mathbb R\to[0,1]$ such that $f_{k_n}(x)\to g(x)$ at every real point, including every discontinuity of $g$. If $g$ is continuous, this convergence is uniform on every compact subset of $\mathbb R$.

More generally, any pointwise-convergent sequence of nondecreasing real functions with continuous limit converges locally uniformly; the bound $[0,1]$ is not needed for this last assertion.

**Proof.** The product $[0,1]^{\mathbb R}$ is compact by Tychonoff's theorem, so the sequence has a cluster point $g$ in the pointwise topology. The set of nondecreasing functions is closed in that topology: each inequality $h(x)\le h(y)$ for $x\le y$ is a closed condition. Hence $g$ is nondecreasing and takes values in $[0,1]$.

A monotone real function has at most countably many discontinuities. Let $D$ be their union with $\mathbb Q$. Restriction to $D$ is continuous, and the countable product of real lines is metrizable. The restricted cluster point is therefore the limit of a subsequence with strictly increasing indices $k_n$. This subsequence converges to $g$ at every point of $D$, including all its discontinuities.

At any other point $x$, $g$ is continuous. Choose rationals $p<x<q$ sufficiently near $x$ that $g(p)$ and $g(q)$ are as close to $g(x)$ as needed. Monotonicity gives

$$
f_{k_n}(p)\le f_{k_n}(x)\le f_{k_n}(q).
$$

Convergence at the rational endpoints and continuity of $g$ squeeze the middle term to $g(x)$. This establishes convergence on the whole line, not just at continuity points.

Finally, assume $g$ is continuous and write $h_n=f_{k_n}$. Given $x$ and $\varepsilon>0$, choose $l<x<r$ so close to $x$ that $g(l)$, $g(r)$, and every $g(y)$ for $l<y<r$ differ from $g(x)$ by less than $\varepsilon/3$. Pointwise convergence at $l,r$ eventually gives

$$
g(l)-\varepsilon/3<h_n(l)\le h_n(y)\le h_n(r)<g(r)+\varepsilon/3.
$$

It follows that $|h_n(y)-g(y)|<\varepsilon$ throughout $(l,r)$ for all sufficiently large $n$. This proves local uniform convergence. A finite subcover of any compact set gives one index valid everywhere on that set. This last argument applies to any such pointwise-convergent sequence and uses no monotonicity in the sequence index.

**Lean declarations:** `exercise13_helly_selection`, `exercise13_locally_uniform`, `exercise13_uniform_on_compact`, `exercise13`.

<a id="r07e14"></a>
### 7.14 — A continuous curve onto the square
**Lean source:** [Exercise14.lean](../../../Math/Rudin/Chapter07/Exercise14.lean).
**Inventory status:** Verified as stated.
**Statement.** Let $f:\mathbb R\to\mathbb R$ be continuous and $2$-periodic. Assume $0\le f\le1$ everywhere, $f=0$ on $[0,1/3]$, and $f=1$ on $[2/3,1]$. Define

$$
x(t)=\sum_{n=1}^{\infty}2^{-n}f(3^{2n-1}t),\qquad
y(t)=\sum_{n=1}^{\infty}2^{-n}f(3^{2n}t),\qquad \Phi(t)=(x(t),y(t)).
$$

Both series converge uniformly on $\mathbb R$, and $\Phi$ is continuous. If $C$ is the middle-thirds Cantor set, then

$$
\Phi(C)=\Phi([0,1])=[0,1]^2.
$$

**Proof.** Each summand is continuous and has absolute value at most $2^{-n}$. The Weierstrass majorant test gives uniform convergence and continuity. Nonnegativity and $\sum_{n\ge1}2^{-n}=1$ put both coordinates in $[0,1]$ for every real $t$.

Choose binary expansions

$$
u=\sum_{n\ge1}u_n2^{-n},\qquad v=\sum_{n\ge1}v_n2^{-n},\qquad u_n,v_n\in\{0,1\}.
$$

Interlace them by $a_{2n-1}=u_n$, $a_{2n}=v_n$, and set

$$
t=\sum_{j\ge1}\frac{2a_j}{3^{j+1}}.
$$

This ternary expansion has a leading zero and only zero-or-two digits, so $t\in C$. For every $j\ge1$, removing the first $j-1$ nonzero-position digits gives

$$
3^jt=2k+\sum_{r\ge0}\frac{2a_{j+r}}{3^{r+1}}\quad\text{for some integer }k\ge0.
$$

The tail belongs to $[0,1/3]$ if $a_j=0$, and to $[2/3,1]$ if $a_j=1$. Periodicity and the plateau conditions therefore give $f(3^jt)=a_j$. Substitution yields $x(t)=u$ and $y(t)=v$. Closed plateau intervals make this argument valid for endpoint values and either permitted binary expansion. Thus every point of the square has a preimage in $C\subset[0,1]$, proving both image equalities.

**Lean declarations:** `exercise14_continuity`, `exercise14_constructive_cantor`, `exercise14_cantor_surjection`, `exercise14_interval_surjection`.

<a id="r07e15"></a>
### 7.15 — Equicontinuity of positive dilations
**Lean source:** [Exercise15.lean](../../../Math/Rudin/Chapter07/Exercise15.lean).
**Inventory status:** Verified as stated.
**Statement.** For any $f:\mathbb R\to\mathbb R$, the family $t\mapsto f(nt)$, $n\ge1$, on $[0,1]$ is equicontinuous if and only if

$$
f(x)=f(0)\qquad(x\ge0).
$$

In particular, under the source assumption that $f$ is continuous on $\mathbb R$, this is the exact restriction. Constancy on the negative half-line does not follow.
**Proof.** Fix $x\ge0$ and $\varepsilon>0$. Equicontinuity at $0$ supplies $\delta>0$ such that $|f(nt)-f(0)|<\varepsilon$ for every positive integer $n$ and every $t\in[0,1]$ with $t<\delta$. Choose $n>x$ and $n>x/\delta$. Then $t=x/n$ is admissible, so $|f(x)-f(0)|<\varepsilon$. Since $\varepsilon$ is arbitrary, $f(x)=f(0)$. Conversely, this identity makes every dilation constant on $[0,1]$, which gives equicontinuity. The continuous function $f(x)=\min(x,0)$ satisfies the restriction but has $f(-1)=-1\ne0=f(0)$. The general equivalence does not require continuity; the continuous classification retains the source hypothesis explicitly.

**Lean declarations:** `exercise15_classification`, `exercise15_continuous_classification`, `exercise15_nonconstant_example`.

<a id="r07e16"></a>
### 7.16 — Pointwise convergence of an equicontinuous sequence
**Lean source:** [Exercise16.lean](../../../Math/Rudin/Chapter07/Exercise16.lean).
**Inventory status:** Verified as stated.
**Statement.** Let $K$ be compact and let $f_n:K\to Y$ be equicontinuous. If $f_n(x)\to g(x)$ at every $x\in K$, then $f_n\to g$ uniformly. The Lean result allows any compact topological domain and any uniform-space target, and also gives the restriction-to-a-compact-set formulation, including the empty set.
**Proof.** In a metric target, fix $\varepsilon>0$. Equicontinuity gives, for each $x\in K$, a neighborhood $U_x$ such that $d(f_n(y),f_n(x))<\varepsilon/4$ for all $n$ and $y\in U_x$. Taking pointwise limits gives $d(g(y),g(x))\le\varepsilon/4$. Choose finitely many of these neighborhoods covering $K$. Pointwise convergence at their centers supplies one $N$ such that the center errors are less than $\varepsilon/4$ for $n\ge N$. For $y$ in a chosen neighborhood, the triangle inequality now gives $d(f_n(y),g(y))<\varepsilon$. The uniform-space version is the standard compact-domain theorem that pointwise and uniform convergence agree on equicontinuous families; the same finite-cover proof uses entourages in place of metric balls. Apply it to the compact subspace for the set formulation. On an empty domain all convergence conditions are vacuous.

**Lean declarations:** `exercise16_uniform_convergence`, `exercise16_uniform_convergence_on`.

<a id="r07e17"></a>
### 7.17 — Metric and vector versions of convergence theorems
**Lean source:** [Exercise17.lean](../../../Math/Rudin/Chapter07/Exercise17.lean).
**Inventory status:** Verified as stated.
**Statement.** For maps $F_n:X\to Y$ into a metric space, uniform convergence to $f$ means

$$
\forall\varepsilon>0\ \exists N\ \forall n\ge N\ \forall x\in X,\quad d(F_n(x),f(x))<\varepsilon.
$$

For a family $F_i:X\to Y$ between metric spaces, the source's equicontinuity condition is the uniform condition

$$
\forall\varepsilon>0\ \exists\delta>0\ \forall x,y\in X\ \forall i,\quad d(x,y)<\delta\ \Longrightarrow\ d(F_i(x),F_i(y))<\varepsilon.
$$

The file proves the following nine extensions.

1. **Supremum criterion (7.9).** Set $s_n=\sup_{x\in X}d(F_n(x),f(x))$ in $[0,\infty]$, with $\sup\varnothing=0$. Then uniform convergence is equivalent to $s_n\to0$. Infinite early errors are permitted; a separate pointwise-convergence assumption is unnecessary.
2. **Continuity (7.12).** A uniform limit of continuous maps into any metric space is continuous. The domain can be any topological space.
3. **Cauchy criterion (7.8).** If $Y$ is complete, a uniform limit exists exactly when, for every $\varepsilon>0$, some $N$ satisfies $d(F_m(x),F_n(x))<\varepsilon$ for all $m,n\ge N$ and all $x$.
4. **Interchange of limits (7.11).** Suppose $Y$ is complete, $F_n\to f$ uniformly on $S$, $x$ is an accumulation point of $S$, and $F_n(t)\to A_n$ as $t\to x$ through $S\setminus\{x\}$. Then $A_n\to L$ for some $L$, and $f(t)\to L$ through the same set. The file also allows any nontrivial approach filter eventually contained in $S$.
5. **Majorant test (7.10).** In a complete normed additive group, if $\|F_n(x)\|\le M_n$ everywhere and the ordered real partial sums of $\sum M_n$ converge to a finite limit, then $\sum F_n$ converges uniformly to its pointwise sum.
6. **Integration (7.16).** Let $a\le b$, let $\alpha$ be nondecreasing on $[a,b]$, and let $F_n:[a,b]\to\mathbb R^k$ be Riemann–Stieltjes integrable with values $v_n=\int_a^bF_n\,d\alpha$. If $F_n\to f$ uniformly, then $f$ is integrable and $v_n\to\int_a^bf\,d\alpha$. Vector integration is coordinatewise. The integrator need not be continuous.
7. **Differentiation (7.17).** In any real Banach space, suppose $x_0\in[a,b]$, every $F_n$ has a derivative $D_n(x)$ relative to $[a,b]$ at each point of that interval, $F_n(x_0)\to v$, and $D_n\to g$ uniformly. Then $F_n$ converges uniformly on $[a,b]$ to a function $f$ with relative derivative $g$ at every point. For $a<b$ this includes one-sided endpoint derivatives. No continuity of $D_n$ is assumed.
8. **Equicontinuity (7.24).** A uniformly convergent sequence of continuous maps from a compact metric space into any metric space satisfies the uniform equicontinuity condition above.
9. **Selection and boundedness (7.25).** An equicontinuous, pointwise bounded sequence on a compact metric domain, with values in a proper metric space, has a uniformly convergent subsequence with continuous limit. A proper metric space is one whose closed bounded sets are compact. If the target is also a normed additive group, there is one $M$ with $\|F_n(x)\|\le M$ for all $n,x$. These assertions include every Euclidean vector target.

**Proof.** For the supremum criterion, uniform error less than $\varepsilon/2$ bounds $s_n$ by $\varepsilon/2$, while $s_n<\varepsilon$ bounds every pointwise error. This also handles empty domains and infinite initial suprema. For continuity, choose a continuous approximant with uniform error less than $\varepsilon/3$ and use its continuity at the chosen point; the triangle inequality gives continuity of the limit.

For the complete-target Cauchy criterion, the uniform Cauchy condition makes each $F_n(x)$ a Cauchy sequence. Completeness supplies $f(x)$. Pass to the pointwise limit in a uniform $\varepsilon/2$ bound to obtain a uniform error at most $\varepsilon/2<\varepsilon$. Conversely, compare two late terms with their uniform limit. For interchange of limits, the same Cauchy bound passes to the approach limit and gives $d(A_m,A_n)\le\varepsilon/2$ for late $m,n$. Hence $A_n\to L$. Fix a late $n$ and bound

$$
d(f(t),L)\le d(f(t),F_n(t))+d(F_n(t),A_n)+d(A_n,L).
$$

The first and third terms are uniformly small and the middle term tends to zero. A nontrivial approach filter ensures that passing bounds to limits is valid; accumulation supplies precisely this condition in the punctured-neighborhood case.

For the majorant test, if $X$ is nonempty the norm bound forces $M_n\ge0$. Convergence of its ordered partial sums then gives summability. The norm of each vector tail is at most the corresponding scalar tail, so completeness and the uniform Cauchy criterion apply. If $X$ is empty the conclusion is immediate.

For integration, write $D=\alpha(b)-\alpha(a)\ge0$. Actual tagged sums use tags in closed partition cells and the increments $\alpha(x_{i+1})-\alpha(x_i)$, not modified endpoint values. A uniform scalar error $|u-w|\le\delta$ gives

$$
|S(u)-S(w)|\le\delta D,\qquad\left|\int u\,d\alpha-\int w\,d\alpha\right|\le\delta D.
$$

Consequently the integrals of a uniformly convergent scalar sequence are Cauchy. Let their limit be $L$. The limit function is bounded because one approximant is bounded. Choose an approximant uniformly close to it and with integral close to $L$, then a partition whose every tagged refinement approximates that approximant's integral. The triangle inequality for these three errors proves that the limit function has integral $L$. Using tolerances with denominator $D+1$ includes $D=0$ and $a=b$. Apply this scalar argument to each of the finitely many coordinates; coordinatewise convergence is Euclidean convergence.

For differentiation, the mean-value estimate on the convex interval gives

$$
\|(F_m-F_n)(y)-(F_m-F_n)(x)\|\le\sup_{t\in[a,b]}\|D_m(t)-D_n(t)\|\,|y-x|.
$$

Here one can use any common derivative-error bound instead of the displayed supremum. Taking $x=x_0$ proves uniform Cauchy convergence of $F_n$, hence a uniform limit $f$. For fixed $x$, divide the same estimate by $|y-x|$ for $y\ne x$. The difference quotients of $F_n$ are uniformly Cauchy on $[a,b]\setminus\{x\}$, and their pointwise limit is the difference quotient of $f$. Interchange their uniform limit with $y\to x$ to obtain derivative $g(x)$. The argument is relative to the closed interval, so includes its endpoints. When $a=b$, the asserted within-derivative condition is vacuous, not a claim of a uniquely determined ordinary derivative.

For equicontinuity, the sequence together with its uniform limit is compact in the uniform topology. The compact-family result of Exercise 7.19 gives equicontinuity, and compactness of the domain makes it uniform. Finally, the closure of an equicontinuous pointwise bounded family in a proper target is compact by Arzelà–Ascoli, as in Exercise 7.19. Sequential compactness selects strictly increasing indices. In a normed target the compact closure is norm bounded, and point evaluation cannot increase the supremum norm; this gives the common bound.

**Lean declarations:** `exercise17_uniform`, `exercise17_equicontinuous`, `exercise17_uniform_iff`, `exercise17_equicontinuous_iff`, `exercise17_metric_sup_criterion`, `exercise17_metric_continuity`, `exercise17_complete_cauchy`, `exercise17_complete_limit_interchange_filter`, `exercise17_complete_limit_interchange`, `exercise17_vector_majorant`, `exercise17_stieltjes_uniform_limit`, `exercise17_hasVectorRSIntegral`, `exercise17_vector_integration`, `exercise17_vector_differentiation`, `exercise17_vector_equicontinuity`, `exercise17_vector_selection_bound`, `exercise17_vector_selection_subsequence`.

<a id="r07e18"></a>
### 7.18 — Compactness of bounded primitives
**Lean source:** [Exercise18.lean](../../../Math/Rudin/Chapter07/Exercise18.lean).
**Inventory status:** Verified as stated.
**Statement.** Let $a\le b$. Suppose $f_n$ are real- or complex-valued Riemann-integrable functions on $[a,b]$, and $|f_n(t)|\le M$ for all $n,t$, where $M\ge0$. Define

$$
F_n(x)=\int_a^x f_n(t)\,dt\qquad(a\le x\le b).
$$

There are strictly increasing indices $k_j$ and a continuous $G$ on $[a,b]$ such that $F_{k_j}\to G$ uniformly. The file constructs the primitive values from integrability on the full interval; it does not assume their existence separately in the final statement.
**Proof.** Splitting a Riemann integral shows existence of every primitive value and, for $x\le y$, gives $F_n(y)-F_n(x)=\int_x^y f_n$. The formal complex estimate bounds the real and imaginary integrals separately, giving the sufficient, though nonsharp, bound

$$
|F_n(y)-F_n(x)|\le2M|y-x|,\qquad |F_n(x)|\le2M(b-a).
$$

Thus the primitives are continuous, equicontinuous, and pointwise bounded on a compact interval. Arzelà–Ascoli gives compact closure in the uniform topology, and sequential compactness gives the required subsequence. Real Darboux-integrable inputs embed into the complex formulation by their zero imaginary component; taking real parts of the primitives and of the uniform limit returns the real result. All integrals here are genuine Riemann integrals. If $a=b$, every primitive is zero and the assertion still holds.

**Lean declarations:** `exercise18_complex_integral_bound`, `exercise18_primitive_lipschitz`, `exercise18_primitive_subsequence`, `exercise18_exists_primitive_subsequence`, `exercise18_real_primitive_subsequence`.

<a id="r07e19"></a>
### 7.19 — Compact subsets of a continuous-function space
**Lean source:** [Exercise19.lean](../../../Math/Rudin/Chapter07/Exercise19.lean).
**Inventory status:** Verified as stated.
**Statement.** Let $K$ be a compact metric space. A subset $S\subset C(K)$ is compact in the supremum metric if and only if it is closed in that metric, pointwise bounded, and equicontinuous. Both real and complex functions are included. More generally, the equivalence holds in $C(K,Y)$ for any proper metric target $Y$. Empty domains and empty families are allowed.
**Proof.** A compact subset of a metric space is closed. For each $x\in K$, evaluation $f\mapsto f(x)$ is continuous, so its image of a compact $S$ is compact and therefore bounded. To obtain equicontinuity, cover compact $S$ by finitely many uniform balls of radius $\varepsilon/3$. At a fixed $x$, continuity of their finitely many centers gives one neighborhood on which each center varies by less than $\varepsilon/3$. Every member of $S$ is within $\varepsilon/3$ of a center at both points, so its variation is less than $\varepsilon$. This proves necessity.

Conversely, properness makes the closure of each bounded evaluation image compact. Arzelà–Ascoli then says that an equicontinuous family with these pointwise compact closures has compact closure in the uniform topology on compact $K$. If $S$ is closed, its closure is $S$, giving sufficiency. This argument also proves the compact-closure assertion without assuming $S$ closed. Neither direction needs $S$ or $K$ to be nonempty.

**Lean declarations:** `exercise19_necessity_closed`, `exercise19_necessity_bounded`, `exercise19_necessity_equicontinuous`, `exercise19_compact_closure`, `exercise19_sufficiency`, `exercise19_ascoli_iff`.

<a id="r07e20"></a>
### 7.20 — A continuous function with zero moments
**Lean source:** [Exercise20.lean](../../../Math/Rudin/Chapter07/Exercise20.lean).
**Inventory status:** Verified as stated.
**Statement.** If $f$ is continuous on $[0,1]$ and

$$
\int_0^1 f(x)x^n\,dx=0\qquad(n=0,1,2,\ldots),
$$

then $f(x)=0$ for every $x\in[0,1]$. The statement holds for real and complex $f$, with the ordinary Riemann integral.
**Proof.** First take real $f$. Linearity gives $\int_0^1f(x)p(x)\,dx=0$ for every real polynomial $p$. Let $M\ge0$ bound $|f|$ on the interval. Given $\varepsilon>0$, Weierstrass approximation supplies $p$ with $|f-p|<\varepsilon/(M+1)$ everywhere. Hence

$$
\left|\int_0^1 f(x)^2\,dx\right|
=\left|\int_0^1 f(x)(f(x)-p(x))\,dx\right|
\le\frac{M\varepsilon}{M+1}\le\varepsilon.
$$

Thus $\int f^2=0$. A continuous nonnegative function on a nondegenerate compact interval with integral zero is identically zero: a positive value, even at an endpoint, would give a positive lower bound on a one-sided interval of positive length. Applying this to $f^2$ proves the conclusion at every point. The Lean argument identifies the continuous Riemann integrals with interval integrals before these estimates and returns to the Darboux formulation for the conclusion. For complex $f$, the moment conditions give zero moments for both $\operatorname{Re}f$ and $\operatorname{Im}f$. Applying the real result to each component gives $f=0$.

**Lean declarations:** `exercise20_polynomial_moments`, `exercise20_square_zero`, `exercise20_zero_moments`, `exercise20_zero_moments_complex`.

<a id="r07e21"></a>
### 7.21 — Complex polynomials are not dense on the circle
**Lean source:** [Exercise21.lean](../../../Math/Rudin/Chapter07/Exercise21.lean).
**Inventory status:** Verified as stated.
**Statement.** On $K=\{z\in\mathbb C:|z|=1\}$, let $A$ be the algebra of restrictions of complex polynomials in $z$ alone. Then $A$ separates points and vanishes at no point, but is not uniformly dense in $C(K,\mathbb C)$. Specifically, the continuous function $h(z)=\overline z$ satisfies

$$
\|p-h\|_\infty\ge1
$$

for every polynomial $p$, and the same lower bound holds for every function in the uniform closure of $A$.
**Proof.** The polynomial $p(z)=z$ separates any two distinct points; the constant polynomial $1$ is nonzero at every point. For an arbitrary polynomial $p$, consider $q(z)=zp(z)-1$. It is holomorphic on a neighborhood of the closed unit disk and $|q(0)|=1$. On its boundary, $z\overline z=1$ and $|z|=1$, so

$$
|q(z)|=|z(p(z)-\overline z)|=|p(z)-\overline z|.
$$

The maximum modulus principle yields $1\le\|p-h\|_\infty$. Since the norm-distance function is continuous, the closed set $\{g:\|g-h\|_\infty\ge1\}$ contains the entire closure of $A$. It does not contain $h$, whose distance from itself is zero. Thus $h$ lies outside that closure. This proof uses the maximum modulus principle rather than the source's suggested integral argument.

**Lean declarations:** `exercise21_mem_iff`, `exercise21_point_separation`, `exercise21_nonvanishing`, `exercise21_uniform_separation`, `exercise21_closure_separation`, `exercise21_not_dense`.

<a id="r07e22"></a>
### 7.22 — Polynomial approximation in Stieltjes mean square
**Lean source:** [Exercise22.lean](../../../Math/Rudin/Chapter07/Exercise22.lean).
**Inventory status:** Verified as stated.
**Statement.** Let $a\le b$, let $\alpha$ be nondecreasing on $[a,b]$, and let $f\in\mathcal R(\alpha)$ there. There are polynomials $p_n$, real for real $f$ and complex for complex $f$, such that the actual Riemann–Stieltjes integrals

$$
E_n=\int_a^b|f(x)-p_n(x)|^2\,d\alpha(x)
$$

exist, are nonnegative, and tend to zero. No continuity or right-continuity of $\alpha$, and no positive-mass condition, is imposed.
**Proof.** For real $f$ and $\varepsilon>0$, the continuous-approximation construction of Exercise 6.12 gives a continuous $g$ with

$$
A=\int_a^b(f-g)^2\,d\alpha<\varepsilon/4.
$$

That construction uses a partition with small Darboux gap and its continuous polygon interpolant, so it applies to the original Stieltjes increments even when $\alpha$ has jumps. Put $D=\alpha(b)-\alpha(a)\ge0$ and choose, by Weierstrass approximation, a real polynomial $p$ with

$$
\|g-p\|_\infty<\delta,\qquad \delta=\sqrt{\frac{\varepsilon}{4(D+1)}}.
$$

Continuous functions and polynomials are Stieltjes integrable. Closure of the integrable functions under subtraction and squaring gives all error integrals. Monotonicity of the integral gives

$$
B=\int_a^b(g-p)^2\,d\alpha\le\delta^2D\le\varepsilon/4.
$$

Since $(f-p)^2\le2(f-g)^2+2(g-p)^2$, the error $E$ for $p$ satisfies $0\le E\le2A+2B<\varepsilon$. Choose such a polynomial for $\varepsilon=1/(n+1)$; then $0\le E_n<1/(n+1)$ proves convergence. The denominator $D+1$ covers zero mass, including $a=b$.

For complex $f=u+iv$, apply the real construction to $u$ and $v$, producing real polynomials $p_n,q_n$. The complex polynomial $P_n=p_n+iq_n$ has

$$
|f-P_n|^2=(u-p_n)^2+(v-q_n)^2.
$$

Its error integral is the sum of the two nonnegative errors, hence tends to zero. The file states both tagged-refinement and Darboux versions of the real result; these use closed-cell tags and the unchanged endpoint values of $\alpha$.

**Lean declarations:** `exercise22_approximate_real`, `exercise22_polynomial_l2_real`, `exercise22_polynomial_l2_darboux`, `exercise22ComplexPolynomial_eval`, `exercise22_polynomial_l2_complex`.

<a id="r07e23"></a>
### 7.23 — An explicit polynomial approximation to absolute value
**Lean source:** [Exercise23.lean](../../../Math/Rudin/Chapter07/Exercise23.lean).
**Inventory status:** Verified as stated.
**Statement.** Define polynomials by

$$
P_0(x)=0,\qquad P_{n+1}(x)=P_n(x)+\frac{x^2-P_n(x)^2}{2}.
$$

For every integer $n\ge0$ and $|x|\le1$,

$$
0\le P_n(x)\le P_{n+1}(x)\le|x|,
$$

and

$$
|x|-P_n(x)\le |x|\left(1-\frac{|x|}{2}\right)^n<\frac2{n+1}.
$$

Consequently $P_n\to|x|$ uniformly on $[-1,1]$.
**Proof.** Write $u=|x|$. The recurrence gives the exact error identity

$$
u-P_{n+1}=(u-P_n)\left(1-\frac{u+P_n}{2}\right).
$$

Starting at $P_0=0$, suppose $0\le P_n\le u\le1$. Then $x^2-P_n^2\ge0$, so $P_{n+1}\ge P_n\ge0$. Both factors in the error identity are nonnegative, so $P_{n+1}\le u$. This proves the monotone bounds by induction. The second factor is at most $1-u/2$, so a second induction gives $u-P_n\le u(1-u/2)^n$.

Set $r=1-u/2$, so $0<r\le1$. Since $r^j\ge r^n$ for $0\le j\le n$,

$$
(n+1)r^n(1-r)\le(1-r)\sum_{j=0}^n r^j=1-r^{n+1}<1.
$$

Using $u=2(1-r)$ gives the strict bound $ur^n<2/(n+1)$. This remains strict when $u=0$, and includes $n=0$. The nonnegative error is bounded independently of $x$ by $2/(n+1)\to0$, proving uniform convergence, including both interval endpoints.

**Lean declarations:** `exercise23_zero`, `exercise23_succ`, `exercise23Value_succ`, `exercise23_error_identity`, `exercise23_monotone_bounds`, `exercise23_geometric_error`, `exercise23_strict_error`, `exercise23_error_bound`, `exercise23_uniform_absolute_value`.

<a id="r07e24"></a>
### 7.24 — Completion by distance-difference functions
**Lean source:** [Exercise24.lean](../../../Math/Rudin/Chapter07/Exercise24.lean).
**Inventory status:** Verified as stated.
**Statement.** Let $X$ be a metric space and fix $a\in X$. For $p\in X$, define the complex-valued function

$$
f_p(x)=d(x,p)-d(x,a).
$$

Then $f_p\in C_b(X,\mathbb C)$ and

$$
|f_p(x)|\le d(a,p),\qquad \|f_p-f_q\|_\infty=d(p,q).
$$

Let $Y$ be the closure of $\{f_p:p\in X\}$ in $C_b(X,\mathbb C)$. Then $Y$ is complete and $p\mapsto f_p$, with codomain restricted to $Y$, is an isometry with dense range. No separability assumption is needed.
**Proof.** The reverse triangle inequality gives $|d(x,p)-d(x,a)|\le d(a,p)$, and the distance functions are continuous. Thus $f_p$ is bounded and continuous. The same inequality gives

$$
|f_p(x)-f_q(x)|=|d(x,p)-d(x,q)|\le d(p,q).
$$

At $x=p$ equality holds. Hence the supremum norm of the difference is exactly $d(p,q)$, proving isometry and injectivity. The space of bounded continuous complex-valued functions is complete in the supremum norm. A closed subspace of a complete metric space is complete, so $Y$ is complete. Every $f_p$ belongs to $Y$, and its image is dense there by the definition of closure. Restricting the codomain leaves the metric equality unchanged. The chosen base point already entails that $X$ is nonempty.

**Lean declarations:** `exercise24_pointwise_bound`, `exercise24_continuous`, `exercise24Embedding_apply`, `exercise24_distance`, `exercise24_norm`, `exercise24_isometry`, `exercise24_completion_isometry`, `exercise24_dense_embedding`, `exercise24_completion`.

<a id="r07e25"></a>
### 7.25 — Euler polygons and their residuals
**Lean source:** [Exercise25.lean](../../../Math/Rudin/Chapter07/Exercise25.lean).
**Inventory status:** Verified as stated.
**Statement.** Let $\phi:[0,1]\times\mathbb R\to\mathbb R$ be continuous and bounded, let $c\in\mathbb R$, and choose $M\ge0$ such that $|\phi(t,z)|\le M$ throughout the closed strip. The source asks for a solution of $y'=\phi(t,y)$, $y(0)=c$, by the following construction. For each positive integer $N$, put

$$
t_i=i/N,\qquad z_0=c,\qquad z_{i+1}=z_i+N^{-1}\phi(t_i,z_i).
$$

Let $f_N$ interpolate these nodes affinely on each $[t_i,t_{i+1}]$. Define $\Delta_N(t)=f_N'(t)-\phi(t,f_N(t))$ off the mesh and $\Delta_N(t_i)=0$ at every mesh point, including $0$ and $1$.

The current file contains the polygon construction, its cell derivative formula, the residual integral identity in both interval-integral and Riemann forms, the bounds and Riemann integrability in part (a), equicontinuity in part (b), and the uniform residual limit in part (e):

$$
|f_N'|\le M\ \text{where the derivative exists},\qquad
|\Delta_N|\le2M,\qquad |f_N|\le |c|+M=:M_1,
$$

$$
|f_N(t)-f_N(s)|\le M|t-s|,\qquad
f_N(x)=c+\int_0^x[\phi(t,f_N(t))+\Delta_N(t)]\,dt,
\qquad \Delta_N\longrightarrow0\ \text{uniformly on }[0,1].
$$

There are strictly increasing indices $\sigma:\mathbb N\to\mathbb N$ for which $f_{\sigma(n)+1}\to f$ uniformly on $[0,1]$. The limit satisfies $|f|\le M_1$, the composed fields converge uniformly, and

$$
f(x)=c+\int_0^x\phi(t,f(t))\,dt,\qquad f(0)=c,\qquad f'(x)=\phi(x,f(x)).
$$

The derivatives are relative to $[0,1]$, hence one-sided at its endpoints. The composition-limit result itself allows any index map $\sigma$, provided the stated uniform polygon limit exists.

**Scope.** The file includes the subsequence selection and the resulting existence theorem, not only a theorem conditional on a uniform polygon limit. The shared construction permits values in a real normed vector space; the integral identity assumes completeness, and the compactness and uniform-limit arguments additionally assume a proper target. These assumptions hold for the real target of this exercise. No continuity or boundedness of the field outside the closed strip is required. No uniqueness of the differential-equation solution is asserted.

**Proof.** A formula for the polygon, extended constantly outside $[0,1]$, is

$$
f_N(t)=c+\sum_{i=0}^{N-1}\bigl(\min(t,t_{i+1})-\min(t,t_i)\bigr)\phi(t_i,z_i).
$$

The clipped affine factors are continuous, nonnegative, at most $1/N$, and sum to $t$ on $[0,1]$. At $t_i$, the preceding complete increments sum to $z_i-c$. Thus the formula gives $f_N(t_i)=z_i$ and, on the entire closed cell,

$$
f_N(t)=z_i+(t-t_i)\phi(t_i,z_i).
$$

In its open interior, $f_N'(t)=\phi(t_i,z_i)$. For $s\le t$, every clipped factor has a nonnegative increment, and their increments sum to $t-s$ on $[0,1]$. The triangle inequality therefore gives $|f_N(t)-f_N(s)|\le M(t-s)$. The same estimate holds on the whole real line for the constant extension because the sum of clipped increments is at most $t-s$. This proves equicontinuity and bounds every actual derivative, including a derivative at a mesh point if it exists. Comparing with $f_N(0)=c$ yields $|f_N(t)|\le|c|+Mt\le M_1$ on $[0,1]$.

Define a step velocity $v_N$ to equal $\phi(t_i,z_i)$ on $(t_i,t_{i+1}]$ and zero outside the union of these cells. Off the finite mesh, $\Delta_N=v_N-\phi(t,f_N(t))$, so $|\Delta_N|\le2M$; at the mesh it is zero. The composition $t\mapsto\phi(t,f_N(t))$ is continuous on the interval, and $v_N$ is locally constant off the mesh. Hence the bounded residual is continuous except possibly at finitely many points, and is Riemann integrable. The file explicitly identifies its Darboux integral with its interval integral. Integrating each step-velocity term gives its clipped affine factor, and therefore

$$
\int_0^x v_N(t)\,dt=f_N(x)-c.
$$

The functions $v_N$ and $\phi(t,f_N(t))+\Delta_N(t)$ differ only at finitely many mesh points. Their integrals are equal, proving the residual identity, including $x=0,1$.

For the residual-limit argument, all pairs $(t,f_N(t))$ belong to the compact rectangle $[0,1]\times[-M_1,M_1]$, on which $\phi$ is uniformly continuous. If $t\in(t_i,t_{i+1})$, then

$$
|t-t_i|\le N^{-1},\qquad |f_N(t)-f_N(t_i)|\le M/N.
$$

Thus the product-metric distance between $(t,f_N(t))$ and $(t_i,f_N(t_i))$ is at most $(1+M)/N$, independently of the cell and point. Uniform continuity makes the difference of the two field values tend uniformly to zero. This difference is $\Delta_N(t)$ off the mesh, while the mesh values are already zero. The full sequence, not merely a subsequence, therefore has the claimed uniform residual limit.

On the compact interval $[0,1]$, the common Lipschitz estimate gives equicontinuity and the bound $M_1$ gives pointwise boundedness. Arzelà–Ascoli supplies a subsequence with strictly increasing indices $\sigma(n)$ that converges uniformly to a function $f$. This is the required selection in part (c). Passing its bound to the pointwise limit gives $|f(t)|\le M_1$, and uniform convergence gives continuity of $f$. Both the polygons and their limit stay in the same compact rectangle. Uniform continuity of $\phi$ therefore changes the uniform estimate $|f_{\sigma(n)+1}(t)-f(t)|\to0$ into uniform convergence of $\phi(t,f_{\sigma(n)+1}(t))$ to $\phi(t,f(t))$. Strict increase implies $\sigma(n)\to\infty$, so the corresponding residual subsequence tends uniformly to zero. Their sums thus converge uniformly to the continuous function $g(t)=\phi(t,f(t))$.

Each such sum is integrable by the residual identity, and $g$ is integrable by continuity. A uniform integrand error at most $\delta$ bounds every primitive error on $[0,1]$ by $\delta$. Passing to the limit in the residual identities gives $f(x)=c+\int_0^x g(t)\,dt$ for every $x\in[0,1]$. At $x=0$ this gives $f(0)=c$. The fundamental theorem of calculus for continuous integrands gives derivative $g(x)$ in the interval interior and the corresponding one-sided derivatives at both endpoints. Together with the selected subsequence, these steps construct the required solution. The continuous scalar integrand also has an ordinary Riemann integral, equal to its interval integral. Thus its Riemann integral from $0$ to $x$ is $f(x)-c$, as required.

**Lean declarations:** `node_zero`, `node_succ`, `polygon_continuous`, `polygon_zero`, `polygon_cell`, `polygon_mesh`, `polygon_hasDerivAt`, `polygon_norm_sub_le`, `polygon_bound`, `residual_mesh`, `residual_eq_deriv_sub`, `residual_bound`, `residual_riemann_integrable`, `polygon_lipschitz`, `polygon_deriv_bound`, `polygon_equicontinuous`, `velocity_integral`, `residual_integral_identity`, `residual_riemann_identity`, `field_uniformContinuousOn`, `residual_uniform`, `limit_bound`, `composition_uniform`, `limit_integral_equation`, `limit_solution`, `polygon_subsequence`, `exists_solution`, `exercise25_solution`, `exercise25_riemann_solution`.

<a id="r07e26"></a>
### 7.26 — Vector-valued solutions from Euler polygons
**Lean source:** [Exercise26.lean](../../../Math/Rudin/Chapter07/Exercise26.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $k\ge0$ and let $\Phi:[0,1]\times\mathbb R^k\to\mathbb R^k$ be continuous and bounded in the Euclidean norm. For every $c\in\mathbb R^k$, the vector Euler polygons from [Exercise 7.25](#r07e25) have a uniformly convergent subsequence on $[0,1]$. Its continuous limit $f$ satisfies

$$
f(0)=c,\qquad f(x)=c+\int_0^x\Phi(t,f(t))\,dt,
\qquad f'(x)=\Phi(x,f(x)).
$$

The derivative is ordinary for $0<x<1$ and one-sided at both endpoints. The residuals of the full polygon sequence tend uniformly to zero. No Lipschitz condition on $\Phi$, and no uniqueness conclusion, is imposed.

**Proof.** Choose $M\ge0$ with $\|\Phi(t,z)\|\le M$ on the strip; any given bound is nonnegative because it bounds $\|\Phi(0,c)\|$. In the mesh construction $t_i=i/N$, define

$$
z_0=c,\qquad z_{i+1}=z_i+N^{-1}\Phi(t_i,z_i)
$$

and interpolate affinely. The same sum and triangle-inequality arguments as in Exercise 7.25 give

$$
\|f_N(t)\|\le\|c\|+M,
\qquad\|f_N(t)-f_N(s)\|\le M|t-s|.
$$

Finite-dimensional Euclidean space is complete, and its closed bounded sets are compact. The vector form of Arzelà–Ascoli therefore supplies strictly increasing indices and a uniform polygon limit $f$. Continuity of $\Phi$ is uniform on the compact set $[0,1]\times\overline B(0,\|c\|+M)$. The cell estimates $|t-t_i|\le1/N$ and $\|f_N(t)-z_i\|\le M/N$ make the residuals uniformly small. At mesh points their defined value is zero. The same uniform continuity gives convergence of $\Phi(t,f_N(t))$ along the selected subsequence to $\Phi(t,f(t))$, uniformly in $t$.

Pass to the limit in the polygon residual integral identity. The integral error is bounded by the interval length times the uniform integrand error, so the displayed integral equation follows. Its integrand is continuous. The fundamental theorem of calculus gives the equation for the derivative, including the two one-sided endpoint derivatives, and evaluation at zero gives $f(0)=c$. This uses the actual vector Euler construction, not a separate differential-equation existence theorem. If $k=0$, the target has one point and all these conclusions still hold.

**Lean declarations:** `exercise26_vector_existence`, `exercise26_vector_residual`.
