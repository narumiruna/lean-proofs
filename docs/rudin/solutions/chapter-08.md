<a id="chapter-08"></a>

# Chapter 8 — Some Special Functions

[All chapters](../solutions.md) · [Previous chapter](chapter-07.md) · [Next chapter](chapter-09.md)

**Exercises:** [1](#r08e01) · [2](#r08e02) · [3](#r08e03) · [4](#r08e04) · [5](#r08e05) · [6](#r08e06) · [7](#r08e07) · [8](#r08e08) · [9](#r08e09) · [10](#r08e10) · [11](#r08e11) · [12](#r08e12) · [13](#r08e13) · [14](#r08e14) · [15](#r08e15) · [16](#r08e16) · [17](#r08e17) · [18](#r08e18) · [19](#r08e19) · [20](#r08e20) · [21](#r08e21) · [22](#r08e22) · [23](#r08e23) · [24](#r08e24) · [25](#r08e25) · [26](#r08e26) · [27](#r08e27) · [28](#r08e28) · [29](#r08e29) · [30](#r08e30) · [31](#r08e31)

<a id="r08e01"></a>
### 8.1 — A smooth function with all derivatives zero at the origin
**Lean source:** [Exercise01.lean](../../../Math/Rudin/Chapter08/Exercise01.lean).
**Inventory status:** Verified as stated.

**Statement.** Define the real function

$$
f(x)=\begin{cases}e^{-1/x^2},&x\ne0,\\0,&x=0.\end{cases}
$$

It is smooth on all of $\mathbb R$. Every successive derivative genuinely exists at every real point, and $f^{(n)}(0)=0$ for every integer $n\ge0$. In particular, the derivative of $f^{(n)}$ at zero exists and equals zero for every $n\ge0$.

**Proof.** Use the standard smooth function

$$
G(t)=\begin{cases}e^{-1/t},&t>0,\\0,&t\le0.\end{cases}
$$

The library's smooth-extension theorem gives smoothness of $G$ and the following derivative identity, including at zero: for a real polynomial $P$,

$$
\frac{d}{dt}\bigl(P(1/t)G(t)\bigr)
=Q(1/t)G(t),\qquad Q(u)=u^2\bigl(P(u)-P'(u)\bigr).
$$

At $t=0$, both products are understood as their zero extensions. Starting with $P=1$, repeated application of this identity shows that every derivative of $G$ has this form and vanishes at zero. The zero extensions are justified by the decay of $e^{-1/t}$ faster than every power of $1/t$ as $t\downarrow0$, as used in the smooth-extension theorem.

Now $f(x)=G(x^2)$, which gives exactly the stated piecewise formula and is smooth by composition. For each positive order, the higher chain rule (Faà di Bruno's formula) expresses its derivative at zero as a finite sum whose terms each contain a derivative of $G$ evaluated at $0$. Every such factor is zero. Order zero is $f(0)=G(0)=0$. Smoothness ensures existence of all successive derivatives, so the vanishing formulas do not rely on assigning default values to nonexistent derivatives.

**Lean declarations:** `exercise01_formula`, `exercise01_smooth`, `exercise01_flatness`, `exercise01_all_derivatives`, `exercise01_derivatives_at_zero`.

<a id="r08e02"></a>
### 8.2 — Two different iterated sums
**Lean source:** [Exercise02.lean](../../../Math/Rudin/Chapter08/Exercise02.lean).
**Inventory status:** Verified as stated.

**Statement.** For positive integers $i,j$, define

$$
a_{ij}=\begin{cases}
0,&i<j,\\
-1,&i=j,\\
2^{j-i},&i>j.
\end{cases}
$$

Every row and every column has a convergent ordinary sum, but

$$
\sum_{i=1}^{\infty}\left(\sum_{j=1}^{\infty}a_{ij}\right)=-2,
\qquad
\sum_{j=1}^{\infty}\left(\sum_{i=1}^{\infty}a_{ij}\right)=0.
$$

The outer sums also converge in their natural order.

**Proof.** Row $i$ is zero after its diagonal term. Its finite sum is

$$
-1+\sum_{j=1}^{i-1}2^{j-i}
=-1+\sum_{k=1}^{i-1}2^{-k}
=-2^{1-i}.
$$

This includes $i=1$, where the finite sum before the diagonal is empty. Summing the row sums gives the geometric series $-\sum_{i\ge1}2^{1-i}=-2$.

Column $j$ starts with $j-1$ zeros, followed by $-1$ and the geometric tail $2^{-1},2^{-2},\ldots$. Its sum is $-1+\sum_{k\ge1}2^{-k}=0$. Consequently every outer partial sum of the column sums is zero. These calculations establish convergence of every inner sum and both outer sums, while their unequal values show that interchanging the two infinite sums is invalid for this signed array.

**Lean declarations:** `exercise02_formula`, `exercise02_source_formula`, `exercise02_rows`, `exercise02_columns`, `exercise02_row_then_outer`, `exercise02_column_then_outer`.

<a id="r08e03"></a>
### 8.3 — Interchanging nonnegative double sums
**Lean source:** [Exercise03.lean](../../../Math/Rudin/Chapter08/Exercise03.lean).
**Inventory status:** Verified as stated.

**Statement.** For an array of nonnegative real numbers $a_{ij}$, indexed by $i,j\ge1$,

$$
\sum_{i=1}^{\infty}\left(\sum_{j=1}^{\infty}a_{ij}\right)
=\sum_{j=1}^{\infty}\left(\sum_{i=1}^{\infty}a_{ij}\right),
$$

where both sides take values in $[0,\infty]$. In particular, one side is infinite if and only if the other is infinite. The result also holds when individual entries themselves may be $+\infty$. The inner sums and the outer sums are limits of their natural ordered partial sums.

**Proof.** Tonelli's theorem for nonnegative series identifies either order of summation with the sum over all pairs $(i,j)$. Equivalently, both sides are the supremum of all finite subsums of the array: any finite set of pairs is contained in a finite rectangle, and nonnegativity makes these subsums increase when indices are added. Thus the two extended values agree without any finiteness assumption.

For each fixed row, the first $N$ terms increase to the supremum of its finite subsums, which is its extended sum. The same applies to the sequence of row sums and, after interchanging the indices, to columns and column sums. This proves the asserted ordered convergence even when the limit is infinite. For finite nonnegative real entries, their embedding into $[0,\infty]$ preserves their values, so the extended theorem applies directly. Equality immediately gives the equivalence of divergence to infinity in the two orders.

**Lean declarations:** `exercise03_nonnegative_interchange`, `exercise03_ordered_sums`, `exercise03_infinite_iff`, `exercise03_real_entries`.

<a id="r08e04"></a>
### 8.4 — Four limits involving powers and logarithms
**Lean source:** [Exercise04.lean](../../../Math/Rudin/Chapter08/Exercise04.lean).
**Inventory status:** Verified as stated.

**Statement.** The following real limits hold:

1. For $b>0$,

   $$
   \lim_{x\to0}\frac{b^x-1}{x}=\log b.
   $$

2. On the natural domain $x>-1$,

   $$
   \lim_{x\to0}\frac{\log(1+x)}x=1.
   $$

3. For nonzero $x$ near zero, with $1+x>0$,

   $$
   \lim_{x\to0}(1+x)^{1/x}=e.
   $$

4. For each fixed real $x$,

   $$
   \lim_{n\to\infty}\left(1+\frac xn\right)^n=e^x.
   $$

   Here $n$ runs through positive integers, and the base is positive for all sufficiently large $n$.

The first three limits are punctured, two-sided limits at zero.

**Proof.** The derivative of $b^x$ at zero is $b^0\log b=\log b$, so its difference quotient proves the first limit. The derivative of $\log(1+x)$ at zero is $1$, giving the second. For all sufficiently small $|x|$, $1+x>0$, and hence

$$
(1+x)^{1/x}=\exp\left(\frac{\log(1+x)}x\right).
$$

The second limit and continuity of the exponential give the third.

The fourth assertion is the standard exponential limit for arbitrary fixed real $x$, used directly from the library. It can also be seen from the second limit: if $x\ne0$, put $t_n=x/n$. Then $t_n\to0$ through nonzero values and

$$
n\log(1+x/n)=x\,\frac{\log(1+t_n)}{t_n}\longrightarrow x.
$$

Exponentiation gives the result once $1+x/n>0$. This eventual positivity follows from $x/n\to0$. If $x=0$, every positive-index term is $1=e^0$. No value assigned at the initial index $n=0$ affects the limit.

**Lean declarations:** `exercise04_a`, `exercise04_b`, `exercise04_positive_base`, `exercise04_c`, `exercise04_d`, `exercise04_d_positive_base`.

<a id="r08e05"></a>
### 8.5 — Four limits from exponential and trigonometric remainders
**Lean source:** [Exercise05.lean](../../../Math/Rudin/Chapter08/Exercise05.lean).
**Inventory status:** Verified as stated.

**Statement.** With the natural real domains of the expressions,

$$
\begin{aligned}
\text{(a)}\quad&\lim_{x\to0}\frac{e-(1+x)^{1/x}}x=\frac e2,\\
\text{(b)}\quad&\lim_{n\to\infty}\frac n{\log n}\bigl(n^{1/n}-1\bigr)=1\quad(n\in\mathbb N,\ n>1),\\
\text{(c)}\quad&\lim_{x\to0}\frac{\tan x-x}{x(1-\cos x)}=\frac23,\\
\text{(d)}\quad&\lim_{x\to0}\frac{x-\sin x}{\tan x-x}=\frac12.
\end{aligned}
$$

The real limits are two-sided, with zero deleted. The power in (a) has positive base near zero.

**Proof.** L'Hôpital's rule gives

$$
\frac{\log(1+x)-x}{x^2}\longrightarrow-\frac12,
$$

because the quotient of the derivatives is $-1/[2(1+x)]$ for sufficiently small nonzero $x$. Put $h(x)=\log(1+x)/x-1$. Then $h(x)\to0$ and $h(x)/x\to-1/2$. The exponential difference quotient $(e^u-1)/u$, continuously extended to value $1$ at zero, tends to $1$. Therefore

$$
\frac{e-(1+x)^{1/x}}x
=-e\,\frac{e^{h(x)}-1}{h(x)}\,\frac{h(x)}x
\longrightarrow\frac e2,
$$

where the continuous extension makes the identity valid also when $h(x)=0$. For (b), set $u_n=\log n/n$. Then $u_n\to0$ and $u_n>0$ for $n>1$. The expression is $(e^{u_n}-1)/u_n$, whose limit is $1$.

For the trigonometric limits, L'Hôpital's rule and $\sin x/x\to1$ give

$$
C(x)=\frac{1-\cos x}{x^2}\longrightarrow\frac12,
\qquad
S(x)=\frac{x-\sin x}{x^3}\longrightarrow\frac16.
$$

Since $\cos x\to1$,

$$
T(x)=\frac{\tan x-x}{x^3}
=\frac{C(x)-S(x)}{\cos x}\longrightarrow\frac13.
$$

The ratios in (c) and (d) are respectively $T(x)/C(x)$ and $S(x)/T(x)$, giving $2/3$ and $1/2$. These nonzero remainder limits also ensure that the original denominators are nonzero in a sufficiently small deleted neighborhood of zero. Thus no value assigned by totalized division at a singular point enters the argument.

**Lean declarations:** `exercise05_a`, `exercise05_b`, `exercise05_c`, `exercise05_d`, `exercise05_domains`.

<a id="r08e06"></a>
### 8.6 — Continuous solutions of the exponential equation
**Lean source:** [Exercise06.lean](../../../Math/Rudin/Chapter08/Exercise06.lean).
**Inventory status:** Verified as stated.

**Statement.** Suppose $f:\mathbb R\to\mathbb R$ is not identically zero and satisfies

$$
f(x)f(y)=f(x+y)\qquad(x,y\in\mathbb R).
$$

If $f$ is differentiable, then $f(x)=e^{cx}$ for some real constant $c$. The same conclusion holds if only continuity is assumed. Conversely, every $f(x)=e^{cx}$ is differentiable, is not identically zero, and satisfies the equation. Even without a regularity assumption, the equation and the nonzero hypothesis imply $f(0)=1$ and $f(x)>0$ everywhere.

**Proof.** Choose $t$ with $f(t)\ne0$. The identity $f(t)f(0)=f(t)$ gives $f(0)=1$. Then $f(x)f(-x)=1$, so $f$ never vanishes. Since

$$
f(x)=f(x/2)^2,
$$

it is positive everywhere. Thus positivity is a conclusion, not an additional hypothesis.

For a continuous solution, define $h(x)=\log f(x)$. Positivity and continuity of $f$ make $h$ continuous, and the equation gives $h(x+y)=h(x)+h(y)$. The standard theorem on continuous additive real functions gives $h(x)=xh(1)$: additivity proves this first on rational arguments, and density of the rationals with continuity extends it to every real argument. With $c=h(1)$, exponentiation gives $f(x)=e^{cx}$. A differentiable solution is continuous, so the first part follows as well.

Conversely, $e^{cx}$ is differentiable and never zero, and $e^{cx}e^{cy}=e^{c(x+y)}$ by the exponential addition law.

**Scope.** “Not identically zero” means that $f(t)\ne0$ for at least one real $t$. The identically zero solution of the functional equation is excluded in both regularity cases.

**Lean declarations:** `exercise06_positive`, `exercise06_a`, `exercise06_b`, `exercise06_converse`.

<a id="r08e07"></a>
### 8.7 — Strict bounds for the sine ratio
**Lean source:** [Exercise07.lean](../../../Math/Rudin/Chapter08/Exercise07.lean).
**Inventory status:** Verified as stated.

**Statement.** For every real $x$ with $0<x<\pi/2$,

$$
\frac2\pi<\frac{\sin x}{x}<1.
$$

**Proof.** The strict chord bound for sine on $(0,\pi/2)$ gives $(2/\pi)x<\sin x$. The standard strict inequality $\sin x<x$ holds for $x>0$. Divide both inequalities by the positive number $x$ to obtain the conclusion. The open interval is essential to the stated strict lower bound: at $x=\pi/2$ that bound becomes equality, while the displayed ratio is not defined at zero.

**Lean declarations:** `exercise07_sine_ratio`.

<a id="r08e08"></a>
### 8.8 — A sine bound for integer multiples
**Lean source:** [Exercise08.lean](../../../Math/Rudin/Chapter08/Exercise08.lean).
**Inventory status:** Verified as stated.

**Statement.** For every integer $n\ge0$ and every real $x$,

$$
|\sin(nx)|\le n|\sin x|.
$$

The integer restriction cannot be dropped: the inequality fails for $n=1/2$ and $x=\pi$.

**Proof.** For $n=0$, both sides are zero. If the bound holds for $n$, the addition formula and $|\cos t|\le1$ give

$$
\begin{aligned}
|\sin((n+1)x)|
&\le |\sin(nx)|\,|\cos x|+|\cos(nx)|\,|\sin x|\\
&\le |\sin(nx)|+|\sin x|\\
&\le(n+1)|\sin x|.
\end{aligned}
$$

Induction proves the assertion for all nonnegative integers. For the stated noninteger example, $|\sin(\pi/2)|=1$, while $(1/2)|\sin\pi|=0$, so the proposed inequality is strictly reversed.

**Lean declarations:** `exercise08_integer_bound`, `exercise08_noninteger_failure`.

<a id="r08e09"></a>
### 8.9 — Harmonic sums and the decimal scale for exceeding one hundred
**Lean source:** [Exercise09.lean](../../../Math/Rudin/Chapter08/Exercise09.lean).
**Inventory status:** Verified as stated.

**Statement.** For $N\ge1$, let $H_N=\sum_{j=1}^N1/j$. Then $H_N-\log N$ has a finite limit, the Euler–Mascheroni constant $\gamma$. For a nonnegative integer $m$, $H_{10^m}>100$ holds exactly when $m\ge44$. In particular, the requested decimal scale is located by

$$
H_{10^{43}}<100<H_{10^{44}}.
$$

**Proof.** The standard harmonic-sum theorem gives

$$
H_N-\log N\longrightarrow\gamma.
$$

For the numerical scale, use the library bounds

$$
2.3025850926<\log10<2.3025850934.
$$

The sequence $H_N-\log N$ is decreasing for positive $N$, and its value at $N=6$ is less than $2/3$. Consequently,

$$
H_{10^{43}}<43\log10+\frac23
<43(2.3025850934)+\frac23<100.
$$

In the other direction, the harmonic integral bound $\log(N+1)\le H_N$ and monotonicity of logarithm give

$$
H_{10^{44}}\ge\log(10^{44}+1)\ge44\log10
>44(2.3025850926)>100.
$$

Thus the two bounds are strict and use explicit certified logarithm estimates, rather than an unquantified asymptotic approximation. Since every harmonic summand is positive, $H_N$ increases with $N$. If $m\le43$, then $H_{10^m}\le H_{10^{43}}<100$; if $m\ge44$, then $H_{10^m}\ge H_{10^{44}}>100$. This proves the exact integer-exponent threshold.

**Lean declarations:** `exercise09_sum_eq_harmonic`, `exercise09_a`, `exercise09_b`, `exercise09_decimal_threshold`.

<a id="r08e10"></a>
### 8.10 — Divergence of the prime reciprocal series
**Lean source:** [Exercise10.lean](../../../Math/Rudin/Chapter08/Exercise10.lean).
**Inventory status:** Verified as stated.

**Statement.** Define the ordered prime reciprocal partial sums by

$$
P_N=\sum_{\substack{p<N\\p\text{ prime}}}\frac1p.
$$

Then $P_N\to+\infty$. In particular, for every real $M$ there is an $N$ such that $P_N>M$.

**Proof.** Use the standard divergence theorem for prime reciprocals, supplied by the library: the nonnegative sequence

$$
a_n=\begin{cases}1/n,&n\text{ prime},\\0,&\text{otherwise}\end{cases}
$$

is not summable. The values at $0$ and $1$ are zero, so no reciprocal of zero is involved in the prime sum. Its ordinary partial sums equal $P_N$.

For a nonnegative sequence, these partial sums are nondecreasing. If they were bounded above, monotone convergence would give a finite limit and hence summability, contrary to the cited theorem. Therefore they are unbounded above. Monotonicity then gives divergence to $+\infty$: after a partial sum exceeds any fixed $M$, every later one also exceeds $M$.

**Scope.** The file uses the library's prime-reciprocal divergence theorem rather than proving the book's finite-product hint as a separate result. It explicitly converts that theorem into divergence of the ordered prime partial sums and their unboundedness.

**Lean declarations:** `exercise10_partial_eq`, `exercise10_prime_reciprocals`, `exercise10_unbounded`.

<a id="r08e11"></a>
### 8.11 — An Abelian limit for a Laplace integral
**Lean source:** [Exercise11.lean](../../../Math/Rudin/Chapter08/Exercise11.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $f:[0,\infty)\to\mathbb C$ be Riemann integrable on $[0,A]$ for every finite $A>0$, and suppose $f(x)\to1$ as $x\to\infty$. For every $t>0$, the improper integral

$$
L(t)=\lim_{A\to\infty}\int_0^A e^{-tx}f(x)\,dx
$$

exists and converges absolutely. Moreover,

$$
\lim_{t\downarrow0}tL(t)=1.
$$

Real functions are included by their embedding into $\mathbb C$.

**Proof.** Convergence to one bounds $|f(x)|$ by $2$ for all sufficiently large $x$. On the remaining compact interval, Riemann integrability supplies a finite bound. Thus there is one $M\ge0$ with $|f(x)|\le M$ for every $x\ge0$.

The finite Riemann integrals agree with their interval Lebesgue integrals: apply the real comparison theorem to the real and imaginary components. The countable cover $(0,\infty)=\bigcup_{n\ge0}(0,n+1]$ then supplies almost-everywhere strong measurability on the positive ray. For each $t>0$,

$$
|e^{-tx}f(x)|\le Me^{-tx},\qquad
\int_0^\infty Me^{-tx}\,dx=\frac Mt<\infty.
$$

Hence the Laplace integrand is absolutely integrable. It is also properly Riemann integrable on each finite interval, by multiplication with the continuous exponential. Its finite-interval integrals therefore tend to its integral over $(0,\infty)$, proving the asserted improper-integral interpretation rather than using a default value of a nonintegrable function.

For $t>0$, substitute $y=tx$ to obtain

$$
tL(t)=\int_0^\infty e^{-y}f(y/t)\,dy.
$$

For each fixed $y>0$, $y/t\to\infty$ as $t\downarrow0$, so the integrand tends to $e^{-y}$. Its norm is at most $Me^{-y}$, independently of $t$, and this majorant is integrable. The dominated convergence theorem gives

$$
\lim_{t\downarrow0}tL(t)=\int_0^\infty e^{-y}\,dy=1.
$$

The point $y=0$ has measure zero and requires no limit assumption on $f(0)$.

**Lean declarations:** `complex_riemann_bridge`, `exercise11_truncated_riemann`, `exercise11_measurable`, `exercise11_bounded`, `exercise11_laplace_integrable`, `exercise11_improper_integral`, `exercise11_change_variable`, `exercise11_abelian_limit`.

<a id="r08e12"></a>
### 8.12 — The periodic indicator, sine series, and the sinc-square integral

**Lean source:** [Exercise12.lean](../../../Math/Rudin/Chapter08/Exercise12.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $0<\delta<\pi$. Let $f_\delta$ be the $2\pi$-periodic function whose values on $[-\pi,\pi]$ are $1$ when $|x|\le\delta$ and $0$ otherwise. In particular, both endpoints have value zero, while $f_\delta(\pm\delta)=1$. With the convention

$$
c_n=\frac{1}{2\pi}\int_{-\pi}^{\pi}e^{-inx}f_\delta(x)\,dx,
$$

all its complex Fourier coefficients are

$$
c_0=\frac{\delta}{\pi},\qquad c_n=\frac{\sin(n\delta)}{n\pi}\quad(n\in\mathbb Z\setminus\{0\}).
$$

The following series converge in their usual order:

$$
\sum_{n=1}^{\infty}\frac{\sin(n\delta)}{n}=\frac{\pi-\delta}{2},\qquad
\sum_{n=1}^{\infty}\frac{\sin^2(n\delta)}{n^2\delta}=\frac{\pi-\delta}{2}.
$$

The second assertion also includes summability as a nonnegative family. Define $\operatorname{sinc}(x)=\sin x/x$ for $x\ne0$ and $\operatorname{sinc}(0)=1$. Its square is integrable on $[0,\infty)$, and

$$
\int_0^\infty\operatorname{sinc}^2(x)\,dx=\frac{\pi}{2},\qquad
\lim_{A\to\infty}\int_0^A\operatorname{sinc}^2(x)\,dx=\frac{\pi}{2}.
$$

For each $A\ge0$, the tagged Riemann integral on $[0,A]$ exists and equals the corresponding finite interval integral above. This includes the zero-length interval. The continuous value of the integrand at zero is $1$. Finally,

$$
\sum_{n=0}^{\infty}\frac{1}{(2n+1)^2}=\frac{\pi^2}{8},
$$

both as a summable family and as a limit of the ordered partial sums.

**Proof.** First put $g_\delta=\mathbf1_{[-\delta,\delta]}$ on the real line. The periodic function is constructed by choosing the representative in $(-\pi,\pi]$ modulo $2\pi$. Periodicity holds for every real $\delta$. If $\delta<\pi$, this construction agrees with $g_\delta$ on the entire closed interval $[-\pi,\pi]$: at $-\pi$ the chosen representative is $\pi$, and both indicator values are zero. Thus its Fourier coefficients equal those of the indicator on this interval.

The source also checks ordinary Riemann integrability, not only measurable integrability. For every $\delta\ge0$, write

$$
g_\delta(x)=\mathbf1_{\{x\le\delta\}}-\mathbf1_{\{x<-\delta\}}.
$$

Both real functions on the right are decreasing, so each has a tagged Riemann integral on $[-\pi,\pi]$. Their difference is the real part of $g_\delta$, and its imaginary part is zero. This proves complex Riemann integrability, including $\delta=0$ and $\delta\ge\pi$. Agreement on the closed interval then proves Riemann integrability of the periodic function for $0\le\delta<\pi$. The identities claimed above retain the strict assumptions $0<\delta<\pi$.

For these strict assumptions, the coefficient integral restricts to $[-\delta,\delta]$. At $n=0$ it is $2\delta/(2\pi)$. For every nonzero integer $n$, integration of the exponential gives

$$
c_n=\frac{1}{2\pi}\left[\frac{e^{-inx}}{-in}\right]_{-\delta}^{\delta}
=\frac{\sin(n\delta)}{n\pi}.
$$

This includes negative frequencies; in particular, $c_{-n}=c_n$. The indicator is measurable and bounded in norm by $1$, so it belongs to $L^2$ on the finite fundamental interval for every real $\delta$. Under $0<\delta<\pi$, its normalized squared norm is

$$
\frac{1}{2\pi}\int_{-\pi}^{\pi}|g_\delta(x)|^2\,dx=\frac{\delta}{\pi}.
$$

Parseval, with this normalization, therefore gives a summable family indexed by $\mathbb Z$ and the equality

$$
\frac{\delta}{\pi}=\frac{\delta^2}{\pi^2}
+\frac{2}{\pi^2}\sum_{n=1}^{\infty}\frac{\sin^2(n\delta)}{n^2}.
$$

Separate the zero coefficient, pair positive and negative frequencies, and multiply by $\pi^2/(2\delta)$. This proves the sine-square identity and hence its ordered partial-sum limit. No reciprocal-square evaluation is used in this argument.

To prove the unsquared sine identity, let $s_N$ be the symmetric Fourier partial sum of $f_\delta$ at zero. The coefficient formulas give, also for $N=0$,

$$
s_N=\frac{\delta}{\pi}+\frac{2}{\pi}\sum_{n=1}^{N}\frac{\sin(n\delta)}{n}.
$$

The periodic function equals $1$ in a neighborhood of zero. Its two one-sided limits there are thus $1$. Pointwise Fejer convergence for periodic Riemann-integrable functions, as proved in Exercise 8.16, shows that the arithmetic means of $s_0,\ldots,s_N$ tend to $1$. Moreover, for each $k\ge1$,

$$
|k(s_k-s_{k-1})|=\frac{2}{\pi}|\sin(k\delta)|\le\frac{2}{\pi}.
$$

The Tauberian converse proved in Exercise 3.14(e) applies to this bounded sequence of weighted differences and the convergent arithmetic means. It yields $s_N\to1$. Solving the displayed formula for the sine partial sum gives the claimed ordered limit. This argument does not assert absolute summability of the unsquared sine series.

For the improper integral, the proof makes the passage from the sine-square sum to an integral explicit. For any mesh $\delta>0$ and $x\ge0$, define the right-endpoint sample

$$
q_\delta(x)=\delta\bigl(\lfloor x/\delta\rfloor+1\bigr).
$$

It is measurable and satisfies $x<q_\delta(x)\le x+\delta$. The intervals $[n\delta,(n+1)\delta)$, $n\ge0$, are pairwise disjoint and cover $[0,\infty)$. On the $n$th interval the sample equals $(n+1)\delta$, so

$$
\int_0^\infty\operatorname{sinc}^2(q_\delta(x))\,dx
=\sum_{n=0}^{\infty}\delta\operatorname{sinc}^2((n+1)\delta).
$$

Here both integrability and summability are proved. The common integrable bound is

$$
0\le\operatorname{sinc}^2(y)\le\frac{4}{(x+1)^2}
\quad(0\le x\le y,\ y>0).
$$

For $x\le1$, use $|\operatorname{sinc}(y)|\le1$ and $(x+1)^2\le4$. For $x>1$, use $(x+1)^2\le4y^2$ and $y^2\operatorname{sinc}^2(y)=\sin^2 y\le1$. The bound is integrable on $[0,\infty)$ by the standard power-integrability criterion. It controls every sampled function and, away from the single point zero, $\operatorname{sinc}^2(x)$ itself. Continuity supplies the value at zero.

When $0<\delta<\pi$, the terms in the sample sum satisfy

$$
\delta\operatorname{sinc}^2((n+1)\delta)
=\frac{\sin^2((n+1)\delta)}{(n+1)^2\delta}.
$$

The sine-square identity therefore evaluates the sampled integral as $(\pi-\delta)/2$. Now take $\delta_j=1/(j+1)$. Each mesh is less than $\pi$, and the sample bounds show $q_{\delta_j}(x)\to x$ for every $x\ge0$, including $x=0$. Continuity of sinc and dominated convergence give convergence of the sampled integrals to the integral of $\operatorname{sinc}^2$. Their known values tend to $\pi/2$. This evaluates the half-line integral. Integrability then gives convergence of the finite interval integrals to the same value as $A\to\infty$. On every $[0,A]$ with $A\ge0$, continuity and the tagged-integral bridge identify the finite integral with the ordinary Riemann integral.

Finally, set $\delta=\pi/2$ in the sine-square identity and multiply by $\pi/2$. The resulting series $\sum_{n\ge1}\sin^2(n\pi/2)/n^2$ has sum $\pi^2/8$. Its even terms vanish, and its odd terms are $1/(2n+1)^2$, since $\sin^2((2n+1)\pi/2)=1$. Splitting the summable family into even and odd indices proves the last identity and its ordered version.

**Lean declarations:** Definitions: `Rudin.Chapter08.exercise12Indicator`, `Rudin.Chapter08.exercise12Periodic`, `Rudin.Chapter08.exercise12Sample`. Coefficients and integrability: `Rudin.Chapter08.exercise12_integral_restrict`, `Rudin.Chapter08.exercise12_coefficient_zero`, `Rudin.Chapter08.exercise12_coefficient`, `Rudin.Chapter08.exercise12_memLp`, `Rudin.Chapter08.exercise12_energy`, `Rudin.Chapter08.exercise12_coeff_norm`, `Rudin.Chapter08.exercise12_riemann`, `Rudin.Chapter08.exercise12_periodic`, `Rudin.Chapter08.exercise12_periodic_eq`, `Rudin.Chapter08.exercise12_periodic_riemann`, `Rudin.Chapter08.exercise12_periodic_coefficient`. Series: `Rudin.Chapter08.exercise12_parseval`, `Rudin.Chapter08.exercise12_sine_square_sum`, `Rudin.Chapter08.exercise12_ordered_sine_square_sum`, `Rudin.Chapter08.exercise12_limit_at_zero`, `Rudin.Chapter08.exercise12_partial_zero`, `Rudin.Chapter08.exercise12_sine_series`, `Rudin.Chapter08.exercise12_odd_square_sum`, `Rudin.Chapter08.exercise12_ordered_odd_square_sum`. Integral: `Rudin.Chapter08.exercise12_sample_bounds`, `Rudin.Chapter08.exercise12_sample_measurable`, `Rudin.Chapter08.exercise12_sinc_dominant`, `Rudin.Chapter08.exercise12_dominant_integrable`, `Rudin.Chapter08.exercise12_steps_integrable`, `Rudin.Chapter08.exercise12_cells_cover`, `Rudin.Chapter08.exercise12_cells_disjoint`, `Rudin.Chapter08.exercise12_cell_integral`, `Rudin.Chapter08.exercise12_riemann_sum_hasSum`, `Rudin.Chapter08.exercise12_sinc_sq_integrable`, `Rudin.Chapter08.exercise12_sample_limit`, `Rudin.Chapter08.exercise12_step_integrals_limit`, `Rudin.Chapter08.exercise12_step_integral`, `Rudin.Chapter08.exercise12_sinc_square_integral`, `Rudin.Chapter08.exercise12_sinc_square_improper`, `Rudin.Chapter08.exercise12_sinc_square_at_zero`, `Rudin.Chapter08.exercise12_sinc_square_riemann`.

<a id="r08e13"></a>
### 8.13 — Parseval for the sawtooth and the reciprocal-square sum

**Lean source:** [Exercise13.lean](../../../Math/Rudin/Chapter08/Exercise13.lean).

**Inventory status:** Verified as stated.

**Statement.** Define the sawtooth on $\mathbb R/(2\pi\mathbb Z)$ by taking the representative $x\in[0,2\pi)$ and assigning it the complex value $x$. Its periodic real-line representative has value zero at every multiple of $2\pi$, including $2\pi$ itself. Its Fourier coefficients, with the normalization

$$
c_n=\frac{1}{2\pi}\int_0^{2\pi}x e^{-inx}\,dx,
$$

are

$$
c_0=\pi,\qquad c_n=\frac{i}{n}\quad(n\in\mathbb Z\setminus\{0\}).
$$

The representative $x\mapsto x$ belongs to $L^2$ on $(0,2\pi]$, its normalized energy is $4\pi^2/3$, and Parseval gives

$$
\sum_{n\in\mathbb Z}|c_n|^2=\frac{4\pi^2}{3}.
$$

Consequently,

$$
\sum_{n=1}^{\infty}\frac{1}{n^2}=\frac{\pi^2}{6}.
$$

Both summability and convergence of the ordered partial sums to this value are proved.

**Proof.** The circle construction agrees with $x\mapsto x$ for every $0\le x<2\pi$. The standard coefficient formula for a lifted half-open representative identifies its circle coefficients with the displayed interval integrals. The different assigned value at $2\pi$ does not change any integral.

For the zero coefficient, integration gives

$$
c_0=\frac{1}{2\pi}\left[\frac{x^2}{2}\right]_0^{2\pi}=\pi.
$$

For a nonzero integer $n$, the constant function $1$ has coefficient zero at frequency $n$ by orthogonality of Fourier characters. Apply the interval Fourier differentiation formula to $x\mapsto x$, whose derivative is the integrable constant $1$. Equivalently, integration by parts gives

$$
\int_0^{2\pi}x e^{-inx}\,dx
=\left[\frac{x e^{-inx}}{-in}\right]_0^{2\pi}
+\frac{1}{in}\int_0^{2\pi}e^{-inx}\,dx
=\frac{2\pi i}{n},
$$

because $e^{-2\pi in}=1$ and the last integral is zero. Division by $2\pi$ yields $c_n=i/n$, including negative $n$.

On $(0,2\pi]$, the representative is measurable and its norm is at most $2\pi$. This proves the actual $L^2$ hypothesis needed for interval Parseval. Since $|x|^2=x^2$,

$$
\frac{1}{2\pi}\int_0^{2\pi}x^2\,dx
=\frac{1}{2\pi}\left[\frac{x^3}{3}\right]_0^{2\pi}
=\frac{4\pi^2}{3}.
$$

Apply Parseval with this energy. The zero mode contributes $\pi^2$, and each nonzero mode has squared norm $1/n^2$. Splitting off zero and pairing positive with negative frequencies gives

$$
\frac{4\pi^2}{3}=\pi^2+2\sum_{n=1}^{\infty}\frac{1}{n^2}.
$$

Subtract $\pi^2$ and divide by $2$. Parseval supplies summability before this regrouping, so it proves the reciprocal-square identity without a precomputed zeta value. The ordered partial-sum limit follows from summability.

**Lean declarations:** Definition: `Rudin.Chapter08.exercise13Sawtooth`. Results: `Rudin.Chapter08.exercise13_periodic_value`, `Rudin.Chapter08.exercise13_periodic_coefficient`, `Rudin.Chapter08.exercise13_coefficient_zero`, `Rudin.Chapter08.exercise13_coefficient`, `Rudin.Chapter08.exercise13_memLp`, `Rudin.Chapter08.exercise13_energy`, `Rudin.Chapter08.exercise13_parseval`, `Rudin.Chapter08.exercise13_coeff_norm`, `Rudin.Chapter08.exercise13_square_sum`, `Rudin.Chapter08.exercise13_ordered_square_sum`.

<a id="r08e14"></a>
### 8.14 — A quadratic cosine expansion and two power sums

**Lean source:** [Exercise14.lean](../../../Math/Rudin/Chapter08/Exercise14.lean).

**Inventory status:** Verified as stated.

**Statement.** For every $x\in[-\pi,\pi]$, including both endpoints,

$$
(\pi-|x|)^2=\frac{\pi^2}{3}+4\sum_{n=1}^{\infty}\frac{\cos(nx)}{n^2}.
$$

The series is absolutely convergent. Moreover,

$$
\sum_{n=1}^{\infty}\frac1{n^2}=\frac{\pi^2}{6},\qquad
\sum_{n=1}^{\infty}\frac1{n^4}=\frac{\pi^4}{90}.
$$

All three identities also hold as limits of the indicated finite sums.

**Proof.** Apply the library's Bernoulli-polynomial cosine-series identity with index $1$ and coordinate $y=|x|/(2\pi)$. Here $0\le y\le1/2$, and evenness of cosine gives $\cos(2\pi ny)=\cos(nx)$. Substitution of $B_2(y)=y^2-y+1/6$ gives the displayed expansion. The zero-frequency term of the totalized natural-index series is zero; removing it gives exactly the positive-frequency series above. Absolute convergence also follows from $|\cos(nx)|\le1$ and convergence of the reciprocal-square series. Setting $x=0$ and dividing by $4$ gives its sum.

For the fourth powers, represent the same periodic function by $q(t)=(t-\pi)^2$ on $[0,2\pi]$. On negative inputs in $[-\pi,0)$, adding $2\pi$ gives $q(x+2\pi)=(\pi-|x|)^2$; the nonnegative half and both endpoints agree as well. Its complex Fourier coefficients, with normalization $c_n=(2\pi)^{-1}\int_0^{2\pi}q(t)e^{-int}\,dt$, are

$$
c_0=\frac{\pi^2}{3},\qquad c_n=\frac{2}{n^2}\quad(n\ne0).
$$

Integration by parts first gives coefficient $i/n$ for $t-\pi$ and then the stated coefficient for $q$; the endpoint values of $q$ agree. Direct integration gives $(2\pi)^{-1}\int_0^{2\pi}|q|^2=\pi^4/5$. The bounded continuous function $q$ is square integrable, so Parseval yields

$$
\frac{\pi^4}{5}=\frac{\pi^4}{9}+8\sum_{n=1}^{\infty}\frac1{n^4}.
$$

Solving gives $\pi^4/90$. Convergence of the ordered finite sums follows from the proved series sums.

**Lean declarations:** `Rudin.Chapter08.exercise14_frequency`, `Rudin.Chapter08.exercise14_cosine_hasSum`, `Rudin.Chapter08.exercise14_fourier_expansion`, `Rudin.Chapter08.exercise14_ordered_fourier`, `Rudin.Chapter08.exercise14_square_sum`, `Rudin.Chapter08.exercise14_ordered_square_sum`, `Rudin.Chapter08.exercise14_periodic_value`, `Rudin.Chapter08.exercise14_periodic_coefficient`, `Rudin.Chapter08.exercise14_coefficient_zero`, `Rudin.Chapter08.exercise14_coefficient`, `Rudin.Chapter08.exercise14_energy`, `Rudin.Chapter08.exercise14_parseval`, `Rudin.Chapter08.exercise14_fourth_power_sum`, `Rudin.Chapter08.exercise14_ordered_fourth_power_sum`.

<a id="r08e15"></a>
### 8.15 — Fejer kernels and uniform convergence

**Lean source:** [Exercise15.lean](../../../Math/Rudin/Chapter08/Exercise15.lean).

**Inventory status:** Verified as stated.

**Statement.** Use the Fourier conventions

$$
c_n(f)=\frac1{2\pi}\int_{-\pi}^{\pi}e^{-int}f(t)\,dt,\qquad
s_N(f;x)=\sum_{n=-N}^{N}c_n(f)e^{inx}.
$$

For $N\ge0$, put $D_N(t)=\sum_{n=-N}^{N}e^{int}=1+2\sum_{k=1}^{N}\cos(kt)$ and $K_N=(N+1)^{-1}\sum_{n=0}^{N}D_n$. Then $K_N$ is continuous, even, and nonnegative, and

$$
K_N(t)=\frac{1-\cos((N+1)t)}{(N+1)(1-\cos t)}\quad(t\notin2\pi\mathbb Z),\qquad
K_N(2\pi k)=N+1.
$$

It satisfies $(2\pi)^{-1}\int_{-\pi}^{\pi}K_N(t)\,dt=1$. If $0<\delta\le|t|\le\pi$, then

$$
K_N(t)\le\frac{2}{(N+1)(1-\cos\delta)}.
$$

For every complex-valued, $2\pi$-periodic function $f$ that is Riemann integrable on $[-\pi,\pi]$, its arithmetic Fourier mean satisfies

$$
\sigma_N(f;x)=\frac1{N+1}\sum_{n=0}^{N}s_n(f;x)
=\frac1{2\pi}\int_{-\pi}^{\pi}K_N(t)f(x-t)\,dt.
$$

The coefficient integrals and the Dirichlet and Fejer convolution integrals are genuine tagged Riemann integrals, with the same values as the interval integrals. If $f$ is continuous on $\mathbb R$, these means converge uniformly to $f$ on $[-\pi,\pi]$.

**Proof.** Pair positive and negative exponentials to obtain the cosine formula for $D_N$. The cosine addition identities give

$$
(1-\cos t)D_n(t)=\cos(nt)-\cos((n+1)t).
$$

Summing this identity gives the quotient formula away from $2\pi\mathbb Z$. At a multiple of $2\pi$, $D_n=2n+1$, whose arithmetic mean is $N+1$. Continuity and evenness follow from the finite cosine sums, so these are the continuous values at the removable singularities. The quotient has nonnegative numerator and denominator; the values at the singularities are positive. Each nonconstant cosine has integral zero on $[-\pi,\pi]$, hence $\int D_n=2\pi$ and $\int K_N=2\pi$. Finally, cosine decreases on $[0,\pi]$, so $1-\cos t\ge1-\cos\delta>0$ in the stated region, while the numerator is at most $2$. This proves the off-zero bound, including $\delta=\pi$ when the region is nonempty.

For each Fourier mode, change variables $u=x-t$ and use periodicity to move the resulting interval back to $[-\pi,\pi]$. This gives

$$
\frac1{2\pi}\int_{-\pi}^{\pi}e^{int}f(x-t)\,dt=c_n(f)e^{inx}.
$$

Sum over the finite symmetric set of modes to obtain the Dirichlet convolution, then average over $n=0,\ldots,N$. Periodic Riemann integrability extends to every finite interval, and affine reflection preserves it. Multiplication by a continuous kernel preserves the tagged Riemann integral. These facts construct the source integrals before identifying their values with the interval integrals. The same Fourier normalization also gives Parseval for any square-integrable function on an interval of length $2\pi$.

Evenness and total mass give $\int_0^\pi K_N=\pi$. The off-zero estimate implies that $K_N/\pi$ tends uniformly to zero outside every neighborhood of zero in $[-\pi,\pi]$. Thus the half-interval approximate-identity theorem applies: for any real Banach space $E$, integrable $g:(0,\pi]\to E$, and right limit $g(t)\to a$ at zero,

$$
\int_0^\pi\frac{K_N(t)}\pi g(t)\,dt\longrightarrow a.
$$

Indeed, near zero the difference $g-a$ is small and the kernel has mass at most one; away from zero its integral tends to zero by uniform kernel decay and integrability. Reflecting the negative half of the convolution gives

$$
\sigma_N(f;x)=\int_0^\pi\frac{K_N(t)}\pi\frac{f(x-t)+f(x+t)}2\,dt.
$$

For continuous $f$, apply the Banach-valued result with $E=C([-\pi,\pi],\mathbb C)$ and $g(t)(x)=(f(x-t)+f(x+t))/2$. Joint continuity and compactness make this a continuous map into the supremum norm, with $g(0)=f$. Convergence in that norm is the required uniform convergence.

**Lean declarations:** `Rudin.Chapter08.dirichletKernel_eq_int_sum`, `Rudin.Chapter08.exercise15_kernel_formula`, `Rudin.Chapter08.exercise15_kernel_at_multiple`, `Rudin.Chapter08.exercise15_continuous`, `Rudin.Chapter08.exercise15_nonnegative`, `Rudin.Chapter08.dirichletKernel_integral`, `Rudin.Chapter08.exercise15_mass`, `Rudin.Chapter08.exercise15_off_zero_bound`, `Rudin.Chapter08.fourierCoefficient_riemann`, `Rudin.Chapter08.fourierPartialSum_eq_int_sum`, `Rudin.Chapter08.fourier_mode_convolution`, `Rudin.Chapter08.fourierPartialSum_convolution`, `Rudin.Chapter08.exercise15_convolution`, `Rudin.Chapter08.periodic_riemann_reflected_source`, `Rudin.Chapter08.exercise15_convolution_riemann`, `Rudin.Chapter08.fourierPartialSum_convolution_riemann`, `Rudin.Chapter08.fejerKernel_even`, `Rudin.Chapter08.fejerKernel_half_mass`, `Rudin.Chapter08.fejerKernel_uniform_off_zero`, `Rudin.Chapter08.fejerKernel_half_limit`, `Rudin.Chapter08.fejerMean_half_convolution`, `Rudin.Chapter08.exercise15_uniform_fejer`, `Rudin.Chapter08.fourierMonomial_bridge`, `Rudin.Chapter08.fourierCoefficient_bridge`, `Rudin.Chapter08.source_parseval`.

<a id="r08e16"></a>
### 8.16 — Fejer convergence at a jump

**Lean source:** [Exercise16.lean](../../../Math/Rudin/Chapter08/Exercise16.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $f:\mathbb R\to\mathbb C$ be $2\pi$-periodic and Riemann integrable on $[-\pi,\pi]$. At any real $x$ where the finite one-sided limits $L=f(x-)$ and $R=f(x+)$ exist,

$$
\sigma_N(f;x)\longrightarrow\frac{L+R}{2}.
$$

This is a pointwise assertion at every such $x$, not an almost-everywhere assertion. At joins of periods the limits are those of the periodic function; its assigned value at $x$ need not equal either limit.

**Proof.** As $t\downarrow0$, the points $x-t$ approach $x$ from the left and $x+t$ approach it from the right. Consequently $g(t)=(f(x-t)+f(x+t))/2$ tends to $(L+R)/2$. The translated and reflected functions are integrable on $[0,\pi]$. Exercise 15 expresses $\sigma_N(f;x)$ as $\int_0^\pi(K_N/\pi)g$; its half-interval approximate-identity theorem gives the limit.

**Lean declarations:** `Rudin.Chapter08.exercise16_pointwise_fejer`.

<a id="r08e17"></a>
### 8.17 — Fourier convergence under monotonicity

**Lean source:** [Exercise17.lean](../../../Math/Rudin/Chapter08/Exercise17.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $f:\mathbb R\to\mathbb R$ be either nondecreasing or nonincreasing on $[-\pi,\pi)$, with $|f|\le M$ there. For every integer $n$, including zero and negative integers,

$$
|n c_n(f)|\le\frac{2M}{\pi}.
$$

For its $2\pi$-periodic extension $F$, both finite one-sided limits exist at every real $x$, and

$$
s_N(f;x)\longrightarrow\frac{F(x-)+F(x+)}2.
$$

In particular, this holds for already periodic $f$. More locally, suppose $f$ is Riemann integrable on $[-\pi,\pi]$, $-\pi\le\alpha<\beta\le\pi$, and $f$ is monotone in either direction on $(\alpha,\beta)$. At each $x$ in that open interval both one-sided limits exist and $s_N(f;x)$ tends to their average. No monotonicity outside that interval is required. Existence of the local one-sided limits uses only the local monotonicity, without the global Riemann-integrability assumption.

**Proof.** First let $f$ be nondecreasing on the closed fundamental interval. Apply the Chapter 6 Riemann–Stieltjes integration-by-parts theorem to $G(t)=e^{-int}$, whose modulus is one. It constructs the integrals and gives

$$
\int_{-\pi}^{\pi}f(t)G'(t)\,dt
=f(\pi)G(\pi)-f(-\pi)G(-\pi)-\int_{-\pi}^{\pi}G\,df.
$$

The last integral has modulus at most $f(\pi)-f(-\pi)\le2M$, and the two boundary terms contribute at most $2M$. Since $G'=-inG$, division by $2\pi$ gives the asserted bound. For half-open data set the missing right endpoint to $M$; this preserves monotonicity and the bound. Changing that single endpoint does not change any Fourier coefficient. Apply the increasing result to $-f$ for the decreasing case. The estimate is trivial at $n=0$.

Bounded monotone functions have finite endpoint and interior one-sided limits. Reduction modulo $2\pi$ and periodic translation transfer these limits to every real point, including the joined endpoints. They are also Riemann integrable: their interior discontinuities form a countable set, and endpoint changes do not affect integrability. Exercise 16 therefore gives convergence of the arithmetic Fourier means. If $S_N=s_N(f;x)$, the coefficient bound and $|e^{inx}|=1$ give

$$
|N(S_N-S_{N-1})|\le\frac{4M}{\pi}\quad(N\ge1).
$$

The bounded-increment Tauberian converse proved in Chapter 3, Exercise 14(e), then transfers convergence of the means to $S_N$ itself. This uses the valid final converse; the zero-bound correction to that earlier exercise's strict intermediate estimate does not require an additional assumption here.

For the local assertion, choose $\alpha<c<x<d<\beta$ and put $g(t)=f(\max(c,\min(d,t)))$. This is globally monotone, bounded on the fundamental interval, and equal to $f$ near $x$. Its Fourier sums have the asserted limit, and local equality identifies its two limits with those of $f$.

The proved localization result applies to interval-integrable complex functions $u,v$, an interior point $x\in(-\pi,\pi)$, a radius $\delta>0$ with $u=v$ whenever $|t-x|<\delta$, and a uniform bound on $|u-v|$ on the closed fundamental interval. Define $h(t)=(u(t)-v(t))/(1-\cos(x-t))$ away from that neighborhood and zero inside. The denominator is bounded away from zero on the remaining compact set, so $h$ is square integrable. The identity

$$
(1-\cos y)D_N(y)=\cos(Ny)-\cos((N+1)y)
$$

expresses $s_N(u;x)-s_N(v;x)$ as the difference of two normalized cosine integrals of $h$. Parseval implies that its Fourier coefficients tend to zero along both positive and negative frequencies, so both cosine integrals tend to zero. The boundedness required here follows for $f$ from its literal Riemann integrability and for $g$ from monotonicity. Localization completes the proof and also confirms existence of the local one-sided limits without assumptions at $\alpha$ or $\beta$.

**Lean declarations:** `Rudin.Chapter08.exercise17_coefficient_bound`, `Rudin.Chapter08.exercise17_bounded_coefficients`, `Rudin.Chapter08.exercise17_fourier_limit`, `Rudin.Chapter08.exercise17_one_sided_limits`, `Rudin.Chapter08.exercise17_pointwise`, `Rudin.Chapter08.exercise17_periodic_extension_limit`, `Rudin.Chapter08.exercise17_local_monotone`, `Rudin.Chapter08.exercise17_local_one_sided_limits`, `Rudin.Chapter08.exercise17_localization`.

<a id="r08e18"></a>
### 8.18 — Two strict trigonometric signs

**Lean source:** [Exercise18.lean](../../../Math/Rudin/Chapter08/Exercise18.lean).

**Inventory status:** Verified as stated.

**Statement.** Throughout $0<x<\pi/2$, both functions are strictly negative:

$$
x^3-\sin^2x\tan x<0,\qquad
2x^2-\sin^2x-x\tan x<0.
$$

**Proof.** Set $A(t)=\sin t-t\cos t$. It vanishes at zero and $A'(t)=t\sin t>0$, so $A(t)>0$ on the stated interval. Next set $B(t)=t(1+2\cos^2t)-3\sin t\cos t$. Again $B(0)=0$, while $B'(t)=4\sin t\,A(t)>0$, hence $B(t)>0$.

Use the continuous value $\operatorname{sinc}(0)=1$. For $0<t<\pi/2$, differentiation gives

$$
\frac{d}{dt}\frac{\operatorname{sinc}^3t}{\cos t}
=\frac{\sin^2t\,t^2 B(t)}{(t^3\cos t)^2}>0.
$$

The quotient is continuous from zero to $x$ because cosine is positive there, and its value at zero is $1$. Thus $\sin^3x/(x^3\cos x)>1$, proving the first strict sign.

Put $a=\sin^2x$ and $b=x\tan x$. Both are positive. Multiplication of the first inequality by $x>0$ gives $ab>x^4$. Since $(a-b)^2\ge0$, $(a+b)^2\ge4ab>4x^4$. Positivity of $a+b$ gives $a+b>2x^2$, which is the second strict sign. No endpoint assertion at $\pi/2$, where tangent is undefined, is used.

**Lean declarations:** `Rudin.Chapter08.exercise18_first_sign`, `Rudin.Chapter08.exercise18_second_sign`.

<a id="r08e19"></a>
### 8.19 — Means along an irrational rotation

**Lean source:** [Exercise19.lean](../../../Math/Rudin/Chapter08/Exercise19.lean).

**Inventory status:** Verified as stated.

**Statement.** If $f:\mathbb R\to\mathbb C$ is continuous and $2\pi$-periodic and $\alpha/\pi$ is irrational, then for every real $x$,

$$
\frac1N\sum_{n=1}^{N}f(x+n\alpha)
\longrightarrow\frac1{2\pi}\int_{-\pi}^{\pi}f(t)\,dt.
$$

The same statement holds for real-valued $f$. The displayed integral is also its tagged Riemann integral.

**Proof.** Regard $f$ as a continuous function on $\mathbb R/(2\pi\mathbb Z)$. The zero Fourier mode is constant, so its average and mean are both $1$. For a nonzero integer $k$, irrationality implies $q=e^{ik\alpha}\ne1$: otherwise $k\alpha=2\pi m$ for an integer $m$, making $\alpha/\pi$ rational. The geometric-sum formula gives

$$
\frac1N\sum_{n=1}^{N}e^{ik(x+n\alpha)}
=\frac{e^{ikx}q}{N}\frac{q^N-1}{q-1}\longrightarrow0,
$$

because $|q|=1$ and $|q^N-1|\le2$. This equals the period mean of the nonzero mode.

Both the rotation average and normalized period integral have operator norm at most one in the supremum norm. Their difference therefore has Lipschitz constant at most two, independently of $N$. Convergence to zero holds on the linear span of the Fourier modes, which is dense in the continuous functions on the circle. The uniform operator bound makes the set of functions with this convergence closed, so it contains every continuous function. Conversion of normalized Haar measure on the circle to an interval of length $2\pi$ gives the displayed mean. Taking real parts gives the real version. Continuity on the closed interval constructs the tagged Riemann value and identifies it with the interval integral. The harmless $N=0$ value of the formal sequence has no effect on its limit.

**Lean declarations:** `Rudin.Chapter08.exercise19_irrational_rotation_mean`, `Rudin.Chapter08.exercise19_real`, `Rudin.Chapter08.exercise19_riemann_integral`.

<a id="r08e20"></a>
### 8.20 — Factorial bounds from logarithmic graphs

**Lean source:** [Exercise20.lean](../../../Math/Rudin/Chapter08/Exercise20.lean).

**Inventory status:** Verified as stated.

**Statement.** Define a lower graph $F$ by the straight chord from $(m,\log m)$ to $(m+1,\log(m+1))$, and an upper graph $G$ by the tangent at $m$, restricted to $[m-1/2,m+1/2)$, for integers $m\ge1$. Explicitly,

$$
F(x)=(m+1-x)\log m+(x-m)\log(m+1)\quad(m\le x\le m+1),
$$

$$
G(x)=x/m-1+\log m\quad(m-1/2\le x<m+1/2).
$$

Then $F(x)\le\log x\le G(x)$ for $x\ge1$. For every integer $n\ge1$ the genuine Darboux integral values are

$$
\int_1^n F=\log(n!)-\tfrac12\log n,\qquad
\int_1^n G=\log(n!)-\tfrac12\log n+\tfrac18-\frac1{8n},
$$

$$
\int_1^n\log x\,dx=n\log n-n+1.
$$

For $n\ge2$ this gives $\int_1^n F>-1/8+\int_1^n G$ and

$$
\frac78<\log(n!)-(n+\tfrac12)\log n+n<1,
$$

$$
e^{7/8}<\frac{n!}{(n/e)^n\sqrt n}<e.
$$

**Proof.** The graphs can be specified globally using $m=\lfloor x\rfloor$ for $F$ and $m=\lfloor x+1/2\rfloor$ for $G$ on $x\ge1$. Adjacent chord formulas agree at integer endpoints. The upper cells are half-open and select exactly one tangent value at each join. Concavity of logarithm puts each chord below its graph, strictly below inside a unit interval. The inequality $\log u\le u-1$, applied to $u=x/m>0$, puts logarithm below the selected tangent.

The chord integral on $[m,m+1]$ is $(\log m+\log(m+1))/2$. Adding cells gives the formula for $\int F$. Split each interval $[m,m+1]$ at $m+1/2$ for $G$. Integrating its two affine pieces gives

$$
\int_m^{m+1}G=\frac{\log m+\log(m+1)}2+\frac1{8m}-\frac1{8(m+1)}.
$$

The correction telescopes. The finite endpoint changes in the tangent pieces do not affect the Darboux integral; boundedness and continuity except at those endpoints establish its existence. The formulas also cover $n=1$, where all integrals vanish. Their difference is $1/8-1/(8n)<1/8$, proving the strict integral comparison.

Integration of $F\le\log\le G$ is legitimate for these constructed integrals. The first comparison is strict for $n\ge2$, because $F<\log$ throughout $(1,2)$, a set of positive length. If $A_n=\log(n!)-(n+1/2)\log n+n$, the two comparisons give $A_n<1$ and $A_n\ge7/8+1/(8n)>7/8$. Finally the positive factorial ratio has logarithm $A_n$, using $\log\sqrt n=(\log n)/2$. Exponentiation gives the two ratio bounds. No Stirling asymptotic is needed.

**Lean declarations:** `Rudin.Chapter08.exercise20_lower_graph`, `Rudin.Chapter08.exercise20_upper_graph`, `Rudin.Chapter08.exercise20_log_bounds`, `Rudin.Chapter08.exercise20_lower_integral`, `Rudin.Chapter08.exercise20_upper_integral`, `Rudin.Chapter08.exercise20_integral_comparison`, `Rudin.Chapter08.exercise20_log_integral`, `Rudin.Chapter08.exercise20_log_factorial`, `Rudin.Chapter08.exercise20_factorial_ratio`.

<a id="r08e21"></a>
### 8.21 — Logarithmic growth of Dirichlet kernel norms

**Lean source:** [Exercise21.lean](../../../Math/Rudin/Chapter08/Exercise21.lean).

**Inventory status:** Verified as stated.

**Statement.** Put $L_n=(2\pi)^{-1}\int_{-\pi}^{\pi}|D_n(t)|\,dt$. For every integer $n\ge1$,

$$
\frac4{\pi^2}\log n<L_n,\qquad
0\le L_n-\frac4{\pi^2}\log n\le3+\frac4{\pi^2}.
$$

Thus the requested positive lower-bound constant can be $4/\pi^2$, and the error sequence is bounded in absolute value. More precisely, with $H_n=\sum_{j=1}^{n}1/j$, the source proves $4H_n/\pi^2\le L_n\le3+4H_n/\pi^2$ even for $n=0$.

**Proof.** The sine addition formulas and induction give $\sin(t/2)D_n(t)=\sin((n+1/2)t)$. For $0<u\le\pi/2$, elementary sine estimates imply

$$
0\le\frac1{\sin u}-\frac1u\le1.
$$

For the upper bound use $\sin u\ge u/2$ and $\sin u\ge u-u^3/6$, which imply $u-\sin u\le u\sin u$ in this range. Since $|\sin v|\le1$, multiplication gives

$$
(2n+1)|\operatorname{sinc}((2n+1)u)|
\le |D_n(2u)|
\le(2n+1)|\operatorname{sinc}((2n+1)u)|+1.
$$

Evenness and the change of variables $t=2u$ express $L_n$ as $(2/\pi)\int_0^{\pi/2}|D_n(2u)|\,du$. The main comparison integral becomes $\int_0^{(n+1/2)\pi}|\operatorname{sinc}v|\,dv$.

On each sine lobe $[k\pi,(k+1)\pi]$, $\int|\sin v|=2$. Dividing by the largest denominator gives a lower lobe bound $2/((k+1)\pi)$; for $k\ge1$, dividing by the smallest denominator gives an upper bound $2/(k\pi)$. The initial lobe is at most $\pi$ because $|\operatorname{sinc}|\le1$. Positivity permits comparison of the cutoff $(n+1/2)\pi$ with $n\pi$ and $(n+1)\pi$. Adding the lobe estimates and the additive kernel error gives precisely the stated harmonic bounds. All integrands used here are continuous at zero through the sinc value, so no singular integral is assumed.

Finally $\log(n+1)\le H_n\le1+\log n$ for $n\ge1$, and $\log n<\log(n+1)$. Substitution gives the strict logarithmic lower bound, including $n=1$, and the explicit two-sided error estimate. Nonnegativity of that error converts its upper bound into an absolute-value bound.

**Lean declarations:** `Rudin.Chapter08.e21_harmonic_bounds`, `Rudin.Chapter08.exercise21_log_lower_bound`, `Rudin.Chapter08.exercise21_error_bounds`, `Rudin.Chapter08.exercise21_bounded_error`.

<a id="r08e22"></a>
### 8.22 — The binomial series and its differential equation
**Lean source:** [Exercise22.lean](../../../Math/Rudin/Chapter08/Exercise22.lean).
**Inventory status:** Verified as stated.

**Statement.** For $\alpha\in\mathbb R$, define

$$
c_0=1,\qquad c_n=\frac{\alpha(\alpha-1)\cdots(\alpha-n+1)}{n!}\quad(n\ge1).
$$

For every $|x|<1$, the series $F(x)=\sum_{n\ge0}c_nx^n$ converges absolutely, and its ordered partial sums converge to $F(x)$. If $\alpha=m\in\mathbb N$, every coefficient with $n>m$ vanishes. The sum is differentiable on $(-1,1)$ and satisfies

$$
(1+x)F'(x)=\alpha F(x),\qquad F(0)=1.
$$

The unique differentiable solution of this equation with initial value one is $F(x)=(1+x)^\alpha$. Thus

$$
(1+x)^\alpha=1+\sum_{n\ge1}\frac{\alpha(\alpha-1)\cdots(\alpha-n+1)}{n!}x^n.
$$

For $\alpha>0$ and $-1<x<1$, the file also proves the absolutely convergent Gamma expansion

$$
(1-x)^{-\alpha}=\sum_{n\ge0}\frac{\Gamma(n+\alpha)}{n!\,\Gamma(\alpha)}x^n.
$$

Both identities include convergence of ordered partial sums. The endpoints $x=\pm1$ are not asserted. The bases $1+x$ and $1-x$ are positive throughout the stated interval.

**Proof.** The coefficient is the falling product divided by $n!$, with the empty product equal to one. If $\alpha=m\in\mathbb N$ and $n>m$, the factor with index $m$ is zero, so the series terminates. Otherwise its coefficients are nonzero and

$$
\frac{|c_{n+1}|}{|c_n|}=\frac{|\alpha-n|}{n+1}\longrightarrow1.
$$

For $0<|x|<1$, the ratio test gives absolute convergence; at $x=0$ only the constant term survives. Equivalently, the radius of convergence is at least one, which is the library result used in Lean. Absolute convergence supplies ordered convergence.

Inside that radius, the power-series differentiation theorem gives

$$
F'(x)=\sum_{n\ge0}(n+1)c_{n+1}x^n.
$$

The falling-product formula gives $(n+1)c_{n+1}=(\alpha-n)c_n$. Reindexing the absolutely convergent derivative series yields

$$
xF'(x)=\sum_{n\ge0}nc_nx^n.
$$

Add the two series term by term to obtain $(1+x)F'(x)=\alpha\sum_{n\ge0}c_nx^n=\alpha F(x)$. At zero the constant coefficient gives $F(0)=1$.

To solve the differential equation, let $f$ be any differentiable solution on $(-1,1)$ with $f(0)=1$. The product rule and the equation give

$$
\frac{d}{dx}\bigl(f(x)(1+x)^{-\alpha}\bigr)=0.
$$

The interval is connected, so this product is constant, and its value at zero is one. Since $(1+x)^\alpha>0$, this proves $f(x)=(1+x)^\alpha$. Apply this to the power-series sum to obtain the binomial identity.

Finally, for $\alpha>0$, positivity of $\Gamma(\alpha)$ and the recurrence $\Gamma(u+1)=u\Gamma(u)$ give

$$
(-1)^n\binom{-\alpha}{n}
=\frac{\alpha(\alpha+1)\cdots(\alpha+n-1)}{n!}
=\frac{\Gamma(n+\alpha)}{n!\,\Gamma(\alpha)}.
$$

For $n=0$ the empty product gives one. Substitute exponent $-\alpha$ and argument $-x$ into the binomial identity and use this coefficient formula. Its absolute convergence also gives the asserted ordered Gamma-series convergence.

**Lean declarations:** `exercise22_coefficient`, `exercise22_hasSum`, `exercise22_ordered_convergence`, `exercise22_terminates`, `exercise22_differentiable`, `exercise22_series_ode`, `exercise22_initial_value`, `exercise22_ode_unique`, `exercise22_binomial_identity`, `exercise22_newton`, `exercise22_gamma_hasSum`, `exercise22_gamma_series`.

<a id="r08e23"></a>
### 8.23 — Integral index and signed turns

**Lean source:** [Exercise23.lean](../../../Math/Rudin/Chapter08/Exercise23.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $a\le b$ and let $\gamma:[a,b]\to\mathbb C$ be closed and nowhere zero. Assume a continuous velocity $v$ gives its derivative within $[a,b]$ at every point, including the endpoints. Then

$$
\operatorname{Ind}(\gamma)=\frac1{2\pi i}\int_a^b\frac{v(t)}{\gamma(t)}\,dt\in\mathbb Z.
$$

The logarithmic derivative has a genuine tagged Riemann integral on the whole interval and every closed subinterval. Its integral index agrees with that computed using the canonical within derivative. For every integer $n$, the curve $e^{int}$ on $[0,2\pi]$ has index $n$, including $n=0$ and negative $n$. There exist continuous real functions $\rho>0$ and $\theta$ on $[a,b]$, with $\theta(a)=0$, such that

$$
\gamma(t)=\gamma(a)\rho(t)e^{i\theta(t)},\qquad
\theta(b)-\theta(a)=2\pi\operatorname{Ind}(\gamma).
$$

**Proof.** The derivative assumption makes $\gamma$ continuous; nonvanishing makes $v/\gamma$ continuous. This constructs its tagged Riemann integrals and identifies them with the interval integrals, also on every ordered subinterval. Put $\Phi(t)=\int_a^t v/\gamma$. The fundamental theorem of calculus supplies its within derivative $v/\gamma$, so differentiation gives

$$
\frac{d}{dt}\bigl(\gamma(t)e^{-\Phi(t)}\bigr)=0.
$$

The zero-derivative theorem on a segment makes this product equal to $\gamma(a)$. At $b$, closure and $\gamma(a)\ne0$ imply $e^{\Phi(b)}=1$. The kernel of the complex exponential is $2\pi i\mathbb Z$, hence $\Phi(b)=2\pi i n$ and the index is the integer $n$.

For $e^{int}$ the continuous velocity is $in e^{int}$; its logarithmic derivative is the constant $in$, whose integral is $2\pi i n$. This verifies closure and the index for every integer sign. For the polar representation take $\rho(t)=e^{\operatorname{Re}\Phi(t)}$ and $\theta(t)=\operatorname{Im}\Phi(t)$. The product identity gives the representation, and $\Phi(b)=2\pi i n$ gives the total angular change. Thus positive and negative indices count net turns in opposite orientations, while zero means zero net angular change, not necessarily a constant curve.

On a nondegenerate interval uniqueness of the within derivative identifies $v$ with that derivative. If $a=b$, the integral is zero independently of the nonunique derivative jet, and the index is zero; the same representation has $\rho(a)=1$ and $\theta(a)=0$.

**Lean declarations:** `Rudin.Chapter08.exercise23_integer_index`, `Rudin.Chapter08.IsC1NonzeroLoop.riemann_logDerivative`, `Rudin.Chapter08.IsC1NonzeroLoop.riemann_logDerivative_subinterval`, `Rudin.Chapter08.IsC1NonzeroLoop.index_eq_riemann_value`, `Rudin.Chapter08.IsC1NonzeroLoop.index_eq_derivWithin`, `Rudin.Chapter08.IsC1NonzeroLoop.primitive_derivative`, `Rudin.Chapter08.IsC1NonzeroLoop.primitive_identity`, `Rudin.Chapter08.IsC1NonzeroLoop.exp_integral_eq_one`, `Rudin.Chapter08.exercise23_circle`, `Rudin.Chapter08.exercise23_signed_turns`.

<a id="r08e24"></a>
### 8.24 — Zero index in the slit plane

**Lean source:** [Exercise24.lean](../../../Math/Rudin/Chapter08/Exercise24.lean).

**Inventory status:** Verified as stated.

**Statement.** A closed nonzero curve on $[a,b]$, $a\le b$, with a continuous within derivative as in Exercise 23 has index zero if its entire range is in $\mathbb C\setminus(-\infty,0]$.

**Proof.** The principal logarithm is differentiable on this slit plane. The chain rule gives within derivative $v(t)/\gamma(t)$ for $\log\gamma(t)$. The fundamental theorem of calculus, using the continuous logarithmic derivative, gives

$$
\int_a^b\frac{v(t)}{\gamma(t)}\,dt
=\log\gamma(b)-\log\gamma(a)=0.
$$

The endpoint equality uses closure and the same single-valued logarithm throughout. Normalizing by $2\pi i$ gives index zero, also on a singleton interval.

**Lean declarations:** `Rudin.Chapter08.exercise24_zero_index`.

<a id="r08e25"></a>
### 8.25 — Stability of the index under a strict perturbation

**Lean source:** [Exercise25.lean](../../../Math/Rudin/Chapter08/Exercise25.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $\gamma_1,\gamma_2$ be closed nonzero curves on the same ordered interval $[a,b]$, each with a continuous within derivative $v_1,v_2$. If

$$
|\gamma_1(t)-\gamma_2(t)|<|\gamma_1(t)|\quad(a\le t\le b),
$$

then their indices are equal. More generally, the index of their quotient is the difference of their indices.

**Proof.** The quotient $q=\gamma_2/\gamma_1$ is again a closed nonzero curve with continuous within derivative

$$
q'=\frac{v_2\gamma_1-\gamma_2v_1}{\gamma_1^2},\qquad
\frac{q'}q=\frac{v_2}{\gamma_2}-\frac{v_1}{\gamma_1}.
$$

All denominators are nonzero. Integration proves $\operatorname{Ind}(q)=\operatorname{Ind}(\gamma_2)-\operatorname{Ind}(\gamma_1)$. The strict hypothesis gives $|1-q(t)|<1$, and therefore $\operatorname{Re}q(t)>0$. Thus the quotient lies in the slit plane and Exercise 24 gives its index zero. Subtraction proves the claim.

**Lean declarations:** `Rudin.Chapter08.IsC1NonzeroLoop.div`, `Rudin.Chapter08.curveIndex_div`, `Rudin.Chapter08.quotient_mem_slitPlane`, `Rudin.Chapter08.exercise25_index_stability`.

<a id="r08e26"></a>
### 8.26 — The index of a continuous loop

**Lean source:** [Exercise26.lean](../../../Math/Rudin/Chapter08/Exercise26.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $\gamma:[0,2\pi]\to\mathbb C$ be continuous, closed, and nowhere zero. There is $\delta>0$ with $|\gamma(t)|>\delta$ everywhere, and a finite complex trigonometric polynomial $P(t)=\sum_k a_ke^{ikt}$ with $|P(t)-\gamma(t)|<\delta/4$ throughout the closed interval. Such polynomials are closed, continuously differentiable, and nonzero. Their integral indices agree, independently of both the polynomial and the admissible $\delta$. This common integer defines $\operatorname{Ind}(\gamma)$.

It agrees with the integral index when $\gamma$ has a continuous within derivative. Without any derivative assumption, a loop in the slit plane has index zero, and two continuous nonzero loops have equal indices under the strict perturbation condition of Exercise 25. Arbitrarily accurate polynomial approximations can also satisfy $|P-\gamma|<|\gamma|/4$ pointwise. Uniform trigonometric approximation itself needs only continuity and equal endpoint values, not nonvanishing.

**Proof.** Compactness gives a positive minimum of $|\gamma|$; half that minimum is an admissible $\delta$. Identify the two interval endpoints to obtain a continuous function on the circle. Density of the linear span of the integer Fourier modes produces an actual finite trigonometric polynomial within any specified positive uniform error, including at the identified endpoints. Differentiating the finite sum gives continuous velocity $\sum_k a_k ik e^{ikt}$. The quarter-norm estimate excludes zero.

If $p,q$ both approximate $z$ with errors less than $|z|/4$, then

$$
|p-q|<|z|/2<|p|,
$$

where the last inequality follows from $|p|>3|z|/4$. Exercise 25 therefore equates the integral indices of any two such polynomials. Every admissible $\delta/4$ approximation meets this relative estimate, even if the two chosen deltas differ. Choose one polynomial and take the integer supplied by Exercise 23; the equality just proved makes the definition independent of the choices. The same comparison works for any smooth quarter-norm approximation. Taking the smooth curve to be $\gamma$ itself proves agreement with its integral index.

If the range of $\gamma$ is in the slit plane, its compact image has a uniform neighborhood still in that open set. Choose the polynomial both inside this neighborhood and within the relative quarter-norm bound. Exercise 24 gives its integral index zero, hence the continuous index is zero.

For two strictly close loops, the positive continuous margin $m(t)=|\gamma_1(t)|-|\gamma_1(t)-\gamma_2(t)|$ has a positive uniform lower bound $\varepsilon$. Choose approximants $P,Q$ each within $\varepsilon/4$ of its loop and within its relative quarter-norm bound. Triangle inequalities give $|P-Q|<|P|$: the loss from the two approximation errors and the lower estimate for $|P|$ is less than $3\varepsilon/4<m(t)$. Smooth stability equates their integral indices, and each computes its original loop's continuous index.

**Lean declarations:** `Rudin.Chapter08.exercise26_trigonometric_approximation`, `Rudin.Chapter08.IsContinuousNonzeroLoop.approximants`, `Rudin.Chapter08.IsContinuousNonzeroLoop.close_polynomial`, `Rudin.Chapter08.exercise26_approximant_index`, `Rudin.Chapter08.exercise26_independence`, `Rudin.Chapter08.continuousCurveIndex_spec`, `Rudin.Chapter08.continuousCurveIndex_eq_smooth`, `Rudin.Chapter08.exercise26_smooth_agreement`, `Rudin.Chapter08.exercise26_negative_axis_extension`, `Rudin.Chapter08.exercise26_perturbation_extension`.

<a id="r08e27"></a>
### 8.27 — A zero forced by positive asymptotic degree

**Lean source:** [Exercise27.lean](../../../Math/Rudin/Chapter08/Exercise27.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $f:\mathbb C\to\mathbb C$ be continuous. Suppose $n$ is a positive integer, $c\ne0$, and

$$
z^{-n}f(z)\longrightarrow c\quad\text{as }|z|\longrightarrow\infty.
$$

Then $f$ has a zero. Under the hypothetical assumption that $f$ is nowhere zero, the loops $\gamma_r(t)=f(re^{it})$, $0\le t\le2\pi$, satisfy: $\operatorname{Ind}(\gamma_0)=0$; $\operatorname{Ind}(\gamma_r)=n$ for every sufficiently large positive $r$; and their integer index is continuous on $[0,\infty)$.

**Proof.** A continuous family of nonzero loops has continuous, in fact locally constant, index. To prove this, fix one loop and a positive uniform lower bound $\delta$ for its modulus. Joint continuity on the compact parameter interval gives nearby loops within $\delta$ in the supremum norm. Exercise 26's strict perturbation theorem equates their indices. This argument applies to any topological family parameter space with the stated joint continuity. A constant nonzero loop has index zero by smooth agreement and zero velocity; this does not require its constant value to avoid the negative axis. These facts prove the zero-radius assertion and continuity of the radial index.

The asymptotic hypothesis is used in its equivalent epsilon-radius form. Choose the error $|c|$. For every sufficiently large $r>0$ and every $z=re^{it}$,

$$
|f(z)-cz^n|=|z|^n|z^{-n}f(z)-c|<|c|\,|z|^n=|cz^n|.
$$

The comparison loop is $cr^ne^{int}$. Multiplication of the integer-speed circle by a nonzero constant cancels in the logarithmic derivative, so its index is $n$. Continuous perturbation stability gives the same index for $\gamma_r$. This proves the large-radius fact directly from the estimate, without using the eventual contradiction.

Finally $[0,\infty)$ is connected, and a continuous integer-valued function on it is constant. Its value at zero is $0$, but its value at a sufficiently large radius is $n>0$, a contradiction. Therefore some $z$ satisfies $f(z)=0$. The formal result includes both the epsilon-radius and filter-limit formulations of the hypothesis.

**Lean declarations:** `Rudin.Chapter08.continuous_family_index`, `Rudin.Chapter08.continuousCurveIndex_const`, `Rudin.Chapter08.scaled_circle_index`, `Rudin.Chapter08.exercise27_a`, `Rudin.Chapter08.exercise27_b`, `Rudin.Chapter08.hasPositiveAsymptoticDegree_iff`, `Rudin.Chapter08.exercise27_c`, `Rudin.Chapter08.exercise27_zero_existence`, `Rudin.Chapter08.exercise27_index_facts`, `Rudin.Chapter08.exercise27_zero_of_tendsto`.

<a id="r08e28"></a>
### 8.28 — An antipodal value on the boundary

**Lean source:** [Exercise28.lean](../../../Math/Rudin/Chapter08/Exercise28.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $D=\{z\in\mathbb C:|z|\le1\}$ and $T=\{z:|z|=1\}$, with their induced topologies. For every continuous $g:D\to T$, there is a boundary point $z\in T$ such that $g(z)=-z$.

**Proof.** Suppose no boundary point has that property. The loops $H_r(t)=g(re^{it})$, $0\le r\le1$, are continuous, closed, and have modulus one. Their indices vary continuously with $r$, hence are constant. At $r=0$ the loop is constant, so every $H_r$ has index zero.

Write $E(t)=e^{it}$, whose index is one. On the boundary $H_1(t)\ne-E(t)$. For unit vectors $w,z$, the identity

$$
|w-z|^2+|w+z|^2=4
$$

shows that non-antipodality implies $|w-z|<2$. Thus the midpoint loop $M=(H_1+E)/2$ is nonzero and satisfies both

$$
|E-M|<|E|=1,\qquad |H_1-M|<|H_1|=1.
$$

Apply continuous index stability first to $E,M$ and then to $H_1,M$. It gives $\operatorname{Ind}(H_1)=\operatorname{Ind}(E)=1$, contradicting the radial index zero. The contradiction concerns the boundary loop, so the resulting witness has modulus exactly one, not merely at most one.

**Lean declarations:** `Rudin.Chapter08.unit_distance_lt_two`, `Rudin.Chapter08.exercise28_boundary_antipode`.

<a id="r08e29"></a>
### 8.29 — A disc fixed point from the ray construction

**Lean source:** [Exercise29.lean](../../../Math/Rudin/Chapter08/Exercise29.lean).

**Inventory status:** Verified as stated.

**Statement.** Every continuous $f:D\to D$ has a fixed point. Under the contrary assumption, the ray starting at $f(z)$ and passing through $z$ defines a continuous boundary map $g:D\to T$ with $g(z)=z$ on $T$. Its explicit parameter and uniqueness include boundary inputs.

**Proof.** For distinct $z,w\in D$, put

$$
A=|w-z|^2>0,\qquad B=\operatorname{Re}(\overline z(w-z)),\qquad C=|z|^2-1\le0.
$$

Expansion gives

$$
|z-s(w-z)|^2-1=As^2-2Bs+C,\qquad A+2B+C=|w|^2-1\le0.
$$

These coefficient conditions imply that the unique nonnegative quadratic root is

$$
s=\frac{B+\sqrt{B^2-AC}}A.
$$

Indeed, the discriminant is nonnegative, $\sqrt{B^2-AC}\ge-B$, and $\sqrt{B^2-AC}>B$. For $C<0$ the last inequality follows from $-AC>0$; for $C=0$ the geometric bound gives $B\le-A/2<0$. The other root is therefore negative. Equivalently, subtracting the root equations factors their difference by $A(t+s)-2B>0$ for $t\ge0$, proving uniqueness without a division by zero. Thus $g=z-s(w-z)$ is the unique circle intersection with a nonnegative parameter. Also $g=w+(1+s)(z-w)$ with $1+s\ge1$, so it is on the specified ray beyond or at $z$.

Assume $f$ has no fixed point and take $w=f(z)$. Then $A(z)>0$ everywhere. The displayed root formula uses continuous coefficients, the continuous square root, and a nonzero denominator. Consequently $s(z)$ and $g(z)$ are continuous, and the quadratic identity gives $|g(z)|=1$. If $|z|=1$, then $C=0$ and $s=0$ is a nonnegative root; uniqueness gives $g(z)=z$. This explicitly covers the boundary case, where an arbitrary choice between quadratic roots would be insufficient.

Exercise 28 supplies a boundary point with $g(z)=-z$. The boundary identity gives $z=-z$, hence $z=0$, contradicting $|z|=1$. Therefore $f$ has a fixed point. No library fixed-point theorem is used.

**Lean declarations:** `Rudin.Chapter08.exercise29_ray_boundary_map`, `Rudin.Chapter08.rayRoot_unique`, `Rudin.Chapter08.ray_coefficients`, `Rudin.Chapter08.ray_quadratic`, `Rudin.Chapter08.rayBoundaryPoint_on_ray`, `Rudin.Chapter08.exercise29_ray_map_continuity`, `Rudin.Chapter08.exercise29_ray_boundary_identity`, `Rudin.Chapter08.exercise29_disc_fixed_point`.

<a id="r08e30"></a>
### 8.30 — A Gamma ratio for every real shift

**Lean source:** [Exercise30.lean](../../../Math/Rudin/Chapter08/Exercise30.lean).

**Inventory status:** Verified as stated.

**Statement.** For every fixed real $c$,

$$
\frac{\Gamma(x+c)}{x^c\Gamma(x)}\longrightarrow1\quad(x\longrightarrow+\infty).
$$

On the explicit eventual domain $x>\max(0,-c)$, both Gamma arguments and the complete denominator are positive. The proof also establishes real-argument logarithmic Stirling asymptotics:

$$
R(x)=\log\Gamma(x+1)-(x+\tfrac12)\log x+x
\longrightarrow\log\sqrt\pi+\tfrac12\log2.
$$

**Proof.** At positive integer $n$, the library factorial Stirling sequence gives $R(n)=\log(\mathrm{stirlingSeq}(n))+(\log2)/2$ and $\mathrm{stirlingSeq}(n)\to\sqrt\pi$. To pass to real arguments, log-convexity of Gamma and $\Gamma(x+1)=x\Gamma(x)$ give, for $n\ge1$ and $0\le t\le1$,

$$
t\log n\le\log\Gamma(n+t+1)-\log\Gamma(n+1)\le t\log(n+1).
$$

Together with $1-u^{-1}\le\log u\le u-1$ for $u>0$, these bounds imply $|R(n+t)-R(n)|\le2/n$. Taking $n=\lfloor x\rfloor$ transfers the integer limit to all real $x\to\infty$.

On the positive eventual domain, Gamma recurrence and logarithm rules now give the exact identity

$$
\log\frac{\Gamma(x+c)}{x^c\Gamma(x)}
=R(x+c)-R(x)+x\log(1+c/x)
+(c-\tfrac12)\log(1+c/x)-c.
$$

The two remainders have the same limit. Also $\log(1+c/x)\to0$ and the standard logarithmic limit gives $x\log(1+c/x)\to c$. Thus the logarithm of the ratio tends to zero. Positivity permits exponentiation, proving the ratio limit. Negative shifts and $c=0$ require no separate restriction beyond the eventual domain.

**Lean declarations:** `Rudin.Chapter08.Exercise30.logGamma_interpolation`, `Rudin.Chapter08.Exercise30.remainder_interpolation`, `Rudin.Chapter08.Exercise30.tendsto_logStirlingRemainder`, `Rudin.Chapter08.Exercise30.eventually_gamma_ratio_domain`, `Rudin.Chapter08.Exercise30.log_gamma_ratio_eq`, `Rudin.Chapter08.Exercise30.exercise30_gamma_ratio`.

<a id="r08e31"></a>
### 8.31 — A scaled polynomial integral

**Lean source:** [Exercise31.lean](../../../Math/Rudin/Chapter08/Exercise31.lean).

**Inventory status:** Verified as stated.

**Statement.** For every natural $n$, the polynomial integral exists and has value

$$
I_n=\int_{-1}^{1}(1-x^2)^n\,dx
=\frac{\sqrt\pi\,\Gamma(n+1)}{\Gamma(n+3/2)}.
$$

This is also its Darboux and tagged Riemann value, including $n=0$. As $n\to\infty$ through positive integers,

$$
\sqrt n\,I_n\longrightarrow\sqrt\pi.
$$

The same limit holds for any sequence of literal tagged Riemann values of these integrands, and also when the sequence is indexed by all natural numbers.

**Proof.** The beta integral identity of Theorem 8.20 at the positive arguments $n+1,n+1$ gives

$$
\int_0^1t^n(1-t)^n\,dt
=\frac{\Gamma(n+1)^2}{\Gamma(2n+2)}.
$$

The integrand is a continuous polynomial, so integrability is established separately. The affine substitution $x=2t-1$ gives $I_n=2\cdot4^n\int_0^1t^n(1-t)^n\,dt$. Legendre's duplication formula at $n+1$, with all Gamma denominators positive, reduces this to the stated expression for $I_n$. Continuity on $[-1,1]$ also constructs both source Riemann values and identifies them with this integral; at $n=0$ the value is $2$.

For $n>0$, Gamma recurrence and $n^{3/2}=n\sqrt n$ yield

$$
\sqrt n\,I_n
=\sqrt\pi\left(\frac{\Gamma(n+3/2)}{n^{3/2}\Gamma(n)}\right)^{-1}.
$$

Exercise 30 with $c=3/2$, restricted to the natural-number sequence, makes the ratio tend to $1$. Its inverse also tends to $1$, proving the scaled limit. Omitting the single index zero gives the positive-integer formulation. Uniqueness and the proved Riemann-to-interval integral comparison identify any sequence of tagged values with $I_n$, so that formulation has the same limit.

**Lean declarations:** `Rudin.Chapter08.Exercise31.beta_integral_nat`, `Rudin.Chapter08.Exercise31.integral_affine_beta`, `Rudin.Chapter08.Exercise31.integral_eq_gamma`, `Rudin.Chapter08.Exercise31.integral_integrable`, `Rudin.Chapter08.Exercise31.integral_riemann_value`, `Rudin.Chapter08.Exercise31.scaled_integral_eq_ratio`, `Rudin.Chapter08.Exercise31.exercise31_scaled_integral_limit_nat`, `Rudin.Chapter08.Exercise31.exercise31_scaled_integral_limit`, `Rudin.Chapter08.Exercise31.exercise31_riemann_limit`.
