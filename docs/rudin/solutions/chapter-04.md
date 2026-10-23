<a id="chapter-04"></a>

# Chapter 4 — Continuity

[All chapters](../solutions.md) · [Previous chapter](chapter-03.md) · [Next chapter](chapter-05.md)

**Exercises:** [1](#r04e01) · [2](#r04e02) · [3](#r04e03) · [4](#r04e04) · [5](#r04e05) · [6](#r04e06) · [7](#r04e07) · [8](#r04e08) · [9](#r04e09) · [10](#r04e10) · [11](#r04e11) · [12](#r04e12) · [13](#r04e13) · [14](#r04e14) · [15](#r04e15) · [16](#r04e16) · [17](#r04e17) · [18](#r04e18) · [19](#r04e19) · [20](#r04e20) · [21](#r04e21) · [22](#r04e22) · [23](#r04e23) · [24](#r04e24) · [25](#r04e25) · [26](#r04e26)

<a id="r04e01"></a>
### 4.1 — Symmetric differences do not imply continuity
**Lean source:** [Exercise01.lean](../../../Math/Rudin/Chapter04/Exercise01.lean).
**Inventory status:** Verified as stated.

**Statement.** The condition

$$
\lim_{h\to0}\bigl(f(x+h)-f(x-h)\bigr)=0\qquad(x\in\mathbb R)
$$

does not imply that $f:\mathbb R\to\mathbb R$ is continuous.

**Proof.** Set $f(0)=1$ and $f(x)=0$ for $x\ne0$. At $x=0$, the symmetric difference is zero for every $h$. At $x\ne0$, it is zero whenever $|h|<|x|$, since neither $x+h$ nor $x-h$ is zero. Thus even the unpunctured limit holds at every $x$. Nevertheless, $f(h)=0$ for every nonzero $h$, whereas $f(0)=1$, so $f$ is not continuous at zero.

**Lean declarations:** `exercise01_symmetric_difference_converse`.

<a id="r04e02"></a>
### 4.2 — Images of closures
**Lean source:** [Exercise02.lean](../../../Math/Rudin/Chapter04/Exercise02.lean).
**Inventory status:** Verified as stated.

**Statement.** If $f:X\to Y$ is continuous between metric spaces and $E\subseteq X$, then

$$
f(\overline E)\subseteq\overline{f(E)}.
$$

The inclusion can be strict.

**Proof.** The closed set $f^{-1}(\overline{f(E)})$ contains $E$, so it contains $\overline E$. This proves the inclusion. For strictness, take $X=Y=\mathbb R$, $E=\mathbb R$, and $f(x)=e^x$. Then $f(\overline E)=(0,\infty)$, while $\overline{f(E)}=[0,\infty)$.

**Lean declarations:** `exercise02_closure_image_inclusion`, `exercise02_strict_inclusion`.

<a id="r04e03"></a>
### 4.3 — Closed zero sets
**Lean source:** [Exercise03.lean](../../../Math/Rudin/Chapter04/Exercise03.lean).
**Inventory status:** Verified as stated.

**Statement.** For a continuous real function $f$ on a metric space $X$, the set $\{p\in X:f(p)=0\}$ is closed.

**Proof.** The singleton $\{0\}$ is closed in $\mathbb R$, and the stated set is its inverse image under the continuous map $f$.

**Lean declarations:** `exercise03_zero_set_closed`.

<a id="r04e04"></a>
### 4.4 — Continuous maps on dense sets
**Lean source:** [Exercise04.lean](../../../Math/Rudin/Chapter04/Exercise04.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $f,g:X\to Y$ be continuous maps between metric spaces, and let $E$ be dense in $X$. Then $f(E)$ is dense in the subspace $f(X)$. If $f=g$ on $E$, then $f=g$ on $X$.

**Proof.** Since $\overline E=X$, Exercise 4.2 gives $f(X)\subseteq\overline{f(E)}$, where this closure is taken in $Y$. Intersecting with $f(X)$ proves density in the range, not necessarily in all of $Y$. The equalizer $\{x:f(x)=g(x)\}$ is closed, because the diagonal of the metric space $Y$ is closed. If it contains $E$, it contains $\overline E=X$.

**Lean declarations:** `exercise04_image_density`, `exercise04_dense_uniqueness`.

<a id="r04e05"></a>
### 4.5 — Extension from a closed set
**Lean source:** [Exercise05.lean](../../../Math/Rudin/Chapter04/Exercise05.lean).
**Inventory status:** Verified as stated.

**Statement.** If $E\subseteq\mathbb R$ is closed and $f:E\to\mathbb R$ is continuous, there is a continuous $g:\mathbb R\to\mathbb R$ with $g|_E=f$. The same conclusion holds for values in $\mathbb R^k$, including $k=0$. Closedness of $E$ cannot be omitted.

**Scope.** The Lean results also allow any metric space $X$ in place of the ambient real line. They use the Tietze extension theorem rather than the suggested piecewise-affine construction. Empty closed domains are included.

**Proof.** A metric space is normal. The real-valued Tietze extension theorem therefore extends every continuous $f:E\to\mathbb R$ from a closed subset to the whole space, with no boundedness assumption on $f$. For $E=\varnothing$, one may simply take $g=0$. For an $\mathbb R^k$-valued function, extend each continuous coordinate by this theorem and assemble the extensions. Continuity of the coordinates gives continuity in the Euclidean topology. In dimension zero there is only one possible value.

For failure without closedness, take $E=(0,\infty)$ and $f(x)=1/x$. This is continuous on $E$, which is not closed because $0\in\overline E\setminus E$. If a continuous extension $g$ existed, the closed set $\{x:xg(x)=1\}$ would contain $(0,\infty)$ and hence zero. This would imply $0=1$.

**Lean declarations:** `exercise05_real_extension`, `exercise05_nonclosed_failure`, `exercise05_vector_extension`.

<a id="r04e06"></a>
### 4.6 — Compact graphs and continuity
**Lean source:** [Exercise06.lean](../../../Math/Rudin/Chapter04/Exercise06.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $E$ be a compact metric space, $Y$ a metric space, and $f:E\to Y$ any map. Then $f$ is continuous if and only if its graph

$$
\Gamma_f=\{(x,f(x)):x\in E\}\subseteq E\times Y
$$

is compact. The empty domain is allowed. The implication from compact graph to continuity does not require a separate compactness assumption on $E$.

**Proof.** If $f$ is continuous, the map $x\mapsto(x,f(x))$ is continuous, so its image of the compact domain is compact. Conversely, suppose $\Gamma_f$ is compact. For every closed $F\subseteq Y$, the set $\Gamma_f\cap(E\times F)$ is compact. Its projection onto $E$ is exactly $f^{-1}(F)$, hence is compact and therefore closed in the metric space $E$. The closed-inverse-image criterion proves continuity.

**Lean declarations:** `exercise06_continuous_graph_compact`, `exercise06_compact_graph_continuous`, `exercise06_graph_equivalence`.

<a id="r04e07"></a>
### 4.7 — Continuity on lines is insufficient
**Lean source:** [Exercise07.lean](../../../Math/Rudin/Chapter04/Exercise07.lean).
**Inventory status:** Verified as stated.

**Statement.** Define $f(0,0)=g(0,0)=0$ and, away from the origin, set

$$
f(x,y)=\frac{xy^2}{x^2+y^4},\qquad g(x,y)=\frac{xy^2}{x^2+y^6}.
$$

Then $|f|\le\tfrac12$ on $\mathbb R^2$, but $f$ is not continuous at the origin. For every neighborhood $U$ of the origin and every real $M$, some $p\in U$ satisfies $|g(p)|>M$. Nevertheless, the restriction of each function to every affine straight line is continuous everywhere on that line.

**Proof.** The denominators are positive away from the origin. The inequality

$$
0\le(|x|-y^2)^2=x^2+y^4-2|x|y^2
$$

gives $|f(x,y)|\le\tfrac12$ there, and the same bound holds at zero. It also bounds the distance between any two values by $1$, so the range is bounded. Along $(x,y)=(t^2,t)$ with $t\ne0$, $f=\tfrac12$, which contradicts continuity at the origin. Along $(x,y)=(t^3,t)$, $g=1/(2t)$. Taking positive $t$ sufficiently small puts this point in any prescribed $U$ and makes $|g|$ larger than any prescribed $M$.

Both functions are continuous away from the origin by the quotient rule for continuous functions. For a line through the origin with direction $v=(a,b)$, if $a=0$ both restrictions are identically zero. If $a\ne0$, cancellation gives, including their assigned values at $t=0$,

$$
f(ta,tb)=\frac{ab^2t}{a^2+t^2b^4},\qquad
 g(ta,tb)=\frac{ab^2t}{a^2+t^4b^6}.
$$

Both expressions are continuous at zero. An affine line that reaches zero at parameter $c$ can be written there as $(t-c)v$, so this argument applies at that point as well. All its other points use ordinary continuity away from zero. For $v\ne0$, one nonzero coordinate recovers the parameter continuously by $t=(p_i-a_i)/v_i$; thus the result is also continuity in the line's subspace topology. The case $v=0$ is a singleton and is immediate.

**Lean declarations:** `exercise07_f_bounded`, `exercise07_f_range_bounded`, `exercise07_g_locally_unbounded`, `exercise07_f_discontinuous`, `exercise07_f_line_continuity`, `exercise07_f_line_restriction`, `exercise07_g_line_continuity`, `exercise07_g_line_restriction`.

<a id="r04e08"></a>
### 4.8 — Uniform continuity on a bounded real domain
**Lean source:** [Exercise08.lean](../../../Math/Rudin/Chapter04/Exercise08.lean).
**Inventory status:** Verified as stated.

**Statement.** If $E\subseteq\mathbb R$ is bounded and $f:E\to\mathbb R$ is uniformly continuous, then $f(E)$ is bounded. Equivalently, this holds for a real function uniformly continuous on $E$. It can fail when $E$ is unbounded.

**Proof.** A bounded subset of $\mathbb R$ is totally bounded: its closure is compact. Choose a uniform-continuity radius $\delta>0$ for output tolerance $1$. A finite collection of $\delta$-balls with centers in $E$ covers $E$, so the values of $f$ lie within distance $1$ of finitely many center values. This is a bounded set. If $E$ is empty, its image is empty and bounded. Without boundedness, use $E=\mathbb R$ and $f(x)=x$: the identity is uniformly continuous, but both domain and image are unbounded.

**Lean declarations:** `exercise08_bounded_image`, `exercise08_bounded_image_on`, `exercise08_unbounded_domain`.

<a id="r04e09"></a>
### 4.9 — Uniform continuity through diameters
**Lean source:** [Exercise09.lean](../../../Math/Rudin/Chapter04/Exercise09.lean).
**Inventory status:** Verified as stated.

**Statement.** For metric spaces $X,Y$ and a map $f:X\to Y$, uniform continuity is equivalent to the following condition: for every real $\varepsilon>0$ there is a real $\delta>0$ such that, for every subset $E\subseteq X$,

$$
\operatorname{diam}E<\delta\quad\Longrightarrow\quad
\operatorname{diam}f(E)<\varepsilon.
$$

**Diameter convention.** The source's earlier diameter definition covers nonempty sets only. To make the displayed all-subsets condition precise, use the extended nonnegative diameter

$$
\operatorname{diam}E=\sup\{d(x,y):x,y\in E\}\in[0,\infty],
$$

with $\operatorname{diam}\varnothing=0$ and diameter $\infty$ for unbounded sets. For every nonempty bounded $E$, this equals the ordinary real supremum in the source, embedded in $[0,\infty]$. This is a notation extension, not a refutation. In particular, an unbounded set is not assigned real diameter zero.

**Proof.** The supremum of the empty family in $[0,\infty]$ is zero. If the pairwise distances of a nonempty set had a finite upper bound, fixing one point would put the entire set in a bounded ball. Thus an unbounded set has infinite extended diameter. For a nonempty bounded set, its pairwise-distance set is nonempty, bounded above, and nonnegative. Its real least upper bound is therefore also its least upper bound in $[0,\infty]$, proving agreement with the source definition.

Suppose $f$ is uniformly continuous. Given $\varepsilon>0$, choose $\delta>0$ for output tolerance $\varepsilon/2$. If $\operatorname{diam}E<\delta$, every $x,y\in E$ has $d(x,y)<\delta$, so $d(f(x),f(y))<\varepsilon/2$. Taking the supremum gives

$$
\operatorname{diam}f(E)\le\varepsilon/2<\varepsilon.
$$

The smaller tolerance is necessary to retain a strict conclusion after taking a supremum. The empty set satisfies the conclusion automatically; unbounded sets cannot satisfy the finite input bound.

Conversely, apply the diameter condition to $E=\{x,y\}$. Its diameter is $d(x,y)$, including when $x=y$, and the image diameter is $d(f(x),f(y))$. The resulting estimate is precisely uniform continuity.

**Lean declarations:** `exercise09_uniform_to_diameter`, `exercise09_diameter_to_uniform`, `exercise09_diameter_empty`, `exercise09_diameter_unbounded`, `exercise09_diameter_agrees`.

<a id="r04e10"></a>
### 4.10 — A sequential proof of uniform continuity
**Lean source:** [Exercise10.lean](../../../Math/Rudin/Chapter04/Exercise10.lean).
**Inventory status:** Verified as stated.

**Statement.** If a map $f:X\to Y$ between metric spaces is not uniformly continuous, there are $\varepsilon>0$ and sequences $p_n,q_n\in X$ with

$$
d_X(p_n,q_n)\longrightarrow0,\qquad
 d_Y(f(p_n),f(q_n))>\varepsilon\quad\text{for every }n.
$$

Use these sequences to prove that a continuous map from a compact metric space is uniformly continuous.

**Proof.** Failure of uniform continuity gives $e>0$ such that for every $\delta>0$ some $p,q$ satisfy $d_X(p,q)<\delta$ and $d_Y(f(p),f(q))\ge e$. Choose these points for $\delta=1/(n+1)$ and set $\varepsilon=e/2$. This proves both required sequence estimates, including strict output separation.

Now suppose $X$ is compact and $f$ continuous. A subsequence $p_{n_j}$ converges to some $x\in X$. The triangle inequality and $d_X(p_{n_j},q_{n_j})\to0$ show that $q_{n_j}\to x$ too. Continuity gives $f(p_{n_j})\to f(x)$ and $f(q_{n_j})\to f(x)$, so their mutual distances tend to zero. This contradicts the fixed lower bound $\varepsilon$.

**Lean declarations:** `exercise10_nonuniform_sequences`, `exercise10_compact_uniform_continuity`.

<a id="r04e11"></a>
### 4.11 — Cauchy images and extension by limits
**Lean source:** [Exercise11.lean](../../../Math/Rudin/Chapter04/Exercise11.lean).
**Inventory status:** Verified as stated.

**Statement.** A uniformly continuous map $f:X\to Y$ between metric spaces sends Cauchy sequences to Cauchy sequences. Consequently, if $E$ is dense in a metric space $X$ and $f:E\to\mathbb R$ is uniformly continuous, then $f$ has a continuous extension to $X$.

**Scope.** The sequence construction in the file works for every complete metric target $Y$ and gives a uniformly continuous extension. No completeness of $X$ is required.

**Proof.** Given an output tolerance $\varepsilon>0$, uniform continuity supplies $\delta>0$. A Cauchy sequence has all sufficiently late pairs within $\delta$, so its image has all sufficiently late pairs within $\varepsilon$.

For each $x\in X$, choose $u_n\in E$ tending to $x$, using density. The sequence is Cauchy in $E$, so $f(u_n)$ is Cauchy and has a limit in the complete target. Define $g(x)$ to be this limit. If $v_n\in E$ also tends to $x$, then $d(u_n,v_n)\to0$; uniform continuity gives $d(f(u_n),f(v_n))\to0$. Hence the two limits agree, so $g$ is independent of the choices. At $x\in E$, comparison with the constant sequence $x$ proves $g(x)=f(x)$.

To prove uniform continuity, choose $\delta$ for the original map with tolerance $\varepsilon/2$. If $d(x,y)<\delta$, approximating sequences $u_n\to x$ and $v_n\to y$ eventually satisfy $d(u_n,v_n)<\delta$. Thus their image distances are eventually at most $\varepsilon/2$. Passing to limits gives $d(g(x),g(y))\le\varepsilon/2<\varepsilon$. In particular $g$ is continuous. If $X$ is empty, the unique map gives the extension; density permits no nonempty $X$ with $E$ empty.

**Lean declarations:** `exercise11_cauchy_images`, `exercise11_extension_via_sequences`, `exercise11_extension_uniformContinuous`.

<a id="r04e12"></a>
### 4.12 — Composition of uniformly continuous maps
**Lean source:** [Exercise12.lean](../../../Math/Rudin/Chapter04/Exercise12.lean).
**Inventory status:** Verified as stated.

**Statement.** If $X,Y,Z$ are metric spaces and $f:X\to Y$, $g:Y\to Z$ are uniformly continuous, then $g\circ f:X\to Z$ is uniformly continuous.

**Proof.** Given $\varepsilon>0$, choose $\eta>0$ such that $d_Y(u,v)<\eta$ implies $d_Z(g(u),g(v))<\varepsilon$. Then choose $\delta>0$ such that $d_X(x,y)<\delta$ implies $d_Y(f(x),f(y))<\eta$. Combining the implications proves the claim.

**Lean declarations:** `exercise12_composition`.

<a id="r04e13"></a>
### 4.13 — Which targets admit dense-domain extensions?
**Lean source:** [Exercise13.lean](../../../Math/Rudin/Chapter04/Exercise13.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $E$ be dense in a metric space $X$ and let $f:E\to\mathbb R$ be uniformly continuous. There is a unique continuous extension $g:X\to\mathbb R$. The extension also exists when the target is $\mathbb R^k$, any compact metric space, or any complete metric space. It need not exist for an arbitrary metric target. For a complete target, the extension is uniformly continuous and is unique among continuous extensions. No nonemptiness assumption is needed, and $k=0$ is allowed.

**Proof.** For any complete metric target, the sequence construction of Exercise 4.11 supplies a uniformly continuous extension. The real line and every finite-dimensional Euclidean space are complete. A compact metric space is complete as well: a Cauchy sequence has a convergent subsequence by compactness, and the Cauchy property makes the entire sequence converge to the same limit. This answers all three target generalizations affirmatively.

For uniqueness, two continuous extensions agree on dense $E$, so Exercise 4.4 makes them equal on $X$. This uniqueness argument works for every metric target, whether complete or not.

For the negative answer, let $X=\mathbb R$, $E=\mathbb R\setminus\{0\}$, and take the same punctured line as target $Y$, with its usual subspace metric. The identity $f:E\to Y$ is uniformly continuous and $E$ is dense. The sequence $1/(n+1)$ is Cauchy but has no limit in $Y$, so $Y$ is not complete. If $g:\mathbb R\to Y$ were a continuous extension, composing it with the inclusion $Y\hookrightarrow\mathbb R$ would give a continuous real map equal to the identity on $E$. Density forces it to be the identity everywhere, requiring $g(0)=0\notin Y$.

**Lean declarations:** `exercise13_real_extension`, `exercise13_uniqueness`, `exercise13_euclidean_range`, `exercise13_compact_range`, `exercise13_complete_range`, `exercise13_arbitrary_range`.

<a id="r04e14"></a>
### 4.14 — A fixed point in the unit interval
**Lean source:** [Exercise14.lean](../../../Math/Rudin/Chapter04/Exercise14.lean).
**Inventory status:** Verified as stated.

**Statement.** Every continuous $f:[0,1]\to[0,1]$ has a fixed point, possibly an endpoint.

**Proof.** The continuous real function $F(x)=f(x)-x$ on $[0,1]$ satisfies $F(0)\ge0$ and $F(1)\le0$. If either value is zero, that endpoint is fixed. Otherwise, the intermediate value theorem gives $c\in(0,1)$ with $F(c)=0$, hence $f(c)=c$.

**Lean declarations:** `exercise14_fixed_point`.

<a id="r04e15"></a>
### 4.15 — Continuous open real maps are monotone
**Lean source:** [Exercise15.lean](../../../Math/Rudin/Chapter04/Exercise15.lean).
**Inventory status:** Verified as stated.

**Statement.** A map is open if it sends every open set to an open set. Every continuous open map $f:\mathbb R\to\mathbb R$ is nondecreasing or nonincreasing. Neither injectivity nor surjectivity is assumed.

**Proof.** An open real map has no local maximum: an open neighborhood on which $f\le f(x)$ would have an open image containing $f(x)$ but no larger values, which is impossible. The same argument excludes local minima.

If $a<b$ and $f(a)=f(b)$, continuity on $[a,b]$ gives a local extremum in $(a,b)$. Indeed, if $f$ is constant there every interior point is an extremum; otherwise an attained maximum above the endpoint value or an attained minimum below it is interior. This contradicts openness. Thus $f$ is injective. The standard monotonicity theorem for continuous injections on a real interval now gives that $f$ is strictly increasing or strictly decreasing, and therefore has the required weak monotonicity.

**Lean declarations:** `exercise15_open_continuous_monotone`.

<a id="r04e16"></a>
### 4.16 — Integer and fractional parts
**Lean source:** [Exercise16.lean](../../../Math/Rudin/Chapter04/Exercise16.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $[x]=\lfloor x\rfloor$ be the integer satisfying $x-1<[x]\le x$, regarded as real-valued, and let $\{x\}=x-[x]$, so $0\le\{x\}<1$. Both functions are continuous exactly at the nonintegers. At every integer $n$,

$$
[n]=n,\quad\lim_{x\to n^-}[x]=n-1,\quad\lim_{x\to n^+}[x]=n,
$$

$$
\{n\}=0,\quad\lim_{x\to n^-}\{x\}=1,\quad\lim_{x\to n^+}\{x\}=0.
$$

Thus all their discontinuities are simple jumps, and both functions are right-continuous at each integer. At a noninteger, both one-sided limits equal the function's value.

**Proof.** On $(n,n+1)$, the integer part is constantly $n$ and the fractional part is $x-n$. This proves continuity and the one-sided limits at nonintegers. Immediately to the left of $n$, the integer part is $n-1$, while on $[n,n+1)$ it is $n$. Subtracting these values from $x$ gives the asserted limits for the fractional part. The unequal left and right limits exclude continuity at every integer; the right-hand formulas include the endpoint values and prove right-continuity. The inequality $[x]\le x$ is non-strict, including at integers.

**Lean declarations:** `exercise16_floor_discontinuities`, `exercise16_floor_integer`, `exercise16_noninteger_limits`, `exercise16_fractional_discontinuities`, `exercise16_frac_integer`.

<a id="r04e17"></a>
### 4.17 — Countability of simple discontinuities
**Lean source:** [Exercise17.lean](../../../Math/Rudin/Chapter04/Exercise17.lean).
**Inventory status:** Verified as stated.

**Statement.** For any real function on $(a,b)$, its simple discontinuities form an at most countable set. Here a simple discontinuity is an interior point at which both finite one-sided limits exist but the function is not continuous. This includes upward jumps, downward jumps, and removable discontinuities. No condition is imposed at $a$ or $b$.

**Proof.** At an upward jump $x$, write $L=f(x-)<f(x+)=R$. The source's rational-triple construction is as follows:

- **(a)** Choose $p\in\mathbb Q$ with $L<p<R$.
- **(b)** From the left limit, choose $q\in\mathbb Q$ with $a<q<x$ such that $f(t)<p$ whenever $q<t<x$.
- **(c)** From the right limit, choose $r\in\mathbb Q$ with $x<r<b$ such that $f(t)>p$ whenever $x<t<r$.

The same $p$ is used in all three steps. A triple $(p,q,r)$ can describe at most one point. If it described $x<y$, the midpoint $t=(x+y)/2$ would lie in both $(x,r)$ and $(q,y)$, forcing $f(t)>p$ and $f(t)<p$. Since $\mathbb Q^3$ is countable, upward jumps are at most countable. Apply the same result to $-f$ for downward jumps.

To treat removable discontinuities, first fix any set $S\subseteq\mathbb R$. Its points $x\in S$ for which some interval $(x,x+\eta_x)$ misses $S$ form a countable set. Choose a rational in each such interval. The intervals belonging to distinct such points are disjoint: if $x<y$ and $y\in S$, then $y\ge x+\eta_x$. Thus the chosen rationals distinguish the points.

If $f(x)$ is strictly below its finite right limit $R$, choose rational $p$ with $f(x)<p<R$. Then $x$ belongs to $S_p=\{t:f(t)<p\}$, but a right-hand interval at $x$ misses $S_p$. The preceding countability result and a countable union over $p$ show that these points are countable. Applying it to $-f$ treats $f(x)>R$. Hence all discrepancies between a value and a finite right limit are countable, including all removable discontinuities.

Finally, if the two finite one-sided limits are equal to each other and to $f(x)$, then $f$ is continuous at $x$. Every simple discontinuity therefore belongs to one of the three countable classes above. Since $x$ is interior to $(a,b)$, domain-relative one-sided limits agree with the usual local one-sided limits; the argument applies without any extension assumption outside the interval.

**Lean declarations:** `exercise17_a`, `exercise17_b`, `exercise17_c`, `exercise17_triple_uniqueness`, `exercise17_upward_jumps_countable`, `exercise17_other_simple_types`, `exercise17_simple_discontinuities_countable`, `exercise17_simple_discontinuities_within_countable`.

<a id="r04e18"></a>
### 4.18 — Thomae's function
**Lean source:** [Exercise18.lean](../../../Math/Rudin/Chapter04/Exercise18.lean).
**Inventory status:** Verified as stated.

**Statement.** Define $f(x)=0$ for irrational $x$, and

$$
f(m/n)=1/n
$$

when $m,n\in\mathbb Z$, $n>0$, and $m,n$ are relatively prime. In particular, $f(0)=1$, using the reduced denominator $1$. Then $f$ is continuous at every irrational point and has a simple removable discontinuity at every rational point. In fact, its deleted limit at every real point is zero.

**Proof.** In any bounded interval there are only finitely many reduced rationals with denominator at most a fixed integer $N$: both the denominator and, by boundedness, the numerator range over finite sets. Given $x\in\mathbb R$ and $\varepsilon>0$, choose $N$ with $1/(N+1)<\varepsilon$ and a bounded neighborhood of $x$. Exclude from a smaller neighborhood the finitely many rationals in this bounded interval with denominator at most $N$, except possibly $x$ itself. Every remaining $y\ne x$ is irrational, giving $f(y)=0$, or has reduced denominator at least $N+1$, giving $0<f(y)\le1/(N+1)<\varepsilon$. This proves the deleted limit is zero. At an irrational point it equals $f(x)$, proving continuity. At a rational point both one-sided limits are zero, but $f(x)>0$; this is a simple removable discontinuity, including at zero.

**Lean declarations:** `exercise18_irrational_continuity`, `exercise18_rational_simple_discontinuity`, `exercise18_deleted_limit`.

<a id="r04e19"></a>
### 4.19 — Intermediate values and closed rational level sets
**Lean source:** [Exercise19.lean](../../../Math/Rudin/Chapter04/Exercise19.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $f:\mathbb R\to\mathbb R$ have the intermediate value property: whenever $f(a)<c<f(b)$, some point strictly between $a$ and $b$, in either order, has value $c$. Suppose $\{x:f(x)=r\}$ is closed for each rational $r$. Then $f$ is continuous.

**Proof.** Fix $x$ and a rational $r\ne f(x)$. The complement of the closed $r$-level set contains an open interval about $x$. On that interval, $f$ must stay on the same side of $r$ as $f(x)$: a point on the other side would, by the intermediate value property on the segment joining it to $x$, produce a point of the excluded level set.

Given $\varepsilon>0$, choose rationals

$$
f(x)-\varepsilon<r<f(x)<s<f(x)+\varepsilon.
$$

Apply the preceding argument to both levels and intersect the resulting neighborhoods. On this intersection $r<f(y)<s$, so $|f(y)-f(x)|<\varepsilon$. Thus $f$ is continuous at every $x$.

**Lean declarations:** `exercise19_closed_rational_fibers`.

<a id="r04e20"></a>
### 4.20 — Distance to a nonempty set
**Lean source:** [Exercise20.lean](../../../Math/Rudin/Chapter04/Exercise20.lean).
**Inventory status:** Verified as stated.

**Statement.** For a nonempty subset $E$ of a metric space $X$, define

$$
\rho_E(x)=\inf_{z\in E}d(x,z).
$$

Then **(a)** $\rho_E(x)=0$ if and only if $x\in\overline E$; and **(b)**

$$
|\rho_E(x)-\rho_E(y)|\le d(x,y)\qquad(x,y\in X).
$$

Consequently $\rho_E:X\to\mathbb R$ is uniformly continuous.

**Proof.** Nonemptiness and the lower bound zero make the infimum a finite nonnegative real number. It is zero exactly when, for every $\varepsilon>0$, some $z\in E$ has $d(x,z)<\varepsilon$. This is precisely the ball criterion for $x\in\overline E$, not necessarily for $x\in E$.

For every $z\in E$, the triangle inequality gives $d(x,z)\le d(x,y)+d(y,z)$. Taking infima gives $\rho_E(x)\le d(x,y)+\rho_E(y)$. Interchange $x,y$ to obtain the reverse difference bound, and combine them to obtain (b). Taking $\delta=\varepsilon$ proves uniform continuity. No assertion for an empty $E$ is needed or used.

**Lean declarations:** `exercise20_a`, `exercise20_b_lipschitz`, `exercise20_b_uniform_continuity`.

<a id="r04e21"></a>
### 4.21 — Positive separation from a compact set
**Lean source:** [Exercise21.lean](../../../Math/Rudin/Chapter04/Exercise21.lean).
**Inventory status:** Verified as stated.

**Statement.** If $K,F$ are disjoint subsets of a metric space, $K$ is compact, and $F$ is closed, there is $\delta>0$ such that

$$
d(p,q)>\delta\qquad(p\in K,\ q\in F).
$$

This includes empty sets. The result can fail for two disjoint closed noncompact sets.

**Proof.** If either set is empty, any positive $\delta$, for example $1$, works vacuously. Otherwise, the continuous function $\rho_F$ attains its minimum $m$ on $K$. At its minimizer $p_0$, closedness and disjointness give $p_0\notin\overline F=F$, hence $m>0$. For every $p\in K$, $q\in F$,

$$
d(p,q)\ge\rho_F(p)\ge m>m/2.
$$

Thus choose $\delta=m/2$, retaining the requested strict inequality.

For the counterexample, use $\mathbb R^2$ with its product maximum metric, and let

$$
A=\{(x,y):y=0\},\qquad B=\{(x,y):xy=1\}.
$$

They are closed as level sets of continuous functions and are disjoint. Both have unbounded first coordinate, so neither is compact. For any $\delta>0$, put $t=2/\delta$. The points $(t,0)\in A$ and $(t,t^{-1})\in B$ have distance $t^{-1}=\delta/2<\delta$. Hence no positive uniform lower bound exists. The same distances occur in the Euclidean metric.

**Lean declarations:** `exercise21_positive_separation`, `exercise21_closed_noncompact_failure`.

<a id="r04e22"></a>
### 4.22 — Separating closed sets by a continuous function
**Lean source:** [Exercise22.lean](../../../Math/Rudin/Chapter04/Exercise22.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $A,B$ be disjoint nonempty closed subsets of a metric space $X$, and set

$$
f(p)=\frac{\rho_A(p)}{\rho_A(p)+\rho_B(p)}.
$$

The denominator is positive everywhere; $f$ is continuous, $0\le f\le1$, $f^{-1}(\{0\})=A$, and $f^{-1}(\{1\})=B$. Every closed subset of $X$ is the zero set of a continuous real function. Moreover,

$$
V=f^{-1}([0,1/2)),\qquad W=f^{-1}((1/2,1])
$$

are disjoint open sets containing $A$ and $B$, respectively. Thus any two disjoint closed subsets of $X$, including empty ones, have disjoint open neighborhoods.

**Proof.** Both distance functions are nonnegative and continuous by Exercise 4.20. Their sum could be zero only if both were zero, placing $p$ in $A\cap B$ by closedness. Hence the denominator is positive and the quotient is continuous. Its numerator lies between zero and its denominator, giving $0\le f\le1$. With a positive denominator, $f(p)=0$ is equivalent to $\rho_A(p)=0$, hence to $p\in A$; and $f(p)=1$ is equivalent to $\rho_B(p)=0$, hence to $p\in B$.

For a nonempty closed set $C$, use $h=\rho_C$ to represent it as a zero set. For $C=\varnothing$, use $h=1$; for $C=X$, the constant zero function also gives the result, including when $X$ is empty.

The half-open intervals displayed above are not open in $\mathbb R$. Instead use the established range bound to write $V=\{p:f(p)<1/2\}$ and $W=\{p:f(p)>1/2\}$. These are open by continuity. Their defining inequalities are incompatible, and the zero and one fibers give $A\subseteq V$ and $B\subseteq W$. Finally, if $A$ is empty, choose $V=\varnothing$, $W=X$; if $B$ is empty, choose $V=X$, $W=\varnothing$. These choices complete the separation claim for arbitrary disjoint closed sets.

**Lean declarations:** `exercise22_denominator_positive`, `exercise22_continuous`, `exercise22_range`, `exercise22_zero_fiber`, `exercise22_one_fiber`, `exercise22_all_closed_zero_sets`, `exercise22_open_neighborhoods`, `exercise22_disjoint_neighborhoods`, `exercise22_normality`.

<a id="r04e23"></a>
### 4.23 — Continuity and slopes of convex functions
**Lean source:** [Exercise23.lean](../../../Math/Rudin/Chapter04/Exercise23.lean).
**Inventory status:** Verified as stated.

**Statement.** Suppose $f:(a,b)\to\mathbb R$ is convex in the source sense:

$$
f(\lambda x+(1-\lambda)y)\le\lambda f(x)+(1-\lambda)f(y)
\quad(x,y\in(a,b),\ 0<\lambda<1).
$$

Then $f$ is continuous on $(a,b)$. If $f$ is convex on an interval $S$, $h$ is convex and nondecreasing on an interval $T$, and $f(S)\subseteq T$, then $h\circ f$ is convex on $S$. In particular, $e^f$ is convex. For $a<s<t<u<b$,

$$
\frac{f(t)-f(s)}{t-s}\le\frac{f(u)-f(s)}{u-s}
\le\frac{f(u)-f(t)}{u-t}.
$$

**Proof.** The endpoint weights $0,1$ give equality, so the strict-weight definition also gives the usual closed-weight definition. Express

$$
t=\frac{u-t}{u-s}s+\frac{t-s}{u-s}u.
$$

Convexity gives $(u-s)f(t)\le(u-t)f(s)+(t-s)f(u)$. Rearranging this inequality and dividing by the positive factors gives each displayed slope inequality.

Fix $x\in(a,b)$ and choose $r<x<s$ inside the interval. The slope inequalities imply, for $r<y<s$ and $y\ne x$,

$$
\frac{f(x)-f(r)}{x-r}\le\frac{f(y)-f(x)}{y-x}
\le\frac{f(s)-f(x)}{s-x}.
$$

For $y<x$, the middle quotient is the same secant slope with endpoints $y,x$; the same inequalities apply. The absolute value of this quotient is bounded by the maximum of the absolute values of the two fixed outer slopes. Thus $|f(y)-f(x)|\le M|y-x|$ locally, proving continuity at $x$. No endpoint continuity is asserted.

For composition, put $z=\lambda x+(1-\lambda)y$. Both $f(z)$ and $\lambda f(x)+(1-\lambda)f(y)$ lie in $T$. First apply monotonicity of $h$ to the convexity inequality for $f$, and then apply convexity of $h$:

$$
h(f(z))\le h(\lambda f(x)+(1-\lambda)f(y))
\le\lambda h(f(x))+(1-\lambda)h(f(y)).
$$

The exponential is convex and increasing on all of $\mathbb R$, so it is an allowed outer function. The file also allows arbitrary convex sets $S,T\subseteq\mathbb R$, including degenerate or empty intervals.

**Lean declarations:** `exercise23_convex_continuity`, `exercise23_increasing_convex_composition`, `exercise23_exp_convex`, `exercise23_first_slope_inequality`, `exercise23_second_slope_inequality`.

<a id="r04e24"></a>
### 4.24 — Continuous midpoint-convex functions are convex
**Lean source:** [Exercise24.lean](../../../Math/Rudin/Chapter04/Exercise24.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $f:(a,b)\to\mathbb R$ be continuous and suppose

$$
f((x+y)/2)\le\frac{f(x)+f(y)}2\qquad(x,y\in(a,b)).
$$

Then $f$ is convex: for every $x,y\in(a,b)$ and $0\le\lambda\le1$,

$$
f(\lambda x+(1-\lambda)y)\le\lambda f(x)+(1-\lambda)f(y).
$$

This includes the source's strictly interior weights and requires no continuity at $a$ or $b$.

**Proof.** First let $g$ be continuous and midpoint-convex on $[0,1]$ with $g(0)=g(1)=0$. It attains a maximum $M=g(c)$. If $c\le1/2$, then

$$
M=g((0+2c)/2)\le\frac{g(0)+g(2c)}2\le M/2.
$$

If $c\ge1/2$, apply midpoint convexity to $2c-1$ and $1$ to obtain the same inequality. Thus $M\le0$, so $g\le0$ throughout $[0,1]$.

For fixed $x,y\in(a,b)$, apply this result to

$$
g(t)=f(tx+(1-t)y)-tf(x)-(1-t)f(y).
$$

The whole segment lies inside $(a,b)$, so $g$ is continuous on $[0,1]$. The affine maps in this formula preserve midpoints; the hypothesis on $f$ therefore makes $g$ midpoint-convex. Its endpoint values are zero. Hence $g(\lambda)\le0$, which is the required convexity inequality, including $\lambda=0,1$ and $x=y$.

**Lean declarations:** `exercise24_midpoint_to_convex`, `exercise24_source`.

<a id="r04e25"></a>
### 4.25 — Sums of closed sets
**Lean source:** [Exercise25.lean](../../../Math/Rudin/Chapter04/Exercise25.lean).
**Inventory status:** Verified as stated.

**Statement.** For subsets of $\mathbb R^k$, let $A+B=\{x+y:x\in A,\ y\in B\}$. **(a)** If $K$ is compact and $C$ is closed, then $K+C$ is closed, including empty summands and $k=0$. **(b)** For an irrational real $\alpha$, the sets

$$
C_1=\mathbb Z,\qquad C_2=\{n\alpha:n\in\mathbb Z\}
$$

are closed, but $C_1+C_2$ is countably infinite, dense in $\mathbb R$, and not closed. Countable infinitude of this sum holds for every real $\alpha$.

**Proof.** For (a), suppose $z_n=k_n+c_n\in K+C$ converges to $z$. Compactness supplies a subsequence $k_{n_j}\to k\in K$. Then $c_{n_j}=z_{n_j}-k_{n_j}\to z-k$, and closedness gives $z-k\in C$. Therefore $z\in K+C$. The sequential closedness criterion applies in Euclidean space. If either summand is empty, the sum is empty and closed; dimension zero causes no change to the argument.

For (b), $\mathbb Z$ is closed in $\mathbb R$, since every noninteger has an open interval around it containing no integer. Irrationality implies $\alpha\ne0$, so multiplication by $\alpha$ is a homeomorphism and sends $\mathbb Z$ to the closed set $C_2$. The sum is the image of the countable set $\mathbb Z^2$ under $(m,n)\mapsto m+n\alpha$; it contains $\mathbb Z$ and hence is infinite, for any $\alpha$.

To see density for irrational $\alpha$, the pigeonhole principle applied to the fractional parts of $0,\alpha,\ldots,N\alpha$ gives distinct indices whose fractional parts differ by less than $1/N$. Their difference is a nonzero element of $\mathbb Z+\alpha\mathbb Z$; it cannot be zero because $\alpha$ is irrational. Taking its absolute value gives a positive element $\eta<1/N$ of this additive subgroup. Integer multiples of $\eta$ approximate any real number with error less than $\eta$. Since $N$ can be arbitrarily large, the subgroup is dense. This is the standard irrational-generator density result used in the Lean proof. If the sum were also closed, density would make it all of $\mathbb R$, contradicting its countability and the uncountability of $\mathbb R$.

**Lean declarations:** `exercise25_a`, `exercise25_b_first_closed`, `exercise25_b_second_closed`, `exercise25_b_countable_sum`, `exercise25_b_dense_sum`, `exercise25_b_nonclosed_sum`.

<a id="r04e26"></a>
### 4.26 — Recovering continuity through an injective map
**Lean source:** [Exercise26.lean](../../../Math/Rudin/Chapter04/Exercise26.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $X,Y,Z$ be metric spaces with $Y$ compact, let $f:X\to Y$ be arbitrary, and let $g:Y\to Z$ be continuous and injective. Put $h=g\circ f$. If $h$ is uniformly continuous, then $f$ is uniformly continuous; if $h$ is continuous, then $f$ is continuous. Compactness of $Y$ is necessary, even when $X$ and $Z$ are compact. The file also proves the forward implications: uniformly continuous $f$ gives uniformly continuous $h$ under compactness of $Y$, and continuous $f$ gives continuous $h$ without compactness or injectivity assumptions on $g$.

**Proof.** A continuous injection from a compact space to a metric space is a homeomorphism onto its image: it maps closed sets, which are compact, to compact and therefore closed sets. Thus the inverse $g^{-1}:g(Y)\to Y$ is continuous. The image $g(Y)$ is compact, so this inverse is uniformly continuous by the compact-domain uniform-continuity theorem. Regard $h$ as a map into the subspace $g(Y)$; its continuity or uniform continuity is unchanged. The identity $f=g^{-1}\circ h$ and composition give the two asserted implications. For the forward directions, use continuity of compositions; in the uniform case $g$ itself is uniformly continuous because $Y$ is compact.

For both failures without compactness, take $X=Z=[0,1]$ with the usual metric and let $Y$ be the same underlying set with the discrete zero-one metric. Let $f:X\to Y$ and $g:Y\to Z$ both be the identity on points. The space $Y$ is infinite and discrete, hence not compact: its cover by singleton open sets has no finite subcover. Every map from a discrete space is continuous, so $g$ is continuous and injective. The composite $h$ is the usual identity on $[0,1]$, hence uniformly continuous and continuous. But $f$ cannot be continuous, since its image of compact $X$ would be all of the noncompact space $Y$. It is consequently not uniformly continuous either. Both outer spaces remain compact, as required.

**Lean declarations:** `exercise26_uniform_continuity`, `exercise26_continuity`, `exercise26_noncompact_uniform_failure`, `exercise26_noncompact_continuity_failure`, `exercise26_uniform_continuity_forward`, `exercise26_continuity_forward`.
