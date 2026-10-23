<a id="chapter-11"></a>

# Chapter 11 — The Lebesgue Theory

[All chapters](../solutions.md) · [Previous chapter](chapter-10.md)

**Exercises:** [1](#r11e01) · [2](#r11e02) · [3](#r11e03) · [4](#r11e04) · [5](#r11e05) · [6](#r11e06) · [7](#r11e07) · [8](#r11e08) · [9](#r11e09) · [10](#r11e10) · [11](#r11e11) · [12](#r11e12) · [13](#r11e13) · [14](#r11e14) · [15](#r11e15) · [16](#r11e16) · [17](#r11e17) · [18](#r11e18)

<a id="r11e01"></a>
### 11.1 — Zero nonnegative integral implies zero almost everywhere
**Lean source:** [Exercise01.lean](../../../Math/Rudin/Chapter11/Exercise01.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $(X,\mu)$ be a measure space, $E\subseteq X$ measurable, and $f$ a real function that is measurable on $E$ and satisfies $f\ge0$ there. If its nonnegative Lebesgue integral satisfies

$$
\int_E f\,d\mu=0,
$$

then $f=0$ almost everywhere on $E$; equivalently, $\mu(\{x\in E:f(x)\ne0\})=0$. No assumption that $\mu(E)$ is finite is needed. The formal statements permit measurability almost everywhere for the restricted measure and also cover functions valued in $[0,\infty]$.

**Proof.** For each positive integer $n$, put

$$
E_n=\{x\in E:f(x)\ge1/n\}.
$$

Monotonicity of the nonnegative integral gives

$$
0=\int_E f\,d\mu\ge\frac1n\mu(E_n).
$$

Hence every $E_n$ has measure zero. Since $f\ge0$ on $E$, its nonzero set there is $\bigcup_{n\ge1}E_n$, which also has measure zero. This argument includes the value $+\infty$. For a function measurable only almost everywhere, take a measurable representative for the restricted measure; the null exceptional set does not change the conclusion. The Lean proof applies the standard zero-nonnegative-integral criterion directly.

**Scope.** For real-valued $f$, the file uses the nonnegative integral after embedding the nonnegative values into $[0,\infty]$. Nonnegativity on $E$ ensures that this loses no values. A separate Bochner-integral version assumes explicitly that $f$ is integrable on $E$. For a nonnegative integrable function this integral agrees with the nonnegative integral, so the same conclusion follows. The integrability assumption is necessary for that formulation because Lean assigns the Bochner integral the default value zero for nonintegrable functions; that default is not the source's zero-integral hypothesis.

**Lean declarations:** `exercise01`, `exercise01_ennreal`, `exercise01_integrable`.

<a id="r11e02"></a>
### 11.2 — Vanishing integrals on measurable subsets
**Lean source:** [Exercise02.lean](../../../Math/Rudin/Chapter11/Exercise02.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $E$ be measurable in a measure space $(X,\mu)$, and let $f$ be integrable on $E$. If $\int_A f\,d\mu=0$ for every measurable $A\subseteq E$, then $f=0$ almost everywhere on $E$. The result holds for real and complex functions, and for functions with values in a complete real normed space. The measure need not be finite or sigma-finite.

**Proof.** Apply the standard uniqueness criterion for an integrable function from its integrals over measurable sets, using the restricted measure $\mu|_E$. For every measurable $A\subseteq X$, restriction of the set integral gives

$$
\int_A f\,d(\mu|_E)=\int_{A\cap E}f\,d\mu=0.
$$

The criterion gives $f=0$ almost everywhere for $\mu|_E$. Since $E$ is measurable, this is exactly $f=0$ almost everywhere on $E$ for $\mu$. The explicit integrability hypothesis excludes the default value assigned to a nonintegrable Bochner integral.

**Lean declarations:** `Rudin.Chapter11.exercise02`.

<a id="r11e03"></a>
### 11.3 — Measurability of the convergence set
**Lean source:** [Exercise03.lean](../../../Math/Rudin/Chapter11/Exercise03.lean).
**Inventory status:** Pending verification.

The extended-real repair is implemented and awaits independent reviews and project checks.

**Statement.** Let $f_n:X\to\overline{\mathbb R}$ be measurable on an arbitrary measurable space. The set where $f_n(x)$ converges to an extended-real limit is measurable. The subset where the limit is a finite real number is also measurable, without requiring finite-valued terms. Real-valued and complex-valued sequences have measurable finite-limit sets as well.

**Proof.** The extended real line with its order topology is compact and metrizable, hence Polish. The measurable convergence-set theorem therefore applies to the full extended-real input space. The sets $C_+$ and $C_-$ where the sequence tends to positive and negative infinity are measurable by the fixed-limit theorem. Uniqueness of limits gives $C_{\mathrm{finite}}=C_{\mathrm{extended}}\setminus(C_+\cup C_-)$. A remaining extended-real limit is neither endpoint, so it is the image of its real value. This proves both implications and measurability. An initial infinite term followed by the constant 7 is included in the finite-limit result.

For real-valued inputs, the standard measurable convergence-set theorem applies directly. Its countable Cauchy criterion can be written as

$$
\bigcap_{j\ge1}\ \bigcup_{N\ge0}\ \bigcap_{m,n\ge N}
\{x:|f_m(x)-f_n(x)|<1/j\}.
$$

Each set in this expression is measurable, and completeness of $\mathbb R$ identifies the Cauchy condition with convergence to a real number. This excludes divergence to either infinity.

A complex sequence converges if and only if its real and imaginary parts both converge to finite real limits. Necessity follows from continuity of the coordinate maps. Conversely, limits $a,b$ of the coordinates give the limit $a+ib$ by addition and multiplication by $i$. The complex convergence set is therefore the intersection of the two measurable real convergence sets.

**Lean declarations:** `Rudin.Chapter11.exercise03_ereal`, `Rudin.Chapter11.exercise03_ereal_finite_iff`, `Rudin.Chapter11.exercise03_ereal_finite`, `Rudin.Chapter11.exercise03_real`, `Rudin.Chapter11.exercise03_complex_iff`, `Rudin.Chapter11.exercise03_complex`.

<a id="r11e04"></a>
### 11.4 — A bounded measurable multiplier
**Lean source:** [Exercise04.lean](../../../Math/Rudin/Chapter11/Exercise04.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $E$ be measurable, $f$ integrable on $E$, and $g$ measurable and bounded on $E$. Then $fg$ is integrable on $E$, for real or complex functions. More generally, the integrability result needs only almost-everywhere strong measurability of $g$ for $\mu|_E$, together with a pointwise bound $\|g(x)\|\le C$ on $E$. Separate results establish ordinary measurability of the product on the subtype $E$ when both factors are measurable there.

**Proof.** Multiplication is continuous over either scalar field, so the product of two measurable functions on $E$ is measurable. For the almost-everywhere formulation, multiply almost-everywhere strongly measurable representatives. On $E$,

$$
\|f(x)g(x)\|\le C\|f(x)\|.
$$

The bounded-multiplier integrability theorem, applied to the restricted measure, now gives integrability and almost-everywhere strong measurability of the product. If $E$ is empty, both conclusions hold without a sign condition on the chosen bound.

**Lean declarations:** `Rudin.Chapter11.exercise04`, `Rudin.Chapter11.exercise04_measurable_real`, `Rudin.Chapter11.exercise04_measurable_complex`.

<a id="r11e05"></a>
### 11.5 — Strict inequality in Fatou's lemma
**Lean source:** [Exercise05.lean](../../../Math/Rudin/Chapter11/Exercise05.lean).
**Inventory status:** Verified as stated.

**Statement.** On $[0,1]$, let $g$ be zero on $[0,1/2]$ and one on $(1/2,1]$. Set $f_{2k}(x)=g(x)$ and $f_{2k+1}(x)=g(1-x)$. Then $0\le f_n\le1$, each $f_n$ is integrable, and

$$
\liminf_{n\to\infty}f_n(x)=0\quad(x\in[0,1]),
\qquad \int_{[0,1]}f_n(x)\,dx=\frac12.
$$

**Proof.** Extend $g$ to the real line as the indicator of $(1/2,1]$. Reflection gives $g(1-x)=\mathbf1_{[0,1/2)}(x)$. Thus both parities take only the values zero and one. If $x\le1/2$, all even terms vanish. If $x>1/2$, all odd terms vanish. There are arbitrarily large indices of either parity, so nonnegativity and these zero subsequences give the stated lower limit. At $x=1/2$ every term is zero; at $0$ and $1$ the values alternate between zero and one. This includes all boundary cases of the closed interval.

Both indicator sets are measurable and have length $1/2$, so their indicators are integrable and have integral $1/2$. Hence the integral of the pointwise lower limit is zero, whereas the lower limit of the integrals is $1/2$.

**Lean declarations:** `Rudin.Chapter11.exercise05_even`, `Rudin.Chapter11.exercise05_odd`, `Rudin.Chapter11.exercise05_reflection`, `Rudin.Chapter11.exercise05_bounds`, `Rudin.Chapter11.exercise05_lower_limit`, `Rudin.Chapter11.exercise05_integrable`, `Rudin.Chapter11.exercise05_integrals`.

<a id="r11e06"></a>
### 11.6 — Uniform convergence on infinite and finite measure spaces
**Lean source:** [Exercise06.lean](../../../Math/Rudin/Chapter11/Exercise06.lean).
**Inventory status:** Verified as stated.

**Statement.** For $n\ge1$, define $f_n(x)=1/n$ when $|x|\le n$, and $f_n(x)=0$ otherwise. These functions converge uniformly to zero on $\mathbb R$, but every integral equals $2$. There is no integrable function $g$ with $|f_n|\le g$ almost everywhere for every $n\ge1$.

In contrast, let $E$ be a measurable set of finite measure. Suppose $F_n:E\to V$ are almost-everywhere strongly measurable, each is bounded, and $F_n\to f$ uniformly on $E$. For a complete real normed space $V$, this includes real and complex values. Then a single nonnegative constant bounds every $F_n$ and $f$ on $E$. This constant is integrable on $E$, all these functions are integrable there, and

$$
\lim_{n\to\infty}\int_E F_n\,d\mu=\int_E f\,d\mu.
$$

**Proof.** The estimate $\|f_n(x)\|\le1/n$ proves uniform convergence. The indicator of $[-n,n]$ times $1/n$ is integrable, and its integral is $(2n)/n=2$ for $n\ge1$. The formal sequence also has an auxiliary index $n=0$; its value is zero, and the integral formula is asserted only for positive indices. If an integrable common majorant existed, dominated convergence applied to $f_{n+1}$ would make its integrals tend to zero. Their constant value $2$ gives a contradiction.

For the finite-measure assertion, write $\|F_n(x)\|\le C_n$. Choose $N$ so that $\|F_n(x)-f(x)\|<1$ on $E$ for $n\ge N$. First $\|f(x)\|\le|C_N|+1$, and then $\|F_n(x)\|\le|C_N|+2$ for all $n\ge N$. The finitely many earlier bounds can be included by taking

$$
B=\sum_{i=0}^{N}|C_i|+2.
$$

Thus $B\ge0$ bounds the entire sequence and its limit. This common-bound argument itself needs neither measurability nor finite measure. Finite measure makes the constant function $B$ integrable on $E$. Pointwise convergence on $E$ gives almost-everywhere strong measurability of $f$ from that of the terms. Domination proves integrability of all terms and the limit, and the dominated convergence theorem gives the integral limit. Zero measure and the empty set require no separate exclusion.

**Lean declarations:** `Rudin.Chapter11.exercise06_literal`, `Rudin.Chapter11.exercise06_bound`, `Rudin.Chapter11.exercise06_uniform_limit`, `Rudin.Chapter11.exercise06_integrable`, `Rudin.Chapter11.exercise06_integrals`, `Rudin.Chapter11.exercise06_no_domination`, `Rudin.Chapter11.exercise06_common_bound`, `Rudin.Chapter11.exercise06_finite_measure_domination`, `Rudin.Chapter11.exercise06_finite_measure_convergence`.

<a id="r11e07"></a>
### 11.7 — A criterion for raw Riemann–Stieltjes integrability
**Lean source:** [Exercise07.lean](../../../Math/Rudin/Chapter11/Exercise07.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $a\le b$, let $f:\mathbb R\to\mathbb R$, and let $\alpha:\mathbb R\to\mathbb R$ be nondecreasing on $[a,b]$. No continuity of $\alpha$ is assumed. For a weak partition $P=(a=x_0\le\cdots\le x_m=b)$, put

$$
\omega_i(f,P)=\sup_{[x_i,x_{i+1}]}f-\inf_{[x_i,x_{i+1}]}f,
\qquad
W_P(y)=\sum_{i=0}^{m-1}\omega_i(f,P)
\mathbf1_{(\alpha(x_i),\alpha(x_{i+1})]}(y).
$$

Then $f$ has a Riemann–Stieltjes integral with the actual values of $\alpha$ if and only if $f$ is bounded on $[a,b]$ and there is a sequence of weak partitions $P_n$ such that $W_{P_n}(y)\to0$ for Lebesgue-almost every mass coordinate $y$. This criterion is proved for both the Darboux definition and the equivalent definition that controls every tagged refinement of a partition. No measurability assumption on $f$ is imposed.

The criterion also implies the necessary one-sided conditions: a positive left jump of $\alpha$ at $c\in(a,b]$ requires left continuity of $f$ at $c$, and a positive right jump at $c\in[a,b)$ requires right continuity. At the two endpoints, only the inward condition applies. At an interior point with both jump parts positive, $f$ must be continuous relative to $[a,b]$. One can include these conditions explicitly in the equivalence; they already follow from boundedness and almost-everywhere vanishing of $W_{P_n}$.

**Proof.** If $|f|\le M$ on $[a,b]$, each closed-cell oscillation lies between zero and $2M$. The half-open mass intervals are disjoint apart from empty cells. Thus $W_P$ is integrable and

$$
0\le W_P\le2M\mathbf1_{(\alpha(a),\alpha(b)]},
\qquad
\int_{\mathbb R}W_P(y)\,dy=U(P,f,\alpha)-L(P,f,\alpha).
$$

The equality follows by integrating each indicator; its length is the raw increment $\alpha(x_{i+1})-\alpha(x_i)$. If an integral exists, choose partitions whose Darboux gaps are less than $1/(n+1)$. The nonnegative functions $W_{P_n}$ tend to zero in $L^1$. The standard subsequence theorem for convergence in measure gives a subsequence tending to zero almost everywhere. Conversely, if such a sequence tends to zero almost everywhere, the displayed integrable bound and dominated convergence make its Darboux gaps tend to zero. Arbitrarily small gaps give existence of the Darboux integral. The proved equivalence of the Darboux and tagged-refinement definitions gives the second formulation.

For the left jump condition, the precise local assumption is that some $d>0$ satisfies $d\le\alpha(c)-\alpha(t)$ for every $t\in[a,c)$. Any partition has a closed cell containing $c$ with left endpoint less than $c$. Its mass is at least $d$, and its oscillation times its mass is at most the full Darboux gap. A gap smaller than $d\varepsilon$ therefore gives oscillation less than $\varepsilon$ on a left neighborhood of $c$, including its value at $c$. This is left continuity. The right-side argument uses a cell whose right endpoint is greater than $c$ and the condition $d\le\alpha(t)-\alpha(c)$ for $t\in(c,b]$. Combining the two sides proves relative continuity when both jumps are positive. For globally nondecreasing $\alpha$, these assumptions follow respectively from $\alpha(c-)<\alpha(c)$ and $\alpha(c)<\alpha(c+)$.

To compare with the source's measure hint, suppose now that $\alpha$ is globally nondecreasing. Its source measure $\mu_\alpha$, formed from the right-limit normalization, has the following interval values for $u<v$:

$$
\begin{aligned}
\mu_\alpha((u,v))&=\alpha(v-)-\alpha(u+),\\
\mu_\alpha((u,v])&=\alpha(v+)-\alpha(u+),\\
\mu_\alpha([u,v))&=\alpha(v-)-\alpha(u-),\\
\mu_\alpha([u,v])&=\alpha(v+)-\alpha(u-),\\
\mu_\alpha(\{c\})&=(\alpha(c)-\alpha(c-))+(\alpha(c+)-\alpha(c)).
\end{aligned}
$$

The formal formulas use the nonnegative part when endpoints are not ordered. In particular, the raw mass of a nonempty cell is

$$
\alpha(v)-\alpha(u)=\mu_\alpha((u,v))
 +(\alpha(u+)-\alpha(u))+(\alpha(v)-\alpha(v-)).
$$

The two endpoint terms retain the split of each atom at the actual value of $\alpha$. Dropping them changes the criterion. Repeated nodes give empty mass intervals and contribute nothing. On a singleton interval every $W_P$ is zero and every real $f,\alpha$ has both integrals equal to zero. More generally, if $\alpha(a)=\alpha(b)$, integrability is equivalent to boundedness and the integral is zero; no continuity is needed.

For $\alpha(x)=x$, the criterion is precisely boundedness and continuity almost everywhere on $[a,b]$. To see necessity, discard the countable union of all partition nodes and the null set where $W_{P_n}$ fails to vanish. At a remaining point $x$, choose a partition whose oscillation at $x$ is small. The point is in the interior of one cell, so that small oscillation bounds $|f(z)-f(x)|$ for all sufficiently close $z$. This proves relative continuity almost everywhere. Conversely, on uniform grids the closed-cell oscillations tend to zero at every relative continuity point. Dominated convergence gives small Darboux gaps, and hence integrability. This includes $a=b$.

The file also proves concrete tests of the jump and endpoint conventions. Let $D(x)=\mathbf1_{(0,\infty)}(x)$ and $H(x)=\mathbf1_{[0,\infty)}(x)$. On $[-1,1]$, $D$ is integrable with respect to $H$ with integral zero: on $[-1,0]$ the integrand is zero, and on $[0,1]$ the integrator is constant. Yet $\mu_H(\{0\})=1$ and $D$ is discontinuous at zero. Thus continuity $\mu_\alpha$-almost everywhere is not necessary. In contrast, $D$ is not integrable with respect to $D$ on $[0,1]$ or $[-1,1]$, and $H$ is not integrable with respect to $H$ on $[-1,0]$. The corresponding inward jump conditions would require the false right or left continuity at zero. Moreover $D$ and $H$ give exactly the same source measure, so a change only in the raw value at a jump can change integrability without changing that measure. Even for the constant integrand $1$ on $[-1,0]$, the raw integral with respect to $D$ is zero while its normalized measure integral is one. These are limitations of the naive measure substitution, not limitations of the criterion above.

**Lean declarations:** `Rudin.Chapter11.Exercise07.exercise07`, `Rudin.Chapter11.Exercise07.exercise07_tagged`, `Rudin.Chapter11.Exercise07.exercise07_with_one_sided_conditions`, `Rudin.Chapter11.Exercise07.exercise07_id`, `Rudin.Chapter11.Exercise07.vanishingMassOscillation_of_integral`, `Rudin.Chapter11.Exercise07.integral_of_vanishingMassOscillation`, `Rudin.Chapter11.Exercise07.integral_massOscillation`, `Rudin.Chapter11.Exercise07.cellOscillation_bounds`, `Rudin.Chapter11.Exercise07.massOscillation_bounds`, `Rudin.Chapter11.Exercise07.integrable_massOscillation`, `Rudin.Chapter11.Exercise07.ae_continuous_of_vanishing_id`, `Rudin.Chapter11.Exercise07.left_continuous_of_positive_jump`, `Rudin.Chapter11.Exercise07.right_continuous_of_positive_jump`, `Rudin.Chapter11.Exercise07.continuous_of_two_positive_jumps`, `Rudin.Chapter11.Exercise07.left_continuous_of_leftLim_lt`, `Rudin.Chapter11.Exercise07.right_continuous_of_lt_rightLim`, `Rudin.Chapter11.Exercise07.sourceMeasure_Ioo`, `Rudin.Chapter11.Exercise07.sourceMeasure_Ioc`, `Rudin.Chapter11.Exercise07.sourceMeasure_Ico`, `Rudin.Chapter11.Exercise07.sourceMeasure_Icc`, `Rudin.Chapter11.Exercise07.sourceMeasure_atom`, `Rudin.Chapter11.Exercise07.raw_increment_sourceMeasure`, `Rudin.Chapter11.Exercise07.repeated_node_mass`, `Rudin.Chapter11.Exercise07.massOscillation_self`, `Rudin.Chapter11.Exercise07.exercise07_self`, `Rudin.Chapter11.Exercise07.exercise07_zero_mass`, `Rudin.Chapter11.Exercise07.exercise07_normalization_endpoint`, `Rudin.Chapter11.Exercise07.monotone_immediateStep`, `Rudin.Chapter11.Exercise07.opposite_jump_integrable`, `Rudin.Chapter11.Exercise07.shared_right_endpoint_jump_not_integrable`, `Rudin.Chapter11.Exercise07.shared_left_endpoint_jump_not_integrable`, `Rudin.Chapter11.Exercise07.shared_right_interior_jump_not_integrable`, `Rudin.Chapter11.Exercise07.positive_atom_discontinuous_integrable`, `Rudin.Chapter11.Exercise07.source_ae_continuity_not_necessary`, `Rudin.Chapter11.Exercise07.raw_value_changes_integrability`.

<a id="r11e08"></a>
### 11.8 — The derivative of a Riemann primitive almost everywhere
**Lean source:** [Exercise08.lean](../../../Math/Rudin/Chapter11/Exercise08.lean).
**Inventory status:** Verified as stated.

**Statement.** Suppose $a\le b$ and $f$ has an ordinary Riemann integral on $[a,b]$. For every $x\in[a,b]$ the Riemann integral defining $F(x)=\int_a^x f(t)\,dt$ exists, including at the endpoints. Moreover $F$ has a genuine derivative $F'(x)=f(x)$ for Lebesgue-almost every $x\in[a,b]$. Both the Darboux and tagged-refinement hypotheses are covered.

**Proof.** Split the given Darboux integral at $x$. The ordinary Riemann-to-Lebesgue bridge proves interval integrability and equality of the two integral values on $[a,x]$, without adding a measurability assumption. Thus the displayed Lebesgue primitive is the actual Riemann primitive at each point of the closed interval. Apply the standard almost-everywhere differentiation theorem for the indefinite Lebesgue integral to the interval-integrable function. It gives existence of the derivative and its value $f(x)$ almost everywhere on $[a,b]$, not merely an assigned value for a derivative operator. Endpoints are null and require no imposed derivative convention. For $a=b$ the almost-everywhere assertion is vacuous and the primitive integral is zero. The tagged version follows from its proved equivalence with Darboux integrability.

**Lean declarations:** `Rudin.Chapter11.exercise08_riemann_primitive`, `Rudin.Chapter11.exercise08_almost_everywhere_derivative`, `Rudin.Chapter11.exercise08_tagged_almost_everywhere_derivative`.

<a id="r11e09"></a>
### 11.9 — Continuity of an indefinite Lebesgue integral
**Lean source:** [Exercise09.lean](../../../Math/Rudin/Chapter11/Exercise09.lean).
**Inventory status:** Verified as stated.

**Statement.** If $a\le b$ and $f$ is Lebesgue integrable on $[a,b]$, then $F(x)=\int_a^x f(t)\,dt$ is continuous on the entire closed interval. This includes both endpoints and holds for functions with values in any complete real normed space, including $\mathbb R$ and $\mathbb C$. Riemann integrability is not assumed.

**Proof.** Apply the standard continuity theorem for an interval-integral primitive to the integrable function on the unordered closed interval, which equals $[a,b]$ because $a\le b$. The theorem follows from dominated convergence for moving interval indicators: as $x$ tends to $x_0$ within $[a,b]$, the indicators converge away from the single point $x_0$, and the norms of the integrands are bounded by the integrable function $\|f\|$. This also proves the one-sided continuity required at each endpoint. On a singleton interval the primitive is zero.

**Lean declarations:** `Rudin.Chapter11.exercise09_continuity`.

<a id="r11e10"></a>
### 11.10 — The finite-measure inclusion and an infinite-measure counterexample
**Lean source:** [Exercise10.lean](../../../Math/Rudin/Chapter11/Exercise10.lean).
**Inventory status:** Verified as stated.

**Statement.** On a finite measure space, every $L^2$ function is integrable. This includes zero measure and normed-group-valued functions under the usual almost-everywhere strong measurability convention. On $\mathbb R$ with Lebesgue measure,

$$
f(x)=\frac1{1+|x|}
$$

is continuous and belongs to $L^2$, but is not integrable. The total measure of this space is infinite.

**Proof.** The standard comparison of $L^p$ exponents on finite measure spaces gives $L^2\subseteq L^1$, and membership in $L^1$ is equivalent to integrability. It does not require positive total measure. For the example, continuity follows from positivity of $1+|x|$. The standard integrability theorem for $(1+\|x\|)^{-r}$ in dimension one, with $r=2>1$, proves integrability of $f^2$ and hence $L^2$ membership.

If $f$ were integrable, then $2f$ would be integrable. For $x>1$,

$$
\frac1x\le\frac2{1+x}=2f(x).
$$

Domination would make $x^{-1}$ integrable on $(1,\infty)$. The power-integral criterion says $x^r$ is integrable there only for $r<-1$, contradicting $r=-1$. Thus infinite measure does not permit the unrestricted inclusion.

**Lean declarations:** `Rudin.Chapter11.exercise10_finite_measure_inclusion`, `Rudin.Chapter11.exercise10_continuous`, `Rudin.Chapter11.exercise10_square_integrable`, `Rudin.Chapter11.exercise10_memLp_two`, `Rudin.Chapter11.exercise10_nonintegrable`, `Rudin.Chapter11.exercise10_infinite_measure`.

<a id="r11e11"></a>
### 11.11 — The complete metric space of integrable function classes
**Lean source:** [Exercise11.lean](../../../Math/Rudin/Chapter11/Exercise11.lean).
**Inventory status:** Verified as stated.

**Statement.** Identify integrable functions that agree almost everywhere. On these $L^1(\mu)$ classes,

$$
d(f,g)=\int_X\|f(x)-g(x)\|\,d\mu
$$

is a complete metric when the values lie in a complete real normed space, including real and complex scalars. No finiteness assumption on $\mu$ is required. On actual functions the same formula is only a pseudometric, as the chapter's almost-everywhere quotient convention requires.

**Proof.** The difference of two integrable representatives is integrable, and so is its norm. If either representative is replaced by an almost-everywhere equal function, the integrand changes only on a null set, so its integral is unchanged. The $L^1$ distance formula identifies this integral exactly with the norm distance on the library's quotient space at exponent one. Thus nonnegativity, symmetry, and the triangle inequality follow from the norm metric, and distance zero means equality of classes. For raw integrable functions it means exactly equality almost everywhere. Mapping each raw function to its $L^1$ class preserves the displayed distance.

The standard completeness theorem for $L^p$, at $p=1$ and for complete target space, supplies completeness of this metric. Consequently a Cauchy sequence of classes has a class $f\in L^1$ such that

$$
\int_X\|f_n(x)-f(x)\|\,d\mu\longrightarrow0.
$$

Finally, on $[0,1]$ with Lebesgue measure take the actual functions $f=\mathbf1_{\{0\}}$ and $g=0$. Both are integrable and agree almost everywhere, but $f(0)=1\ne0=g(0)$. Their distance is zero. This proves the failure of pointwise separation without the quotient; it is not a refutation of the source under its stated convention.

**Lean declarations:** `Rudin.Chapter11.exercise11_distance`, `Rudin.Chapter11.exercise11_norm_difference`, `Rudin.Chapter11.exercise11_distance_integrable`, `Rudin.Chapter11.exercise11_metric_axioms`, `Rudin.Chapter11.exercise11_representative_independence`, `Rudin.Chapter11.exercise11_toL1_distance`, `Rudin.Chapter11.exercise11_zero_iff_ae`, `Rudin.Chapter11.exercise11_complete`, `Rudin.Chapter11.exercise11_cauchy_converges`, `Rudin.Chapter11.exercise11_raw_function_degeneracy`.

<a id="r11e12"></a>
### 11.12 — Integrating a separately continuous function
**Lean source:** [Exercise12.lean](../../../Math/Rudin/Chapter11/Exercise12.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $f:[0,1]^2\to\mathbb R$ or $\mathbb C$ be separately continuous and satisfy $\|f(x,y)\|\le1$. Then

$$
g(x)=\int_0^1 f(x,y)\,dy
$$

is continuous on the closed interval $[0,1]$, including its endpoints. Every section integral exists. The continuity result also holds with values in any complete real normed space. Joint continuity and joint measurability are not assumed. Separate results identify the real and complex section integrals as actual Riemann integrals, not just totalized Lebesgue values.

**Proof.** For each fixed $x$, continuity of $y\mapsto f(x,y)$ on a compact interval proves its interval integrability and supplies its measurability. At a fixed $x_0\in[0,1]$, continuity of $x\mapsto f(x,y)$ for each $y$ gives convergence of the sections as $x\to x_0$ within $[0,1]$. Their norms are bounded by the integrable constant $1$. The parameter form of dominated convergence therefore proves continuity of $g$ relative to $[0,1]$, so the same argument covers one-sided endpoint limits.

For real sections, boundedness and continuity imply the closed-cell Darboux Riemann criterion and equality with the Lebesgue interval integral. For complex sections, apply the real result to real and imaginary parts; each is bounded by the complex norm. The proved equivalence between complex tagged sums and their two real components then gives the complex Riemann integral, with the same value because integration commutes with the two coordinates.

**Lean declarations:** `Rudin.Chapter11.exercise12_section_integrable`, `Rudin.Chapter11.exercise12_continuity`, `Rudin.Chapter11.exercise12_real_riemann`, `Rudin.Chapter11.exercise12_complex_riemann`.

<a id="r11e13"></a>
### 11.13 — A closed bounded noncompact set in L²
**Lean source:** [Exercise13.lean](../../../Math/Rudin/Chapter11/Exercise13.lean).
**Inventory status:** Verified as stated.

**Statement.** In real $L^2([-\pi,\pi])$ with Lebesgue measure and equality almost everywhere, let $s_n$ be the class of $x\mapsto\sin(nx)$, $n\ge1$. The set $\{s_n:n\ge1\}$ is closed and bounded but not compact. More precisely,

$$
\|s_n\|^2=\pi,\qquad d(s_n,s_m)=\sqrt{2\pi}\quad(n\ne m).
$$

The file also proves that the normalized sine classes are orthonormal and that the sine coefficients of every fixed $L^2$ vector tend to zero. In particular, for every Lebesgue-measurable $E\subseteq[-\pi,\pi]$,

$$
\int_E\sin(nx)\,dx\longrightarrow0\quad(n\to\infty).
$$

**Proof.** The literal sine functions are measurable and bounded by one on a finite-measure interval, so they define $L^2$ classes. The integral of $\cos(kx)$ on $[-\pi,\pi]$ is zero for every nonzero integer $k$. The identity

$$
\sin(nx)\sin(mx)=\frac{\cos((n-m)x)-\cos((n+m)x)}2
$$

therefore gives inner product $\pi$ when $n=m$ and zero otherwise. The diagonal identity gives norm $\sqrt\pi$; expanding the squared norm of a difference gives squared distance $2\pi$ for distinct indices. The classes are represented by the displayed literal functions almost everywhere, so these are their actual $L^2$ distances.

A sequence with pairwise distances at least the positive constant $\sqrt{2\pi}$ is a closed embedding of the discrete index space. Its range is closed, and its constant norm makes it bounded. If the range were compact, this embedding would make the infinite discrete space of natural-number indices compact. A compact discrete space is finite, which is a contradiction.

Dividing the sine classes by $\sqrt\pi$ gives an orthonormal family. Bessel's inequality makes the squared inner products with any fixed vector summable, so the coefficients tend to zero. The indicator of any Lebesgue-measurable subset $E$ belongs to this $L^2$ space. Its inner products with the sine classes are exactly the displayed set integrals, proving their limit. The formal indicator results use null measurability, so they do not restrict $E$ to Borel sets. The formal indices are $n+1$ with $n\in\mathbb N$.

**Lean declarations:** `Rudin.Chapter11.exercise13_closedness`, `Rudin.Chapter11.exercise13_boundedness`, `Rudin.Chapter11.exercise13_noncompactness`, `Rudin.Chapter11.SineL2.memLp_sin`, `Rudin.Chapter11.SineL2.sine_ae`, `Rudin.Chapter11.SineL2.integral_cos_int`, `Rudin.Chapter11.SineL2.integral_sine_mul`, `Rudin.Chapter11.SineL2.inner_sine`, `Rudin.Chapter11.SineL2.norm_sine_sq`, `Rudin.Chapter11.SineL2.norm_sine`, `Rudin.Chapter11.SineL2.dist_sine`, `Rudin.Chapter11.SineL2.closedEmbedding_sine`, `Rudin.Chapter11.SineL2.orthonormal_normalized`, `Rudin.Chapter11.SineL2.tendsto_inner_sine`, `Rudin.Chapter11.SineL2.memLp_indicator`, `Rudin.Chapter11.SineL2.inner_sine_indicator`, `Rudin.Chapter11.SineL2.tendsto_setIntegral_sine`.

<a id="r11e14"></a>
### 11.14 — Complex measurability and open preimages
**Lean source:** [Exercise14.lean](../../../Math/Rudin/Chapter11/Exercise14.lean).
**Inventory status:** Verified as stated.

**Statement.** For a function $f:X\to\mathbb C$ on a measurable space, measurability of both $\operatorname{Re}f$ and $\operatorname{Im}f$ is equivalent to measurability of $f^{-1}(V)$ for every open $V\subseteq\mathbb C$.

**Proof.** The standard coordinate characterization of the Borel measurable structure on $\mathbb C$ says that measurable real and imaginary parts make $f$ measurable. The preimage of any open set is then measurable, since open sets are Borel. Conversely, the Borel sigma-algebra is generated by open sets. Measurable preimages of all open sets therefore imply measurability of $f$. Composing it with the continuous real and imaginary coordinate maps gives both coordinate measurability assertions. Combining these directions gives the equivalence.

**Lean declarations:** `Rudin.Chapter11.exercise14_open_preimages`, `Rudin.Chapter11.exercise14_coordinate_measurability`, `Rudin.Chapter11.exercise14`.

<a id="r11e15"></a>
### 11.15 — An additive elementary charge with no countably additive extension
**Lean source:** [Exercise15.lean](../../../Math/Rudin/Chapter11/Exercise15.lean).
**Inventory status:** Verified as stated.

**Statement.** On the ring of elementary subsets of $(0,1]$, the following prescriptions determine a well-defined, finite, nonnegative, finitely additive real set function $\phi$. Each of $[a,b]$, $[a,b)$, $(a,b]$, and $(a,b)$ has value $b-a$ when $0<a\le b\le1$. Both $(0,b)$ and $(0,b]$ have value $1+b$ when $0<b\le1$. Empty intervals and all singletons in $(0,1]$ have value zero. The charge is not regular in the sense of ambient-real closed inner sets and open outer sets. It has no countably additive extension to any sigma-ring containing the elementary ring, even if signed extended-real values are permitted.

**Proof.** An elementary set is a finite union of order-connected subsets of $(0,1]$. Each such subset is one of the four interval types, including empty intervals and singletons. Intersections remain intervals, and the difference of two intervals splits into at most two disjoint intervals. Thus the finite unions form a ring, and every elementary set has a finite disjoint interval decomposition.

Say that $A$ contains the right germ at zero if it contains every sufficiently small positive number. For an interval in $(0,1]$, either it or its complement contains this germ. To prove this, if the interval has points arbitrarily close to zero, fix any one of its positive points and use order-connectedness between that point and smaller points. This gives a whole right neighborhood of zero inside the interval. Otherwise some right neighborhood misses the interval. Finite unions preserve this dichotomy. Hence the literal indicator of every elementary set is eventually constant, with value zero or one, as $x\downarrow0$.

Define canonically on sets

$$
\phi(A)=m(A)+\mathbf1_{\{A\text{ contains the right germ at }0\}}.
$$

Every elementary set is measurable and contained in $(0,1]$, so this value is finite. Intervals bounded away from zero have no germ and have their usual length, including the degenerate cases. The two intervals starting at zero contain the germ and have value $1+b$. For disjoint elementary sets, both cannot contain the germ, and their union contains it exactly when one does. Thus the germ term is additive on disjoint pairs, as is length. Induction gives finite additivity for every finite disjoint family. The sum over any disjoint interval decomposition equals this canonical set value, so different decompositions give the same sum. The file proves these statements both for a finite nonnegative extended-value encoding and for the real charge, with a proved comparison between them.

For nonregularity, take $A=(0,1/2)$, whose charge is $3/2$. Every ambient-real closed $F\subseteq(0,1]$ is compact and bounded away from zero: the open complement of $F$ contains a neighborhood of zero. Therefore a closed elementary $F\subseteq A$ has no germ and $\phi(F)=m(F)\le1/2$. The inner regularity inequality with $\varepsilon=1/2$ would give $3/2\le\phi(F)+1/2\le1$, a contradiction. The same witness disproves the weaker variant with relative openness of outer sets at the endpoint $1$; the inner sets must still be closed in $\mathbb R$. Relative closedness of the inner sets would be a different condition.

Finally, the elementary intervals

$$
D_n=(2^{-(n+1)},2^{-n}],\qquad n\ge0,
$$

are pairwise disjoint and have union $(0,1]$. Each is bounded away from zero, so its charge equals its length. Consequently

$$
\sum_{n=0}^{\infty}\phi(D_n)=1,
\qquad \phi\!\left(\bigcup_{n=0}^{\infty}D_n\right)=\phi((0,1])=2.
$$

Any countably additive extension agreeing on the elementary sets would contradict these equalities. This argument needs only that the extension's domain contain the elementary ring, not additional topology. For a signed extended-real extension, its ordered partial sums on this same family are finite real sums tending to $1$, while countable additivity would make them tend to the union's value $2$. Uniqueness of limits gives the same contradiction. Thus the obstruction covers the source's signed extension convention as well as nonnegative measures.

**Lean declarations:** `Rudin.Chapter11.ElementaryCharge.elementary_ring`, `Rudin.Chapter11.ElementaryCharge.intervals_semiring`, `Rudin.Chapter11.ElementaryCharge.intervals_eq_fourIntervals`, `Rudin.Chapter11.ElementaryCharge.elementary_eq_fourIntervals`, `Rudin.Chapter11.ElementaryCharge.disjoint_decomposition`, `Rudin.Chapter11.ElementaryCharge.elementary_iff_finite_disjoint`, `Rudin.Chapter11.ElementaryCharge.interval_germ_constant`, `Rudin.Chapter11.ElementaryCharge.germ_union_constant`, `Rudin.Chapter11.ElementaryCharge.germ_constant`, `Rudin.Chapter11.ElementaryCharge.indicator_germ_constant`, `Rudin.Chapter11.ElementaryCharge.eventual_membership`, `Rudin.Chapter11.ElementaryCharge.subset_domain`, `Rudin.Chapter11.ElementaryCharge.measurable`, `Rudin.Chapter11.ElementaryCharge.finite_value`, `Rudin.Chapter11.ElementaryCharge.germ_not_compl`, `Rudin.Chapter11.ElementaryCharge.germ_add`, `Rudin.Chapter11.ElementaryCharge.additive`, `Rudin.Chapter11.ElementaryCharge.φ_empty`, `Rudin.Chapter11.ElementaryCharge.finite_additivity`, `Rudin.Chapter11.ElementaryCharge.well_defined`, `Rudin.Chapter11.ElementaryCharge.not_germ_of_away`, `Rudin.Chapter11.ElementaryCharge.interval_prescriptions`, `Rudin.Chapter11.ElementaryCharge.intervals_elementary`, `Rudin.Chapter11.ElementaryCharge.singleton_value`, `Rudin.Chapter11.ElementaryCharge.zero_interval_prescriptions`, `Rudin.Chapter11.ElementaryCharge.zero_intervals_elementary`, `Rudin.Chapter11.ElementaryCharge.charge_nonneg`, `Rudin.Chapter11.ElementaryCharge.ofReal_charge`, `Rudin.Chapter11.ElementaryCharge.charge_formula`, `Rudin.Chapter11.ElementaryCharge.charge_interval_prescriptions`, `Rudin.Chapter11.ElementaryCharge.charge_zero_interval_prescriptions`, `Rudin.Chapter11.ElementaryCharge.charge_finite_additivity`, `Rudin.Chapter11.ElementaryCharge.charge_well_defined`, `Rudin.Chapter11.ElementaryCharge.charge_empty`, `Rudin.Chapter11.ElementaryCharge.closed_away_zero`, `Rudin.Chapter11.ElementaryCharge.compact_away_zero`, `Rudin.Chapter11.ElementaryCharge.closed_subset_compact`, `Rudin.Chapter11.ElementaryCharge.regular_implies_endpoint_regular`, `Rudin.Chapter11.ElementaryCharge.nonregular_endpoint`, `Rudin.Chapter11.ElementaryCharge.nonregular`, `Rudin.Chapter11.ElementaryCharge.dyadic_elementary`, `Rudin.Chapter11.ElementaryCharge.dyadic_disjoint`, `Rudin.Chapter11.ElementaryCharge.dyadic_union`, `Rudin.Chapter11.ElementaryCharge.dyadic_value`, `Rudin.Chapter11.ElementaryCharge.no_countable_extension`, `Rudin.Chapter11.ElementaryCharge.dyadic_charge_hasSum`, `Rudin.Chapter11.ElementaryCharge.no_extendedReal_countable_extension`.

<a id="r11e16"></a>
### 11.16 — Sine subsequences converge only on a null set
**Lean source:** [Exercise16.lean](../../../Math/Rudin/Chapter11/Exercise16.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $(n_k)$ be a strictly increasing sequence of positive integers. The exact pointwise convergence set

$$
E=\{x\in(-\pi,\pi):\sin(n_kx)\text{ converges to a finite real limit}\}
$$

is measurable and has Lebesgue measure zero. Its measurability holds for every natural-number frequency sequence, without the increasing or positivity assumptions.

**Proof.** Each $x\mapsto\sin(n_kx)$ is continuous and measurable. The measurable convergence-set theorem, intersected with $(-\pi,\pi)$, proves measurability of the exact set $E$; no exceptional points are removed from its definition. It has finite measure.

The cosine classes of positive integer frequencies on $[-\pi,\pi]$ have inner product $\pi$ at equal frequencies and zero otherwise, by the cosine product identity and the zero integrals of nonconstant integer-frequency cosines. Normalizing them gives an orthonormal family. Bessel's inequality makes the coefficients of the $L^2$ indicator of $E$ tend to zero. After identifying the classes with their literal representatives almost everywhere, this says

$$
\int_E\cos(rx)\,dx\longrightarrow0\quad(r\in\mathbb N,\ r\to\infty).
$$

Put $a_k=n_{2k+1}$ and $b_k=n_k$. On $E$, convergence of the sine sequence implies

$$
h_k(x)=(\sin(a_kx)-\sin(b_kx))^2\longrightarrow0.
$$

Since $0\le h_k\le4$ and $m(E)<\infty$, dominated convergence gives $\int_Eh_k\to0$. On the other hand,

$$
h_k(x)=1-\frac12\cos(2a_kx)-\frac12\cos(2b_kx)
-\cos((a_k-b_k)x)+\cos((a_k+b_k)x).
$$

Strict increase of the natural-number frequencies gives $n_k\ge k$ and $n_{2k+1}-n_k\ge k+1$. Thus all four cosine frequencies in this identity tend to infinity. Their set integrals tend to zero by the preceding Bessel argument, so $\int_Eh_k\to m(E)$. Uniqueness of limits gives $m(E)=0$. Finiteness of $m(E)$ ensures that a zero real-valued measure is indeed zero measure, not the default real value of infinity.

**Lean declarations:** `Rudin.Chapter11.exercise16_measurability`, `Rudin.Chapter11.exercise16_null_convergence_set`, `Rudin.Chapter11.CosineL2.memLp_cos`, `Rudin.Chapter11.CosineL2.cosine_ae`, `Rudin.Chapter11.CosineL2.integral_cosine_mul`, `Rudin.Chapter11.CosineL2.inner_cosine`, `Rudin.Chapter11.CosineL2.orthonormal_normalized`, `Rudin.Chapter11.CosineL2.tendsto_inner_cosine`, `Rudin.Chapter11.CosineL2.inner_cosine_indicator`, `Rudin.Chapter11.CosineL2.tendsto_setIntegral_cosine`.

<a id="r11e17"></a>
### 11.17 — Only finitely many uniformly positive sine frequencies
**Lean source:** [Exercise17.lean](../../../Math/Rudin/Chapter11/Exercise17.lean).
**Inventory status:** Verified as stated.

**Statement.** If $E\subseteq(-\pi,\pi)$ is Lebesgue measurable with positive measure and $\delta>0$, then

$$
\{n\in\mathbb Z:\sin(nx)\ge\delta\text{ for every }x\in E\}
$$

is finite. The condition is pointwise on all of $E$, includes equality with $\delta$, and allows negative as well as positive integer frequencies. The formal assumption is null measurability, so arbitrary Lebesgue-measurable sets are included.

**Proof.** Since $E$ is contained in a bounded interval, $0<m(E)<\infty$. Apply the sine coefficient limit proved from Bessel's inequality in Exercise 13 to the actual $L^2$ indicator of $E$. With $c=\delta m(E)>0$, choose $N$ such that

$$
-c<\int_E\sin((k+1)x)\,dx<c\qquad(k\ge N).
$$

For any real frequency $t$ whose sine is at least $\delta$ on $E$, monotonicity of the integral gives

$$
c\le\int_E\sin(tx)\,dx.
$$

All integrals exist because sine is bounded and $E$ has finite measure. For a positive integer $n=k+1$ satisfying the pointwise condition, the upper bound above forces $k<N$. For a negative integer $n=-(k+1)$, oddness of sine makes its integral the negative of the positive-frequency integral; the lower bound above again forces $k<N$. Frequency zero is impossible because its integral is zero while $c>0$. Hence all admissible integers lie in the finite interval $[-N,N]$.

**Lean declarations:** `Rudin.Chapter11.exercise17_finite_frequencies`.

<a id="r11e18"></a>
### 11.18 — Schwarz equality and the missing zero case
**Lean source:** [Exercise18.lean](../../../Math/Rudin/Chapter11/Exercise18.lean).
**Inventory status:** Verified refutation and correction.

**Statement.** For complex square-integrable functions $f,g$ on a measure space, the printed claim is

$$
\left|\int f\overline g\,d\mu\right|^2
=\left(\int|f|^2\,d\mu\right)\left(\int|g|^2\,d\mu\right)
\quad\Longleftrightarrow\quad
 g=cf\ \text{almost everywhere for some }c\in\mathbb C.
$$

The implication from proportionality to equality is valid, but the unrestricted reverse implication is false.

**Correction.** On an arbitrary measure space, the complete criterion is

$$
\left|\int f\overline g\,d\mu\right|^2
=\left(\int|f|^2\,d\mu\right)\left(\int|g|^2\,d\mu\right)
\quad\Longleftrightarrow\quad
 f=0\ \text{almost everywhere}\ \text{or}\ 
 g=cf\ \text{almost everywhere for some }c\in\mathbb C.
$$

Thus the printed equivalence holds if one adds the explicit assumption that $f$ is not zero almost everywhere. No finite-total-measure assumption is required. Square integrability in the file includes almost-everywhere strong measurability and finite $L^2$ seminorm.

**Proof.** First consider the one-point space $X=\{*\}$ with unit point mass, and take $f(*)=0$, $g(*)=1$. Both functions are square integrable: their squared-norm integrals are $0$ and $1$. The displayed equality is $0=0\cdot1$. But no scalar satisfies $1=c\cdot0$ at the point of full measure. This refutes the printed necessity even on a finite measure space.

For the correction, let $F,G$ denote the classes of $f,g$ in complex $L^2(\mu)$. Its inner product, with the convention that the first argument is conjugate-linear, gives

$$
\langle G,F\rangle=\int f\overline g\,d\mu,\qquad
\|F\|^2=\int|f|^2\,d\mu,\qquad
\|G\|^2=\int|g|^2\,d\mu.
$$

The products are integrable by the $L^2$ inner-product theorem. Equality in the squared formula is equivalent to $|\langle G,F\rangle|=\|F\|\|G\|$, because both sides are nonnegative. The standard equality criterion for Cauchy–Schwarz in an inner-product space states that this holds exactly when $F=0$ or $G=cF$ for some complex scalar. Equality of $L^2$ classes is precisely equality almost everywhere of representatives. This gives the corrected assertion and, when $f$ is not zero almost everywhere, the printed equivalence with that additional hypothesis.

For completeness, if $g=cf$ almost everywhere and $A=\int|f|^2\,d\mu$, then

$$
\int f\overline g\,d\mu=\overline c\,A,
\qquad \int|g|^2\,d\mu=|c|^2A.
$$

Both sides of Schwarz equality are therefore $|c|^2A^2$. If $f=0$ almost everywhere, both sides are zero for every $g\in L^2$. If $g=0$ almost everywhere, proportionality holds with $c=0$. These observations include the both-zero case and show why no zero-function case can be omitted.

**Lean declarations:** `exercise18_proportional_implies_equality`, `exercise18_original_counterexample`, `exercise18_of_not_ae_zero`, `exercise18`, `exercise18_L2`, `exercise18_inner_integral`, `exercise18_norm_sq_integral`.
