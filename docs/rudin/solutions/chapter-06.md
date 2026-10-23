<a id="chapter-06"></a>

# Chapter 6 — The Riemann–Stieltjes Integral

[All chapters](../solutions.md) · [Previous chapter](chapter-05.md) · [Next chapter](chapter-07.md)

**Exercises:** [1](#r06e01) · [2](#r06e02) · [3](#r06e03) · [4](#r06e04) · [5](#r06e05) · [6](#r06e06) · [7](#r06e07) · [8](#r06e08) · [9](#r06e09) · [10](#r06e10) · [11](#r06e11) · [12](#r06e12) · [13](#r06e13) · [14](#r06e14) · [15](#r06e15) · [16](#r06e16) · [17](#r06e17) · [18](#r06e18) · [19](#r06e19)

Throughout this chapter, $\alpha$ is real-valued. The notation $f\in\mathcal R(\alpha)$ refers to the literal Riemann–Stieltjes integral on the stated compact interval, not to a measure integral obtained by changing $\alpha$. A partition has nodes $a=x_0\le\cdots\le x_n=b$, with $n\ge1$. Its lower and upper sums use the infimum and supremum of $f$ on each **closed** cell, multiplied by $\alpha(x_{i+1})-\alpha(x_i)$. The integrator is nondecreasing on $[a,b]$, the integrand is bounded there, and integrability means that the supremum of lower sums equals the infimum of upper sums. Repeated nodes contribute zero. Thus all integrals over singleton intervals are zero.

The support results prove equivalence with convergence of every tagged refinement of a suitable partition; tags may be cell endpoints. For complex functions, the definition uses norm convergence of the complex tagged sums with these same real increments. This is equivalent to integrability of both real components. No right-continuous normalization of a raw integrator is made. Ordinary Riemann integration means $\alpha(x)=x$.

The support bridges used below have specific scopes. Continuous functions have literal integrals for every interval-nondecreasing $\alpha$, by uniform continuity and small Darboux gaps. Identification with a Stieltjes measure integral requires an already right-continuous Stieltjes function. For the identity integrator, every literal proper Riemann integral equals the Lebesgue interval integral, without extra continuity or measurability assumptions. A bounded function continuous almost everywhere is literally Riemann integrable: closed-cell step envelopes have gaps tending to zero almost everywhere, and dominated convergence makes their integral gaps tend to zero. These bridges justify the measure-theoretic steps below; they do not redefine the source integrals.

<a id="r06e01"></a>
### 6.1 — A function supported at one point
**Lean source:** [Exercise01.lean](../../../Math/Rudin/Chapter06/Exercise01.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $a\le b$, $x_0\in[a,b]$, and let $\alpha$ be nondecreasing on $[a,b]$ and continuous at $x_0$ relative to that interval. Define $f(x_0)=1$ and $f(x)=0$ for $x\ne x_0$. Then $f\in\mathcal R(\alpha)$ and

$$
\int_a^b f\,d\alpha=0.
$$

The hypotheses include either endpoint and impose no conditions outside $[a,b]$.

**Proof.** Every positive-length cell contains a point other than $x_0$, so its lower contribution is zero. A zero-length cell also contributes zero. Thus every lower sum is zero, and all upper sums are nonnegative.

If $a<b$, relative continuity gives $u\le x_0\le v$ in $[a,b]$, with $u<v$ and $\alpha(v)-\alpha(u)<\varepsilon$. Choose $u<x_0$ unless $u=a=x_0$, and $x_0<v$ unless $v=b=x_0$. A partition containing $u,v$ isolates the support in $[u,v]$; omit any empty outer interval. Its upper sum is at most $\alpha(v)-\alpha(u)<\varepsilon$. Hence the upper integral is zero as well. If $a=b$, every increment is zero, which proves the same conclusion.

**Lean declarations:** `exercise01`, `exercise01_of_lt`, `pointSpike_lowerSum`, `pointSpike_upperSum_nonneg`, `pointSpike_small_upperSum`.

<a id="r06e02"></a>
### 6.2 — Zero integral and the role of continuity
**Lean source:** [Exercise02.lean](../../../Math/Rudin/Chapter06/Exercise02.lean).
**Inventory status:** Verified as stated.

**Statement.** Suppose $a<b$, $f:[a,b]\to\mathbb R$ is continuous and nonnegative, and its ordinary Riemann integral is zero. Then $f(x)=0$ for every $x\in[a,b]$, including the endpoints.

For comparison with Exercise 6.1, the function $h=\mathbf1_{\{1/2\}}$ on $[0,1]$ is nonnegative, has ordinary integral zero, and satisfies $h(1/2)=1$, but is not continuous. Also, the vanishing assertion fails on a singleton interval even for the continuous constant function $1$.

**Proof.** The continuous identity-integrator bridge identifies the given integral with the ordinary interval integral. If $f(x_0)>0$ anywhere in $[a,b]$, continuity gives a relative neighborhood on which $f$ has a positive lower bound. Since $a<b$, that neighborhood contains an interval of positive length, also when $x_0$ is an endpoint. Nonnegativity elsewhere then makes the integral strictly positive, a contradiction.

Exercise 6.1 with $\alpha(x)=x$ proves the zero integral of $h$. Its value at $1/2$ is $1$. If it were continuous on $[0,1]$, the preceding result would force that value to be zero. Finally, $\int_a^a1\,dx=0$, although $1\ne0$ at $a$.

**Scope.** The comparison removes continuity of the **integrand**, not continuity of the integrator in Exercise 6.1. It does not refute the continuous theorem.

**Lean declarations:** `exercise02`, `exercise02_comparison`, `exercise02_singleton_obstruction`.

<a id="r06e03"></a>
### 6.3 — Three values at a jump
**Lean source:** [Exercise03.lean](../../../Math/Rudin/Chapter06/Exercise03.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $f:[-1,1]\to\mathbb R$ be bounded. Each $\beta_j$ is zero for $x<0$ and one for $x>0$, while

$$
\beta_1(0)=0,\qquad\beta_2(0)=1,\qquad\beta_3(0)=\tfrac12.
$$

1. $f\in\mathcal R(\beta_1)$ if and only if $\lim_{x\downarrow0}f(x)=f(0)$.
2. $f\in\mathcal R(\beta_2)$ if and only if $\lim_{x\uparrow0}f(x)=f(0)$.
3. $f\in\mathcal R(\beta_3)$ if and only if $f$ is continuous at zero.
4. Every integral that exists in these cases equals $f(0)$. In particular, continuity at zero gives all three integrals and the same value. No continuity away from zero is required.

**Proof.** More generally, put $\beta(0)=c$ with $0\le c\le1$. A cell with nonzero increment must contain zero. Tag every such cell at zero. The sum is then exactly $f(0)$, because all increments telescope to $1$. Consequently any integral value must be $f(0)$.

Suppose the tagged sums converge. In a partition controlling their error, change one tag in a cell containing zero from $0$ to $y$. The resulting error is

$$
|f(y)-f(0)|\,|\beta(x_{i+1})-\beta(x_i)|.
$$

The cell where the partition first crosses into $(0,1]$ has increment at least $1-c$. If $c<1$, control of this error forces right continuity at zero. The cell where it first reaches $[0,1]$ from the left has increment at least $c$; if $c>0$, the same argument forces left continuity.

Conversely, assume continuity on each side whose coefficient is nonzero. Insert $-d,0,d$ into a partition, with $0<d\le1$ sufficiently small. In every refinement, cells with nonzero increments lie on the required side within distance $d$ of zero. Their tag values differ from $f(0)$ by less than $\varepsilon$. The absolute error is at most $\varepsilon$ times the total increment, which is $1$. A side with coefficient zero contributes nothing and needs no continuity. Apply this with $c=0,1,1/2$ and use the proved Darboux–tagged equivalence.

**Scope.** The actual values $\beta_j(0)$ are essential. Replacing them by right limits would change the problem.

**Lean declarations:** `exercise03_a_integrability`, `exercise03_a_integral`, `exercise03_a_value`, `exercise03_b_integrability`, `exercise03_b_integral`, `exercise03_b_value`, `exercise03_c_integrability`, `exercise03_c_integral`, `exercise03_c_value`, `exercise03_d`, `exercise03_beta_negative`, `exercise03_beta_positive`.

<a id="r06e04"></a>
### 6.4 — The rational indicator is not Riemann integrable
**Lean source:** [Exercise04.lean](../../../Math/Rudin/Chapter06/Exercise04.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $D(x)=1$ on rational points and $D(x)=0$ on irrational points. For $a\le b$, its lower Darboux integral is $0$ and its upper Darboux integral is $b-a$. Thus it is not Riemann integrable when $a<b$, either in the Darboux or equivalent tagged sense. The same holds for any function with these values on $[a,b]$, regardless of its values outside that interval.

**Proof.** Both rational and irrational points occur in every positive-length cell. Its infimum is therefore $0$ and its supremum is $1$. Repeated-node cells have zero weight. Every lower sum is $0$, while every upper sum is

$$
\sum_i(x_{i+1}-x_i)=b-a.
$$

Taking the two extrema gives the stated values. They differ precisely when $a<b$. On a singleton they both vanish. Equality of functions on the interval preserves all these sums, which gives the final formulation.

**Lean declarations:** `exercise04`, `exercise04_source`, `exercise04_darboux_extrema`, `exercise04_tagged`, `rationalIndicator_lowerSum`, `rationalIndicator_upperSum`.

<a id="r06e05"></a>
### 6.5 — Integrable squares and cubes
**Lean source:** [Exercise05.lean](../../../Math/Rudin/Chapter06/Exercise05.lean).
**Inventory status:** Verified as stated.

**Statement.** For bounded real functions, integrability of $f^2$ does not imply integrability of $f$ on a nondegenerate interval. In contrast, if $a\le b$ and $f^3\in\mathcal R(\alpha)$, then $f\in\mathcal R(\alpha)$. This includes ordinary Riemann integrals and the equivalent tagged formulation.

**Proof.** Let $f=2D-1$, with $D$ from Exercise 6.4. Then $f$ is $1$ on rational points and $-1$ on irrational points; hence $|f|=1$, $f^2=1$, and $\int_a^bf^2\,dx=b-a$, including $a=b$. If $f$ were integrable for $a<b$, linearity would make $D=(f+1)/2$ integrable, contrary to Exercise 6.4.

For the cube, use the continuous signed cube root

$$
r(y)=(\max(y,0))^{1/3}-(\max(-y,0))^{1/3}.
$$

Both power bases are nonnegative. Splitting into $y\ge0$ and $y\le0$ proves continuity at all points, $r(x^3)=x$, and $r(y)^3=y$, including negative inputs and zero. The bounded range of the integrable function $f^3$ lies in a compact interval. The continuous-composition theorem for literal Riemann–Stieltjes integrals therefore makes $r\circ f^3=f$ integrable.

**Scope.** The cube theorem needs no separate bound on $f$: boundedness of $f^3$, already included in its integrability, suffices. The assertion is for real functions, not arbitrary complex cube roots.

**Lean declarations:** `exercise05_square`, `exercise05_square_integral`, `exercise05_sign_nonintegrable`, `exercise05_cube`, `exercise05_cube_stieltjes`, `exercise05_cube_tagged`, `continuous_signedCubeRoot`, `signedCubeRoot_cube`, `cube_signedCubeRoot`.

<a id="r06e06"></a>
### 6.6 — Discontinuities confined to the Cantor set
**Lean source:** [Exercise06.lean](../../../Math/Rudin/Chapter06/Exercise06.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $P$ be the middle-thirds Cantor set. Suppose $f:[0,1]\to\mathbb R$ satisfies $|f(x)|\le M$ and is continuous relative to $[0,1]$ at every point outside $P$. Then $f$ is ordinarily Riemann integrable, and its literal integral equals its Lebesgue interval integral. No continuity is required at points of $P$, including $0$ and $1$.

**Proof.** The compact set $P$ has finite Lebesgue measure $m$. Its self-similarity is

$$
P=\tfrac13P\ \cup\ \tfrac13(2+P).
$$

Translation invariance and scaling of Lebesgue measure give $m\le m/3+m/3$. Finiteness and nonnegativity imply $m=0$. Thus the given bounded function is relatively continuous almost everywhere. The support criterion described above supplies arbitrarily small literal Darboux gaps and the asserted integral, not merely an almost-everywhere replacement of $f$.

**Lean declarations:** `exercise06`, `exercise06_cantor_null`.

<a id="r06e07"></a>
### 6.7 — Proper and conditionally convergent improper integrals
**Lean source:** [Exercise07.lean](../../../Math/Rudin/Chapter06/Exercise07.lean).
**Inventory status:** Verified as stated.

**Statement.** An improper integral at a finite left endpoint $a<b$ means a finite limit

$$
\lim_{c\downarrow a}\int_c^b f(x)\,dx,
$$

with an actual proper Riemann integral on every $[c,b]$, $a<c\le b$. At infinity it means a finite limit of $\int_a^B f$ as $B\to\infty$, with actual proper integrals for every $B\ge a$. These definitions include the singleton truncations and assign no value to divergence.

1. If $f$ is properly Riemann integrable on $[a,b]$, $a<b$, with integral $v$, its improper integral at $a$ exists and equals $v$. In particular this applies to $[0,1]$.
2. On $(0,1]$, the explicit function

   $$
   f(x)=\frac{\cos(1/x-1)}x
   $$

   has a finite improper integral, but $|f|$ does not. Both have proper integrals on every $[c,1]$, $0<c\le1$.

**Proof.** For the first assertion, restriction preserves proper integrability. The ordinary bridge gives an integrable function on the compact interval with the same value $v$. Continuity of its integral with respect to the lower endpoint then gives the required limit. Neither continuity nor prior measurability of $f$ is assumed.

For the construction, define, for $k\ne0$ and $t\ge0$,

$$
K_k(t)=\frac{\cos(kt)}{1+t},\qquad H_k(t)=\frac{\sin(kt)}{(1+t)^2}.
$$

These functions are continuous on each truncation. Integration by parts gives

$$
\int_0^B K_k(t)\,dt
=\frac{\sin(kB)}{k(1+B)}+\frac1k\int_0^B H_k(t)\,dt.
$$

The boundary term tends to zero, and $|H_k(t)|\le(1+t)^{-2}$ proves absolute convergence of the second integral. Thus every $K_k$ has a finite improper integral.

The integral of $|K_1|$ cannot converge finitely. Otherwise the nonnegative-improper-integral bridge would give absolute integrability of $K_1$. Since $\cos^2t\le|\cos t|$, the integral of $\cos^2t/(1+t)$ would also converge. But $2\cos^2t-\cos(2t)=1$ implies

$$
2\int_0^B\frac{\cos^2t}{1+t}\,dt-\int_0^BK_2(t)\,dt=\log(1+B),
$$

contradicting the finite limits on the left.

Finally, the proper substitution $t=1/x-1$ gives

$$
\int_c^1f(x)\,dx=\int_0^{1/c-1}K_1(t)\,dt,\qquad
\int_c^1|f(x)|\,dx=\int_0^{1/c-1}|K_1(t)|\,dt.
$$

It follows that the first limit exists, with value $\int_0^\infty H_1(t)\,dt$. A finite limit for the second would, on setting $c=(1+B)^{-1}$, contradict the preceding nonconvergence. Continuity away from zero supplies all proper witnesses.

**Lean declarations:** `exercise07_a`, `exercise07_b`, `properRiemann_of_continuousOn`, `properRiemann_restrict_right`, `improperRiemannTop_of_integrableOn`, `integrableOn_of_improperRiemannTop_nonneg`, `oscillatoryKernel_proper_identity`, `oscillatoryKernel_improper`, `oscillatoryKernel_one_not_absolute`, `inverse_substitution`, `conditionalEndpointExample_proper`.

<a id="r06e08"></a>
### 6.8 — The integral test
**Lean source:** [Exercise08.lean](../../../Math/Rudin/Chapter06/Exercise08.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $f:[1,\infty)\to\mathbb R$ be nonnegative and nonincreasing. Then

$$
\int_1^\infty f(x)\,dx\text{ converges finitely}
\quad\Longleftrightarrow\quad
\sum_{n=1}^\infty f(n)\text{ converges}.
$$

Series convergence means convergence of the ordered partial sums. Monotonicity alone supplies the proper Riemann integrals on every $[1,B]$, including $B=1$.

**Proof.** On $[n,n+1]$, monotonicity gives

$$
f(n+1)\le\int_n^{n+1}f(x)\,dx\le f(n).
$$

Consequently, for $N\ge1$,

$$
\sum_{n=2}^{N+1}f(n)\le\int_1^{N+1}f(x)\,dx\le\sum_{n=1}^Nf(n).
$$

All these partial sums and integral truncations are nondecreasing. A finite improper limit bounds the left sums, which therefore converge. Conversely, bounded partial sums bound the integral at integer endpoints; monotonicity bounds every real truncation by a larger integer truncation. Thus the truncations have a finite limit. The Lean proof uses the corresponding standard sum–integral comparison theorems through the ordinary bridge. It proves the equivalence between ordered convergence and summability for these nonnegative terms; unconditional summability is not an extra assumption.

**Lean declarations:** `exercise08_integral_test`, `exercise08_proper`, `ordinarySeriesConverges_iff_summable_of_nonneg`.

<a id="r06e09"></a>
### 6.9 — Integration by parts at improper endpoints
**Lean source:** [Exercise09.lean](../../../Math/Rudin/Chapter06/Exercise09.lean).
**Inventory status:** Verified as stated.

**Statement.** The following sufficient rules use real functions and explicit local $C^1$ data.
1. Let $a<b$. Suppose $u,v$ have derivatives $u',v'$ relative to $(a,b]$ at every point there, and $u',v'$ are continuous on $(a,b]$. If $u(x)v(x)\to L$ as $x\downarrow a$ and $\int_a^b u'v=I$ exists improperly, then

   $$
   \int_a^b uv'=u(b)v(b)-L-I.
   $$

2. Suppose instead that these derivative and continuity conditions hold on $[a,\infty)$. If $u(x)v(x)\to L$ at infinity and $\int_a^\infty u'v=I$ exists improperly, then

   $$
   \int_a^\infty uv'=L-u(a)v(a)-I.
   $$

3. Both improper integrals below converge and are equal:

   $$
   \int_0^\infty\frac{\cos x}{1+x}\,dx
      =\int_0^\infty\frac{\sin x}{(1+x)^2}\,dx.
   $$

   The right integral converges absolutely; the left does not.

**Proof.** Relative derivatives permit the appropriate one-sided derivatives at included endpoints. They also give continuity of $u,v$. On every closed truncation the products are continuous, so both proper integrals exist. Proper integration by parts gives

$$
\int_c^Buv'=u(B)v(B)-u(c)v(c)-\int_c^Bu'v.
$$

Taking the indicated limit proves each rule and constructs the other improper integral. No derivative is assumed at the omitted endpoint.

For the example take $u(x)=(1+x)^{-1}$ and $v(x)=\sin x$. Then $u'v=-\sin x/(1+x)^2$, the boundary product is zero at $0$ and tends to zero at infinity. The bound $|\sin x|/(1+x)^2\le(1+x)^{-2}$ gives absolute convergence of the right integral. The second rule gives the equality. The double-angle/logarithm argument in Exercise 6.7 proves failure of absolute convergence on the left. All four integrands, including the two absolute values, are continuous on each $[0,B]$, so their proper integral witnesses exist even at $B=0$.

**Lean declarations:** `exercise09_finite_endpoint_rule`, `exercise09_infinite_endpoint_rule`, `exercise09_example_equality`, `exercise09_sine_absolute`, `exercise09_cosine_not_absolute`, `properRiemann_integration_by_parts`, `exercise09_proper`.

<a id="r06e10"></a>
### 6.10 — Young and Hölder inequalities
**Lean source:** [Exercise10.lean](../../../Math/Rudin/Chapter06/Exercise10.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $p,q>0$ satisfy $1/p+1/q=1$; these conditions imply $p,q>1$.
1. For $u,v\ge0$,

   $$
   uv\le\frac{u^p}{p}+\frac{v^q}{q},
   $$

   with equality exactly when $u^p=v^q$, including $u=v=0$.
2. On $a\le b$, let $\alpha$ be nondecreasing and let real nonnegative $f,g\in\mathcal R(\alpha)$ satisfy $\int f^p\,d\alpha=\int g^q\,d\alpha=1$. Then $fg$ is integrable and $\int fg\,d\alpha\le1$.
3. For complex $f,g\in\mathcal R(\alpha)$ on $a\le b$, the product and both norm powers are integrable, and

   $$
   \left|\int_a^b fg\,d\alpha\right|
      \le\left(\int_a^b|f|^p\,d\alpha\right)^{1/p}
          \left(\int_a^b|g|^q\,d\alpha\right)^{1/q}.
   $$

   Zero power integrals, zero total increment, jumps, and singleton intervals are included.
4. The same Hölder bound holds for ordinary improper integrals on $[a,\infty)$ and on $(a,b]$, $a<b$. Here $f,g$ are complex-valued and properly Riemann integrable on **every** closed truncation, including singleton cuts. Assume the improper integrals of $|f|^p$ and $|g|^q$ have finite values $A,B$. Then the product has proper integrals on every truncation and a finite improper value $z$, with $|z|\le A^{1/p}B^{1/q}$. Product convergence is a conclusion, not a hypothesis.

**Proof.** Young's inequality and its exact equality condition are the standard nonnegative form of Young's theorem. Continuous composition gives the required powers; the product closure law constructs the product integral. Integrating Young's inequality proves the normalized assertion.

To include zero norms without division, apply finite Hölder directly to the actual nonnegative weights $w_i=\alpha(x_{i+1})-\alpha(x_i)$:

$$
\sum_i F_iG_iw_i\le
\left(\sum_iF_i^pw_i\right)^{1/p}
\left(\sum_iG_i^qw_i\right)^{1/q}.
$$

This follows by applying unweighted finite Hölder to $F_iw_i^{1/p}$ and $G_iw_i^{1/q}$. Choose common refinements whose tagged sums approximate the three integrals with errors tending to zero. Continuity of the positive powers, also at zero, gives the real integral inequality. For complex functions the norm of the integral is at most the integral of the norm, and $|fg|=|f||g|$; apply the real inequality to these two norms. Component and composition results supply all integral-existence statements.

For the improper cases, on each truncation Young gives

$$
\int|fg|\le\frac1p\int|f|^p+\frac1q\int|g|^q.
$$

The assumed finite power limits bound these nonnegative truncations. The ordinary real and componentwise complex bridges, followed by the bounded-truncation criterion, prove absolute integrability of the product on the ray or the finite half-open interval. Thus its proper integrals have a finite limit. Passing to the limit in the proper Hölder inequality gives the required bound, again without dividing by $A$ or $B$.

**Scope.** The improper assertions use the identity integrator. They do not assert an improper theorem for an arbitrary raw Stieltjes integrator.

**Lean declarations:** `young`, `young_eq_iff`, `holder_normalized`, `holder_complex`, `holder_improper_left_complex`, `holder_improper_top_complex`, `weighted_holder`, `holder_real_values`, `holder_complex_values`, `exists_rs_rpow`, `exists_complex_norm_rpow`, `complex_ordinary_integral`, `proper_complex_product`, `proper_product_norm_young`.

<a id="r06e11"></a>
### 6.11 — The weighted quadratic seminorm
**Lean source:** [Exercise11.lean](../../../Math/Rudin/Chapter06/Exercise11.lean).
**Inventory status:** Verified as stated.

**Statement.** For $a\le b$, nondecreasing $\alpha$, and complex $u\in\mathcal R(\alpha)$, define

$$
\|u\|_2=\left(\int_a^b|u|^2\,d\alpha\right)^{1/2}.
$$

The integral exists and this quantity is nonnegative. For $f,g,h\in\mathcal R(\alpha)$,

$$
\|f-h\|_2\le\|f-g\|_2+\|g-h\|_2.
$$

The same assertion holds for real functions under their canonical complex embedding. This is a seminorm on actual functions; no separation assertion is made.

**Proof.** Composition gives each squared-norm integral. Put $A=\int|u|^2$, $B=\int|v|^2$, and $C=\int|u||v|$, all with respect to $\alpha$. Schwarz, the $p=q=2$ case of Exercise 6.10, gives $C\le\sqrt A\sqrt B$. The pointwise triangle inequality yields

$$
\int|u+v|^2\le A+2C+B\le(\sqrt A+\sqrt B)^2.
$$

All quantities are nonnegative, so taking square roots proves $\|u+v\|_2\le\|u\|_2+\|v\|_2$. Apply it to $u=f-g$ and $v=g-h$. Real embedding preserves the actual integral and the absolute value, giving the real case. For the zero integrator every increment vanishes, so even the constant function $1$ has seminorm zero.

**Scope.** The implementation selects the unique raw integral value when it exists, with a default value outside that domain. Every use in these inequalities proves existence first; the default is not an integrability claim.

**Lean declarations:** `rsL2Norm_difference_triangle`, `rsL2Norm_real_difference_triangle`, `exists_l2_integral`, `rsL2Norm_eq`, `rsL2Norm_nonneg`, `schwarz_norm_values`, `rsL2Norm_add_le`, `hasComplexRSIntegral_real`, `rsL2Norm_constant_one_zero_integrator`.

<a id="r06e12"></a>
### 6.12 — Continuous approximation in the quadratic seminorm
**Lean source:** [Exercise12.lean](../../../Math/Rudin/Chapter06/Exercise12.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $a\le b$, let $\alpha$ be nondecreasing on $[a,b]$, let $f\in\mathcal R(\alpha)$ be complex-valued, and let $\varepsilon>0$. There is a continuous function $g:\mathbb R\to\mathbb C$, itself integrable against $\alpha$, such that its actual squared-error integral $E$ satisfies

$$
0\le E=\int_a^b|f-g|^2\,d\alpha<\varepsilon^2,
\qquad\|f-g\|_2<\varepsilon.
$$

When $f$ is real, $g$ can be real. No continuity of $\alpha$ or positive total increment is assumed.

**Proof.** First suppose $f$ is real and $|f|\le M$ on the interval, with $M\ge0$. Choose a partition $P$ with

$$
U(P,f,\alpha)-L(P,f,\alpha)<\frac{\delta}{2M+1}.
$$

Interpolate the values $f(x_i)$ linearly on each positive-length cell, and extend constantly outside $[a,b]$. One global formula is

$$
g(t)=f(a)+\sum_i r_i(t)\bigl(f(x_{i+1})-f(x_i)\bigr),\qquad
r_i(t)=\min\!\left(1,\max\!\left(0,\frac{t-x_i}{x_{i+1}-x_i}\right)\right).
$$

For repeated nodes the coefficient difference is zero; omit that term, so no division by zero is needed in this mathematical formula. On a genuine cell, $g$ is the convex combination of its two endpoint values. Hence both $f(t)$ and $g(t)$ lie between the closed-cell extrema $m_i,M_i$. Thus

$$
|f(t)-g(t)|^2\le2M(M_i-m_i).
$$

The continuous-integrand existence theorem and algebraic closure show that $g$ and $(f-g)^2$ have actual raw integrals. Their upper-sum bound gives

$$
0\le E\le U(P,(f-g)^2,\alpha)
\le2M\bigl(U(P,f,\alpha)-L(P,f,\alpha)\bigr)<\delta.
$$

Choose $\delta=\varepsilon^2$ for the real assertion.

For complex $f$, apply this construction separately to its real and imaginary parts with $\delta=\varepsilon^2/2$. Combine the two real polygons into $g$. The identity $|f-g|^2=(\Re(f-g))^2+(\Im(f-g))^2$ gives $E<\varepsilon^2$. Taking the nonnegative square root proves the seminorm estimate. The argument uses the actual closed-cell gaps and therefore also covers jumps of $\alpha$, zero mass, and $a=b$.

**Lean declarations:** `continuous_approximation_complex`, `continuous_approximation_real`, `exists_continuous_real_sq_error`, `exists_continuous_complex_rs`, `partitionPolygon_cell_affine`, `partitionPolygon_error_bound`, `partitionPolygon_upper_error_le`.

<a id="r06e13"></a>
### 6.13 — A quadratic oscillatory phase
**Lean source:** [Exercise13.lean](../../../Math/Rudin/Chapter06/Exercise13.lean).
**Inventory status:** Verified as stated.

**Statement.** Define, for real $x$,

$$
F(x)=\int_x^{x+1}\sin(t^2)\,dt.
$$

Every such integral, and every finite truncation of $\sin(t^2)$, is a proper Riemann integral.
1. For $x>0$, $|F(x)|<1/x$.
2. For $x>0$,

   $$
   2xF(x)=\cos(x^2)-\cos((x+1)^2)+r(x),\qquad |r(x)|<2/x.
   $$

3. $\limsup_{x\to\infty}xF(x)=1$ and $\liminf_{x\to\infty}xF(x)=-1$; actual sequences tending to infinity approach both values.
4. $\int_0^\infty\sin(t^2)\,dt$ converges as a finite limit of proper Riemann integrals.

**Proof.** Continuity gives every proper integral. Integration by parts on $0<a\le b$ gives

$$
\int_a^b\sin(t^2)\,dt
=\frac{\cos(a^2)}{2a}-\frac{\cos(b^2)}{2b}
-\int_a^b\frac{\cos(t^2)}{2t^2}\,dt.
$$

The last integral has absolute value at most $1/(2a)-1/(2b)$. For $a<b$ the inequality is strict: $|\cos(t^2)|$ cannot be identically $1$ on a nondegenerate positive interval. Otherwise $\sin(t^2)$ would vanish there, while its derivative $2t\cos(t^2)$ would not. Continuity makes the strict pointwise inequality strict after integration. Combining the three bounds gives $|F(x)|<1/x$ and the uniform tail bound

$$
\left|\int_a^b\sin(t^2)\,dt\right|\le1/a.
$$

The latter is the Cauchy criterion at infinity, proving part 4 with all proper witnesses.

Multiplying the integration-by-parts formula by $2x$ gives part 2 with

$$
r(x)=\frac{\cos((x+1)^2)}{x+1}
-2x\int_x^{x+1}\frac{\cos(t^2)}{2t^2}\,dt.
$$

Its absolute value is at most $2/(x+1)<2/x$, hence tends to zero.

To attain both limiting bounds, set

$$
y_n=\pi(n+1)+\frac{\pi-1}{2},\quad
m_n(\delta)=\left\lfloor\frac{y_n^2-\delta}{2\pi}\right\rfloor,\quad
x_n(\delta)=\sqrt{2\pi m_n(\delta)+\delta},
$$

for $\delta=0$ or $\pi$. The floor arguments are nonnegative. The floor inequalities give $x_n\le y_n$ and $|x_n-y_n|\le2\pi/y_n\to0$, so $x_n\to\infty$. Moreover,

$$
\cos(x_n^2)=\cos\delta,\qquad
\cos((x_n+1)^2)=\cos\bigl(\delta+\pi+2(x_n-y_n)\bigr).
$$

The asymptotic formula therefore gives $x_nF(x_n)\to1$ for $\delta=0$ and $\to-1$ for $\delta=\pi$. Part 1 bounds all sufficiently large scaled values between $-1$ and $1$, which proves the limsup and liminf assertions.

**Lean declarations:** `quadraticWindow_hasDarboux`, `quadratic_hasDarboux`, `exercise13_a`, `exercise13_b`, `exercise13_c`, `exercise13_c_sequences`, `exercise13_d`, `quadratic_tail_bound`, `quadratic_integration_by_parts`, `quadraticRemainder_tendsto`.

<a id="r06e14"></a>
### 6.14 — An exponential oscillatory phase
**Lean source:** [Exercise14.lean](../../../Math/Rudin/Chapter06/Exercise14.lean).
**Inventory status:** Verified as stated.

**Statement.** For real $x$, let

$$
F(x)=\int_x^{x+1}\sin(e^t)\,dt.
$$

All finite truncations are proper Riemann integrals. For **every real** $x$,

$$
e^x|F(x)|<2,
$$

$$
e^xF(x)=\cos(e^x)-e^{-1}\cos(e^{x+1})+r(x),\qquad |r(x)|<3e^{-x}.
$$

Furthermore,

$$
\limsup_{x\to\infty}e^xF(x)=1+e^{-1},\qquad
\liminf_{x\to\infty}e^xF(x)=-(1+e^{-1}),
$$

with sequences attaining both limits, and $\int_0^\infty\sin(e^t)\,dt$ converges improperly.

**Proof.** Continuity supplies all proper integrals. Integration by parts gives

$$
\int_a^b\sin(e^t)\,dt
=e^{-a}\cos(e^a)-e^{-b}\cos(e^b)
-\int_a^be^{-t}\cos(e^t)\,dt.
$$

For $a\le b$, the correction has absolute value at most $e^{-a}-e^{-b}$, and the bound is strict when $a<b$. Indeed, $|\cos(e^t)|$ cannot be constantly $1$ on an interval, since the phase derivative $e^t$ never vanishes. Thus $|F(x)|<2e^{-x}$ for all real $x$. The non-strict estimate on arbitrary tails is

$$
\left|\int_a^b\sin(e^t)\,dt\right|\le2e^{-a},
$$

which proves improper convergence by the Cauchy criterion.

For the sharper remainder, a second integration by parts gives

$$
\int_a^be^{-t}\cos(e^t)\,dt
=e^{-2b}\sin(e^b)-e^{-2a}\sin(e^a)
+2\int_a^be^{-2t}\sin(e^t)\,dt.
$$

Its absolute value is at most $2e^{-2a}$. Taking

$$
r(x)=-e^x\int_x^{x+1}e^{-t}\cos(e^t)\,dt
$$

proves the displayed identity and $|r(x)|\le2e^{-x}<3e^{-x}$.

The identity bounds all limiting values by $\pm(1+e^{-1})$. To attain the bounds, use irrationality of $e$ and density of irrational rotations modulo $2\pi$. For any $\delta\ge0$ and target $\beta$, choose increasing integers $n_j$ such that

$$
e\bigl(\delta+2\pi(n_j+1)\bigr)\pmod{2\pi}\longrightarrow\beta\pmod{2\pi}.
$$

With $x_j=\log(\delta+2\pi(n_j+1))$, one has $x_j\to\infty$, $\cos(e^{x_j})=\cos\delta$, and $\cos(e^{x_j+1})\to\cos\beta$. The remainder tends to zero. The choices $(\delta,\beta)=(0,\pi)$ and $(\pi,0)$ yield the two claimed extremal limits.

**Scope.** Repeating Exercise 6.13 includes the limit and convergence questions. The sharp scaled limits here are $\pm(1+e^{-1})$, not $\pm2$; the strict bound $2$ alone does not determine them.

**Lean declarations:** `exponentialWindow_hasDarboux`, `exponential_hasDarboux`, `exercise14_decay_bound`, `exercise14_asymptotic`, `exercise14_limits`, `exercise14_limit_sequences`, `exercise14_improper_convergence`, `exponential_tail_bound`, `exponential_second_integration_by_parts`, `exponentialRemainder_tendsto`, `exponential_phase_irrational`, `exponential_phase_sequence`.

<a id="r06e15"></a>
### 6.15 — A strict Schwarz-type bound
**Lean source:** [Exercise15.lean](../../../Math/Rudin/Chapter06/Exercise15.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $a\le b$ and let real $f$ have derivative $f'$ relative to $[a,b]$ at every point, including one-sided endpoint derivatives. Assume $f'$ is continuous on $[a,b]$, $f(a)=f(b)=0$, and the actual Riemann integral satisfies $\int_a^bf^2\,dx=1$. Then all the following integrals exist properly, and

$$
\int_a^bxf(x)f'(x)\,dx=-\tfrac12,
$$

$$
\left(\int_a^b(f')^2\,dx\right)
\left(\int_a^bx^2f^2\,dx\right)>\tfrac14.
$$

The normalization rules out $a=b$.

**Proof.** The derivative hypotheses give continuity of $f$, and all displayed integrands are continuous. Integrate

$$
(xf^2)'=f^2+2xff'.
$$

The endpoint terms vanish and $\int f^2=1$, proving the first identity.

For each real $c$, the integral $\int_a^b(f'+cxf)^2\,dx$ is strictly positive. If the continuous nonnegative integrand had zero integral, it would vanish everywhere, so $f'=-cxf$. On this compact interval,

$$
|f'|\le |c|(|a|+|b|)|f|.
$$

The zero-solution theorem for this differential inequality, with $f(a)=0$, forces $f=0$, contradicting the normalization.

Put $A=\int_a^b(f')^2\,dx\ge0$ and $B=\int_a^bx^2f^2\,dx$. Apply the strict positivity just proved with $c=2A$. Expanding the square and using the first identity gives

$$
0<A+4A(-\tfrac12)+4A^2B=A(4AB-1).
$$

Since $A\ge0$, this forces $AB>1/4$. This explicitly excludes equality rather than assuming a strict version of Schwarz.

**Lean declarations:** `exercise15_integration_identity`, `exercise15_strict_product_bound`, `exercise15`.

<a id="r06e16"></a>
### 6.16 — Floor-function integral formulas for zeta
**Lean source:** [Exercise16.lean](../../../Math/Rudin/Chapter06/Exercise16.lean).
**Inventory status:** Verified as stated.

**Statement.** For $s>1$, the ordered series $\zeta(s)=\sum_{n=1}^\infty n^{-s}$ converges, and

$$
\zeta(s)=s\int_1^\infty\frac{\lfloor x\rfloor}{x^{s+1}}\,dx,
$$

$$
\zeta(s)=\frac{s}{s-1}-s\int_1^\infty\frac{x-\lfloor x\rfloor}{x^{s+1}}\,dx.
$$

Both formulas use actual improper Riemann integrals. The remainder integral converges for every real $s>0$. For every real $s$ and every $B\ge1$, both integrands have proper Riemann integrals on $[1,B]$. The exact finite identity, valid for every real $s$ and integer $N\ge1$, is

$$
\sum_{n=1}^N n^{-s}=N^{1-s}+s\int_1^N\frac{\lfloor x\rfloor}{x^{s+1}}\,dx.
$$

**Proof.** On each compact interval starting at $1$, the floor function is monotone and hence properly Riemann integrable. The factor $x^{-s-1}$ is continuous there. Product and subtraction laws give proper integrability of both displayed integrands for all real $s$, also at $B=1$.

Abel summation applied to $x^{-s}$, whose derivative is $-sx^{-s-1}$ for $x>0$, gives the finite identity. For $s>1$, the $p$-series theorem gives ordered convergence, while

$$
0\le\frac{\lfloor x\rfloor}{x^{s+1}}\le x^{-s}\qquad(x\ge1)
$$

proves convergence of the floor integral over all real cutoffs. Letting $N\to\infty$ in the finite identity, with $N^{1-s}\to0$, proves the first formula.

For $s>0$,

$$
0\le\frac{x-\lfloor x\rfloor}{x^{s+1}}\le x^{-s-1},
$$

and the comparison integral is finite. Together with the proper witnesses this proves convergence of the remainder. If $s>1$, the two integrands add to $x^{-s}$, whose integral from $1$ to infinity is $1/(s-1)$. Adding their truncations and taking limits gives the second formula.

**Scope.** Only the remainder convergence is extended to $0<s\le1$. No convergence of the defining zeta series, or zeta formula on that range, is asserted.

**Lean declarations:** `exercise16_a`, `exercise16_ordered_series`, `exercise16_proper_integrals`, `exercise16_finite_identity`, `exercise16_b`, `exercise16_remainder_convergence`.

<a id="r06e17"></a>
### 6.17 — Integration by parts with a discontinuous monotone factor
**Lean source:** [Exercise17.lean](../../../Math/Rudin/Chapter06/Exercise17.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $a\le b$, let real $\alpha$ be nondecreasing on $[a,b]$, let $g$ be continuous there, and suppose $G'=g$ relative to $[a,b]$ at every point, with one-sided endpoint derivatives. Then both literal integrals exist and

$$
\int_a^b\alpha(x)g(x)\,dx
=\alpha(b)G(b)-\alpha(a)G(a)-\int_a^bG\,d\alpha.
$$

The assertion holds for real $g,G$ and also for complex $g,G$ with a real parameter derivative. In the complex case multiplication by $\alpha$ is real scalar multiplication. No continuity of $\alpha$ is assumed, even at endpoints.

**Proof.** Monotonicity makes $\alpha$ ordinarily Riemann integrable, and continuity makes $g$ so; their product is integrable. The derivative condition makes $G$ continuous, hence $G\in\mathcal R(\alpha)$. This constructs both integrals before proving their relation.

For a partition, finite summation by parts gives the exact identity

$$
\sum_iG(x_{i+1})\bigl(\alpha(x_{i+1})-\alpha(x_i)\bigr)
+\sum_i\alpha(x_i)\bigl(G(x_{i+1})-G(x_i)\bigr)
=\alpha(b)G(b)-\alpha(a)G(a).
$$

Uniform differentiability, which follows from the continuous derivative on the compact interval, gives

$$
|G(y)-G(x)-g(x)(y-x)|\le\eta|y-x|
$$

for sufficiently close points of $[a,b]$. If $|\alpha|\le C$, replacing the second sum by its left-tag ordinary sum changes it by at most $C\eta(b-a)$. Zero-length cells give zero error. Take a common refinement that both controls the two integrals and has sufficiently short cells. The first sum tends to $\int G\,d\alpha$, the replaced sum tends to $\int\alpha g\,dx$, and the error tends to zero. The displayed formula follows with the original endpoint values of $\alpha$. Apply this real proof to real and imaginary components for the complex assertion. At $a=b$ all terms cancel directly.

**Lean declarations:** `exercise17_stieltjes_parts`, `exercise17_stieltjes_parts_complex`.

<a id="r06e18"></a>
### 6.18 — The same circle with different lengths
**Lean source:** [Exercise18.lean](../../../Math/Rudin/Chapter06/Exercise18.lean).
**Inventory status:** Verified refutation and correction.

**Statement.** On $[0,2\pi]$, define complex curves

$$
\gamma_1(t)=e^{it},\qquad\gamma_2(t)=e^{2it},\qquad
\gamma_3(t)=\begin{cases}1,&t=0,\\
\exp\bigl(2\pi i\,t\sin(1/t)\bigr),&t>0.
\end{cases}
$$

All three are continuous and have the unit circle as their range. The first two are rectifiable, with lengths $2\pi$ and $4\pi$. The third has infinite length and infinite variation, and is not rectifiable. Length is the supremum of ordered partition chord sums in the usual complex norm, as in Exercise 6.19.

**Correction.** The printed third formula contains $1/t$ but its interval includes zero. There is no real reciprocal of zero: no real $u$ satisfies $0u=1$. The value $\gamma_3(0)=1$ is an explicit endpoint repair and is the **unique** continuous extension of the printed positive-parameter formula. The phase remains $t\sin(1/t)$, not $\sin(1/t)$ alone. The inventory records a verified refutation and explicit correction, not a proof of the unextended printed formula.

**Proof.** The bound $|t\sin(1/t)|\le|t|$ makes the phase tend to zero as $t\to0$. Thus the positive-parameter formula tends to $1$, proving continuity of the repair and uniqueness of its endpoint value. Away from zero continuity follows by composition. The first two curves are continuous directly.

Every value has modulus one. The first curve covers the circle over a full angular period; the second covers it as well by taking half of each first-curve parameter. For the third curve put $h(t)=t\sin(1/t)$ and $l=2/(3\pi)$. Then $h(l)=-2/(3\pi)$, while the inequality $\sin u\ge u-u^3/6$ gives

$$
h(2\pi)\ge1-\frac1{24\pi^2}.
$$

Since $1/(24\pi^2)\le2/(3\pi)$, the phase values differ by at least $1$. Continuity and the intermediate value theorem show that $2\pi h([l,2\pi])$ contains an angular interval of width $2\pi$. Such an interval covers the whole unit circle under $\theta\mapsto e^{i\theta}$.

For angular points,

$$
|e^{is}-e^{it}|=2\left|\sin\frac{s-t}{2}\right|\le|s-t|.
$$

Thus the length of $t\mapsto e^{i\omega t}$ on $[0,L]$, for $\omega,L\ge0$, is at most $\omega L$. A uniform partition with $N$ cells has chord sum

$$
2N\left|\sin\frac{\omega L}{2N}\right|\longrightarrow\omega L.
$$

This gives the reverse inequality, also when $\omega L=0$. Taking $(\omega,L)=(1,2\pi)$ and $(2,2\pi)$ proves the two finite lengths.

For the third curve choose decreasing times

$$
\tau_n=\frac1{\pi/2+(n+2)\pi},\qquad
\theta_n=2\pi\tau_n=\frac2{n+5/2}.
$$

They lie in $[0,2\pi]$, and

$$
\Im\gamma_3(\tau_n)=(-1)^n\sin\theta_n,\qquad0\le\theta_n\le\pi/2.
$$

Successive imaginary parts have opposite signs. The chord between them is at least $\sin\theta_n$. Using $\sin\theta\ge2\theta/\pi$ on $[0,\pi/2]$ gives the sufficient bound

$$
\frac1{n+3}\le\pi\,|\gamma_3(\tau_{n+1})-\gamma_3(\tau_n)|.
$$

For each finite list, reverse the decreasing times and insert the two interval endpoints. Its chord sum is bounded by the source length. If that length were finite, all partial sums of these nonnegative chords would be bounded, and the displayed bound would make a shifted harmonic series converge. This is impossible. Hence the length is infinite. The proved equality between source length and variation gives infinite variation as well.

**Lean declarations:** `exercise18_common_range`, `exercise18_gamma1_continuous`, `exercise18_first_length`, `exercise18_gamma2_continuous`, `exercise18_second_length`, `exercise18_endpoint_extension`, `exercise18_endpoint_unique`, `exercise18_printed_endpoint_obstruction`, `exercise18_third_nonrectifiable`, `exercise18_third_infinite_variation`, `exercise18_gamma3_positive`, `exercise18_phase_width`, `linearCircle_length`, `exercise18_sample_im`, `exercise18_harmonic_chord`.

<a id="r06e19"></a>
### 6.19 — Invariance under continuous reparameterization
**Lean source:** [Exercise19.lean](../../../Math/Rudin/Chapter06/Exercise19.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $c\le d$, let $\gamma:[a,b]\to\mathbb R^k$ be continuous, and let $\varphi:[c,d]\to[a,b]$ be a continuous bijection with $\varphi(c)=a$. Put $\widetilde\gamma=\gamma\circ\varphi$. Then $\widetilde\gamma$ is continuous, and
1. $\widetilde\gamma$ is an arc if and only if $\gamma$ is an arc, where an arc is a continuous injective map of the parameter interval.
2. $\widetilde\gamma$ is a closed curve if and only if $\gamma$ is a closed curve, where closed means equality of the endpoint values.
3. The curves have equal lengths in $[0,\infty]$, so one is rectifiable if and only if the other is.

The Euclidean norm is the usual $\ell^2$ norm. The file also proves these assertions for a pseudometric target; the length and rectifiability assertions do not require continuity of $\gamma$. Under the full hypotheses, singleton intervals are included. Separately, the length convention gives zero for empty or singleton intervals.

**Proof.** Define the source length by

$$
L(\gamma;[a,b])=\sup_{a=x_0\le\cdots\le x_n=b}
\sum_{i=0}^{n-1}d\bigl(\gamma(x_{i+1}),\gamma(x_i)\bigr),
$$

with the supremum in the extended nonnegative reals. Every partition list is admissible in the definition of variation, so source length is at most variation. Conversely, add $a,b$ to any finite ordered list in $[a,b]$. The extra chords are nonnegative, so its sum is at most a full partition sum. Thus the two suprema agree. Removing repeated nodes does not change a sum, so strictly increasing finite lists give the same supremum. Empty intervals have no partitions and hence supremum zero; singleton chords are all zero. In a normed space the distance is exactly the norm of the chord difference.

A continuous injective real function on an interval is strictly monotone. The condition $\varphi(c)=a$ and the fact that its range is $[a,b]$ force increasing orientation; the singleton case is immediate. Surjectivity and monotonicity then give $\varphi(d)=b$. Mapping an ordered partition through $\varphi$ preserves its order and its chord sum. Conversely, each ordered partition of $[a,b]$ has ordered preimages by bijectivity and increasing order. Therefore the two length suprema are equal, without assuming finiteness. This also proves the equivalence of rectifiability.

Composition gives continuity of $\widetilde\gamma$. Injectivity is preserved in one direction by composition of injections; in the other, lift two parameters of $\gamma$ through the surjection $\varphi$ and use injectivity of the composite. Finally, $\widetilde\gamma(c)=\gamma(a)$ and $\widetilde\gamma(d)=\gamma(b)$ give the closed-curve equivalence.

**Lean declarations:** `exercise19_arc`, `exercise19_closed_curve`, `exercise19_rectifiability`, `exercise19_length`, `exercise19_euclidean`, `curveLength_eq_eVariationOn`, `curveLength_eq_zero_of_ge`, `curveLength_eq_strictLists`, `curveChordSum_eq_norm`, `reparam_strictMono`, `reparam_last`, `reparam_continuous`.
