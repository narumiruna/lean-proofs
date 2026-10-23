<a id="chapter-10"></a>

# Chapter 10 — Integration of Differential Forms

[All chapters](../solutions.md) · [Previous chapter](chapter-09.md) · [Next chapter](chapter-11.md)

**Exercises:** [1](#r10e01) · [2](#r10e02) · [3](#r10e03) · [4](#r10e04) · [5](#r10e05) · [6](#r10e06) · [7](#r10e07) · [8](#r10e08) · [9](#r10e09) · [10](#r10e10) · [11](#r10e11) · [12](#r10e12) · [13](#r10e13) · [14](#r10e14) · [15](#r10e15) · [16](#r10e16) · [17](#r10e17) · [18](#r10e18) · [19](#r10e19) · [20](#r10e20) · [21](#r10e21) · [23](#r10e23) · [28](#r10e28) · [29](#r10e29) · [30](#r10e30) · [32](#r10e32)

<a id="r10e01"></a>
### 10.1 — Integration order for a convex zero extension

**Lean source:** [Exercise01.lean](../../../Math/Rudin/Chapter10/Exercise01.lean).

**Inventory status:** Pending verification.

**Statement.** Let $H\subset\mathbb R^n$ be compact and convex, and let $f:H\to\mathbb R$ or $\mathbb C$ be continuous. Retain the values of $f$ on the boundary and extend it by zero outside $H$. There is an enclosing coordinate cell on which every repeated integral exists, at every remaining parameter, in every coordinate order. Each order has value $\int_H f$. Order independence also holds on any coordinate cell with ordered bounds, whether or not it contains $H$.

The results do not require nonempty interior. They include empty sets, lower-dimensional sets, dimension zero, and cells with degenerate sides. In dimension zero, integration is evaluation.

**Proof.** The zero extension is bounded and measurable. For every finite-dimensional affine parameter map $L$, the inverse image $L^{-1}(H)$ is closed and convex. Its frontier has measure zero in the parameter space. Away from that frontier, the composite zero extension is continuous: inside, use the continuity of $f$ on $H$; outside, the composite is locally zero. This argument applies to every affine section, including boundary sections and collapsed sections.

This regularity is preserved by integration in one coordinate. Indeed, apply Fubini to the almost-everywhere continuity statement in the joint parameter and integration variables. For almost every parameter, the integrand is continuous in the parameter at almost every integration point. Its uniform bound then permits dominated convergence. The resulting marginal is bounded, measurable, and almost everywhere continuous on every affine parameter space. Each individual coordinate row is bounded and almost everywhere continuous, so the one-dimensional Darboux criterion supplies its actual Riemann integral. Induction gives all repeated source integrals, not just almost-everywhere row integrals. Fubini, now with integrability established, identifies their values with the cell measure integral.

For the approximation argument, extend $f$ continuously to an ambient function $g$. Choose continuous cutoffs $c_j$ with $0\le c_j\le1$, zero outside $H$ and on its frontier, tending to $1$ in its interior. The source uses distance-based thickened indicators with width $1/(j+1)$. The functions $c_jg$ are continuous, have topological support in $H$, and have a common bound. They converge to the literal zero extension outside the null convex frontier. No uniform convergence at nonzero boundary values is asserted. Dominated convergence transfers this approximation to each repeated value. The continuous-cell theorem gives the same value for all orders at each $j$; uniqueness of limits gives order independence for the zero extension.

For complex values, apply the real argument to the real and imaginary parts. The component equivalence for complex tagged sums supplies actual complex one-dimensional source integrals at each stage. Compactness supplies strictly ordered enclosing bounds, and the volume-preserving Euclidean coordinate map identifies the common enclosing-cell value with $\int_H f$. The plane-coordinate conclusions give the same witnesses in $\mathbb R\times\mathbb R$.

Inventory obligations `R10E01.existence` and `R10E01.order_independence` remain marked in progress; the current source contains the results above.

**Lean declarations:** `Rudin.Chapter10.Exercise01.existence_real`, `Rudin.Chapter10.Exercise01.existence_complex`, `Rudin.Chapter10.Exercise01.plane_source_real`, `Rudin.Chapter10.Exercise01.plane_source_complex`, `Rudin.Chapter10.Exercise01.order_independence_real`, `Rudin.Chapter10.Exercise01.order_independence_complex`, `Rudin.Chapter10.Exercise01.real_existence`, `Rudin.Chapter10.Exercise01.complex_existence`, `Rudin.Chapter10.Exercise01.continuous_approximations`, `Rudin.Chapter10.Exercise01.continuous_approximations_complex`, `Rudin.Chapter10.Exercise01.approximation_source_limit`, `Rudin.Chapter10.Exercise01.real_order_independence`, `Rudin.Chapter10.Exercise01.complex_order_independence`.

<a id="r10e02"></a>
### 10.2 — Unequal repeated integrals near a singular point

**Lean source:** [Exercise02.lean](../../../Math/Rudin/Chapter10/Exercise02.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $\phi_i:\mathbb R\to\mathbb C$ be continuous, supported in $(2^{-i},2^{1-i})$, with $\int_{\mathbb R}\phi_i=1$, for $i\ge1$. Real functions are included; positivity is not assumed. Set

$$
f(x,y)=\sum_{i\ge1}\bigl(\phi_i(x)-\phi_{i+1}(x)\bigr)\phi_i(y).
$$

The series is pointwise finite, its ordered partial sums converge to $f$, and it is locally finite away from $(0,0)$. The function has compact support in $[0,1]^2$ and is continuous away from the origin. Every coordinate section is continuous and compactly supported, and both integrations in each order exist, including their source Riemann integrals. Their values are

$$
\int_{\mathbb R}\left(\int_{\mathbb R}f(x,y)\,dx\right)dy=0,
\qquad
\int_{\mathbb R}\left(\int_{\mathbb R}f(x,y)\,dy\right)dx=1.
$$

Moreover, $f(0,0)=0$, but $f$ is unbounded in every neighborhood of the origin, is discontinuous there, and is not integrable on the plane. The geometric conclusions also hold in Euclidean plane coordinates.

**Proof.** Write $r_n=2^{-n}$, with source index $i=n+1$. At any fixed nonzero coordinate, sufficiently small dyadic intervals miss that coordinate and a whole neighborhood of it. At coordinate zero, every $\phi_i$ vanishes. Thus every point kills a tail of the series. Away from the origin, at least one coordinate kills the tail on a neighborhood. The remaining terms form a finite sum of continuous functions. All terms vanish outside $[0,1]^2$, so the closure of the nonzero set is compact.

For fixed $y$, only finitely many terms remain as functions of $x$. Integrating each gives $(1-1)\phi_i(y)=0$. For fixed $x$, choose a finite cutoff with vanishing tail. Integration in $y$ gives the telescoping sum

$$
\sum_{i=1}^{N}\bigl(\phi_i(x)-\phi_{i+1}(x)\bigr)=\phi_1(x).
$$

The outer integrals are therefore the integrals of zero and $\phi_1$, respectively. Each section is continuous and supported in $[0,1]$. The continuous-function bridge supplies Darboux integrals for its real and imaginary parts and complex tagged-sum convergence. The real case also has explicit witnesses in the recursive two-coordinate source predicate for both orders.

Distinct dyadic support intervals do not overlap. If $\phi_i(x)\ne0$, then all other $\phi_j(x)$ vanish, and

$$
f(x,x)=\phi_i(x)^2,\qquad |f(x,x)|=|\phi_i(x)|^2.
$$

Integral one on an interval contained in $[0,2^{1-i}]$ rules out a uniform bound $M$ whenever $M2^{1-i}<1$: otherwise the norm of that integral would be less than one. Choose $i$ so large that this interval is inside a prescribed diagonal neighborhood and the resulting squared value exceeds any prescribed bound. This proves local unboundedness without positivity, even for complex functions. It also proves discontinuity at the origin. Finally, plane integrability would permit Fubini and force the two repeated values to agree, contradicting $0\ne1$. Complexification preserves the actual real series and transfers all the real conclusions.

**Lean declarations:** `Rudin.Chapter10.Exercise02.Family.well_defined`, `Rudin.Chapter10.Exercise02.Family.ordered_convergence`, `Rudin.Chapter10.Exercise02.Family.locally_finite_off_origin`, `Rudin.Chapter10.Exercise02.Family.compact_support`, `Rudin.Chapter10.Exercise02.Family.continuous_off_origin`, `Rudin.Chapter10.Exercise02.Family.x_then_y`, `Rudin.Chapter10.Exercise02.Family.y_then_x`, `Rudin.Chapter10.Exercise02.Family.unbounded_every_neighborhood`, `Rudin.Chapter10.Exercise02.Family.discontinuous_origin`, `Rudin.Chapter10.Exercise02.Family.not_integrable`, `Rudin.Chapter10.Exercise02.Family.euclidean_conclusions`, `Rudin.Chapter10.Exercise02.RealFamily.complex_f`, `Rudin.Chapter10.Exercise02.RealFamily.real_case`, `Rudin.Chapter10.Exercise02.RealFamily.source_orders`.

<a id="r10e03"></a>
### 10.3 — Local factorization into primitive maps

**Lean source:** [Exercise03.lean](../../../Math/Rudin/Chapter10/Exercise03.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $E\subset\mathbb R^n$ be open and contain zero. Suppose $F$ is $C^1$ on $E$, $F(0)=0$, and $A=F'(0)$ is invertible. Then $F_1=A^{-1}F$ has derivative $I$ at zero. On a neighborhood of zero it is a composition of exactly $n$ primitive $C^1$ maps:

$$
F_1=G_n\circ\cdots\circ G_1,\qquad
F=A\circ G_n\circ\cdots\circ G_1.
$$

Each factor fixes zero, has derivative $I$ there, and has an open primitive domain containing zero. A primitive map changes at most one coordinate. For $n=0$, the factor family is empty and the composition is the identity.

The planar flip $(x,y)\mapsto(y,x)$ cannot be a composition $H\circ G$ of two primitive maps on any neighborhood $U$ of zero, provided $G(U)$ lies in the primitive domain of $H$. This obstruction requires no regularity of $G$ or $H$.

**Proof.** The chain rule gives $(A^{-1}F)'(0)=A^{-1}A=I$. For the normalized map, let $P_m$ replace the first $m$ input coordinates by their values under $F_1$, leaving the others unchanged. Every $P_m$ fixes zero and has derivative $I$ there. The inverse function theorem supplies a $C^1$ local inverse $H_m$ with derivative $I$ at zero and both inverse identities on neighborhoods.

Define the next factor by replacing only coordinate $m+1$ of $z$ by the corresponding coordinate of $F_1(H_m(z))$. All other coordinates remain unchanged. Near zero, this factor sends $P_m(x)$ to $P_{m+1}(x)$. The chain rule gives derivative $I$ for the factor. Its $C^1$ germ can be restricted to an open neighborhood. Induction identifies the first $m$ factors with $P_m$ near zero. Since $P_0=I$ and $P_n=F_1$, exactly $n$ factors suffice. Multiplying by $A$ recovers $F$.

For the flip, consider which coordinate each primitive factor can change. If both change the same coordinate, the other coordinate remains fixed, contrary to a flip at a small point on the other axis. If $G$ changes the first coordinate and $H$ the second, the first output coordinate forces $G(x,y)=(y,y)$ on $U$. Thus $G(a,0)=G(0,0)$ for a sufficiently small nonzero $a$, while their flipped images are distinct. The composition cannot have both values. The case where $G$ changes the second coordinate and $H$ the first is the same argument using $(0,a)$.

**Lean declarations:** `Rudin.Chapter10.exercise03_normalization`, `Rudin.Chapter10.exercise03_partial_inverse`, `Rudin.Chapter10.exercise03_factorization`, `Rudin.Chapter10.exercise03_a`, `Rudin.Chapter10.exercise03_a_finite`, `Rudin.Chapter10.exercise03_b`.

<a id="r10e04"></a>
### 10.4 — Two explicit primitive factorizations

**Lean source:** [Exercise04.lean](../../../Math/Rudin/Chapter10/Exercise04.lean).

**Inventory status:** Verified as stated.

**Statement.** Define

$$
\begin{aligned}
F(x,y)&=(e^x\cos y-1,e^x\sin y),\\
G_1(x,y)&=(e^x\cos y-1,y),&G_2(u,v)&=(u,(1+u)\tan v),\\
H_2(x,y)&=(x,e^x\sin y),&H_1(u,v)&=(\sqrt{e^{2u}-v^2}-1,v).
\end{aligned}
$$

On $U=\{(x,y):-\pi/2<y<\pi/2\}$, one has $F=G_2\circ G_1=H_1\circ H_2$. Here $G_1(U)\subset U$ and $H_2(U)\subset V=\{(u,v):e^{2u}-v^2>0\}$. Both $U$ and $V$ are open neighborhoods of zero. The four factors are primitive on these domains. The maps $F,G_1,H_2$ are globally smooth; $G_2$ is smooth on $U$, and $H_1$ is smooth on $V$. The derivatives of $F,G_1,G_2$ at zero are $I$, so all three Jacobians there are $1$.

**Proof.** On $U$, $\cos y>0$. The first factor leaves $y$ unchanged, and

$$
(1+(e^x\cos y-1))\tan y=e^x\sin y.
$$

This proves the first factorization and its domain condition. For the second, use

$$
e^{2x}-(e^x\sin y)^2=(e^x\cos y)^2.
$$

The right side is positive on $U$. Thus $H_2$ lands in $V$, and its positive square root is $e^x\cos y$, not its negative. This gives the stated formula for $H_1\circ H_2$. Each primitive assertion follows from the unchanged coordinate. Standard composition rules give smoothness, using the nonzero cosine and positive square-root arguments on the specified domains. Differentiating the displayed coordinates at zero gives the two coordinate projections as rows for each of $F,G_1,G_2$. Their derivative matrices are therefore $I$, with determinant $1$.

**Lean declarations:** `Rudin.Chapter10.exercise04_domains`, `Rudin.Chapter10.exercise04_primitive_maps`, `Rudin.Chapter10.exercise04_smooth`, `Rudin.Chapter10.exercise04_first_factorization`, `Rudin.Chapter10.exercise04_alternative_factor`, `Rudin.Chapter10.exercise04_derivatives`, `Rudin.Chapter10.exercise04_jacobians`.

<a id="r10e05"></a>
### 10.5 — A finite partition of unity in a metric space

**Lean source:** [Exercise05.lean](../../../Math/Rudin/Chapter10/Exercise05.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $K$ be a compact subset of an arbitrary metric space $X$, and let $(U_i)_{i\in I}$ be an open cover of $K$. There are a finite index set $J$, a choice $a:J\to I$, and continuous functions $\psi_j:X\to[0,1]$ such that

$$
\operatorname{supp}\psi_j\subset U_{a(j)},\qquad
\sum_{j\in J}\psi_j(x)=1\quad(x\in K).
$$

Support means the closure of the nonzero set. Neither local compactness of $X$ nor compact support of the functions is required. Empty $K$ is allowed.

**Proof.** For disjoint nonempty closed sets $A,B$, the metric separator

$$
s(x)=\frac{d(x,A)}{d(x,A)+d(x,B)}
$$

is continuous, lies in $[0,1]$, is zero on $A$, and is one on $B$. Its denominator is positive at each point because the sets are closed and disjoint. If $A$ is empty use the constant one; if only $B$ is empty use zero.

Given $x\in U_i$, normality of metric spaces supplies open neighborhoods $V,W$ with $x\in V$, $\overline V\subset W$, and $\overline W\subset U_i$. Separate $W^c$ and $\overline V$. The resulting bump is one on $V$, zero outside $W$, and has support in $\overline W\subset U_i$. Compactness selects finitely many such $V$ covering $K$, with bumps $b_1,\ldots,b_N$. Use the ordered-product construction

$$
\psi_j=b_j\prod_{\ell<j}(1-b_\ell).
$$

Every function is continuous, lies in $[0,1]$, and has support contained in that of its own bump. The identity $\sum_j\psi_j=1-\prod_j(1-b_j)$ gives sum one on $K$, since some bump is one at each point of $K$. The empty compact set permits an empty family. The finite-bump extraction is also proved separately and reused for smooth bumps.

**Lean declarations:** `Rudin.Chapter10.exercise05_separator_spec`, `Rudin.Chapter10.exercise05_bump`, `Rudin.Chapter10.exercise05_finite_bumps`, `Rudin.Chapter10.exercise05_metric_partition`.

<a id="r10e06"></a>
### 10.6 — A smooth finite partition of unity

**Lean source:** [Exercise06.lean](../../../Math/Rudin/Chapter10/Exercise06.lean).

**Inventory status:** Pending verification.

**Statement.** For compact $K\subset\mathbb R^n$ and any open cover $(U_i)$ of $K$, the finite subordinate partition in Exercise 10.5 can be chosen globally $C^\infty$. Each function also has compact support, is differentiable, takes values in $[0,1]$, and the functions sum to one on $K$. Empty $K$ and dimension zero are included.

**Proof.** Let $g(s)$ be the flat function from Chapter 8, equal to $e^{-1/s^2}$ for $s\ne0$ and zero at zero. Then $b(t)=g(\sqrt t)$ is $e^{-1/t}$ for $t>0$ and zero for $t\le0$. The source identifies this function exactly with the smooth positive-side flat function. Consequently

$$
\eta(t)=\frac{b(t)}{b(t)+b(1-t)}
$$

is the standard smooth transition: it lies in $[0,1]$, is zero for $t\le0$, and one for $t\ge1$.

Given $x\in U_i$, choose $r>0$ with $B(x,r)\subset U_i$ and set

$$
h(y)=\eta\left(\frac{(r/2)^2-\|y-x\|^2}{(r/2)^2-(r/4)^2}\right).
$$

The denominator is positive. The squared norm is smooth, so $h$ is globally smooth. It equals one on $B(x,r/4)$ and vanishes when $\|y-x\|\ge r/2$. Its support is a closed subset of the compact ball $\overline B(x,r/2)$, which is contained in $U_i$. Finite extraction gives bumps covering $K$. Apply the same ordered-product formula as in Exercise 10.5. Finite products preserve smoothness; support containment preserves compact support and subordination. The telescoping product proves the sum condition. Smoothness implies differentiability.

The source contains this construction, but `R10E06.smooth_partition` remains marked in progress in the inventory.

**Lean declarations:** `Rudin.Chapter10.exercise06_source_glue`, `Rudin.Chapter10.exercise06_transition_eq`, `Rudin.Chapter10.exercise06_auxiliary_smooth`, `Rudin.Chapter10.exercise06_bump`, `Rudin.Chapter10.exercise06_product_smooth`, `Rudin.Chapter10.exercise06_smooth_partition`.

<a id="r10e07"></a>
### 10.7 — The standard simplex as a convex hull

**Lean source:** [Exercise07.lean](../../../Math/Rudin/Chapter10/Exercise07.lean).

**Inventory status:** Verified as stated.

**Statement.** The closed standard simplex

$$
Q^n=\{x\in\mathbb R^n:x_i\ge0,\ \sum_i x_i\le1\}
$$

is the smallest convex set containing $0,e_1,\ldots,e_n$. Equivalently, it is their convex hull. The image of any convex set under any real affine map is convex, without openness or nonemptiness assumptions. The simplex assertion includes $n=0$.

**Proof.** Nonnegative convex combinations preserve each coordinate inequality and the inequality on the coordinate sum, so $Q^n$ is convex. It contains all the listed vertices. Conversely, for $x\in Q^n$,

$$
x=\left(1-\sum_i x_i\right)0+\sum_i x_i e_i.
$$

These weights are nonnegative and sum to one. Every convex set containing the vertices therefore contains $x$. When $n=0$, the only vertex and the only point of the simplex are zero. Finally, if $T$ is affine, then $T(ax+by)=aT(x)+bT(y)$ for $a,b\ge0$ with $a+b=1$. This proves convexity of the affine image.

**Lean declarations:** `Rudin.Chapter10.exercise07_convex`, `Rudin.Chapter10.exercise07_minimal`, `Rudin.Chapter10.exercise07_a`, `Rudin.Chapter10.exercise07_b`.

<a id="r10e08"></a>
### 10.8 — An exponential integral over a parallelogram

**Lean source:** [Exercise08.lean](../../../Math/Rudin/Chapter10/Exercise08.lean).

**Inventory status:** Pending verification.

**Statement.** Let $H$ have vertices $(1,1),(3,2),(4,5),(2,4)$. The affine map

$$
T(u,v)=(1+2u+v,1+u+3v)
$$

sends the unit square onto $H$, takes $0,e_1,e_2$ to the prescribed vertices, and has Jacobian $5$. Moreover,

$$
\int_H e^{x-y}\,dx\,dy
=\int_{[0,1]^2}5e^{u-2v}\,du\,dv
=\frac52(e-1)(1-e^{-2}).
$$

The original integrand is integrable on $H$. The transformed square integrand also has an explicit repeated Darboux source integral with this value.

**Proof.** Write $T(u,v)=(1,1)+u(2,1)+v(1,3)$. This gives all four vertices and identifies its square image with the stated parallelogram, including its boundary. The actual derivative is the constant matrix

$$
\begin{pmatrix}2&1\\1&3\end{pmatrix},
$$

whose determinant is $6-1=5$. The same two linear equations show that $T$ is injective. Compactness of its square image and continuity of the exponential give integrability independently of the substitution. Change of variables applies to this injective differentiable map, and $T_1-T_2=u-2v$. Separating the exponential gives

$$
5\left(\int_0^1 e^u\,du\right)\left(\int_0^1 e^{-2v}\,dv\right)
=5(e-1)\frac{1-e^{-2}}2.
$$

Continuity on the square gives every stage of the transformed repeated Darboux integral, and the same one-dimensional calculation gives its value.

All four `R10E08` obligations remain todo with no mapped declarations, although the current file proves these results. The explicit source-integral witness is for the transformed square; the file expresses the original-region substitution as a measure-integral theorem, not as a separate source witness for the zero extension on $H$.

**Lean declarations:** `Rudin.Chapter10.Exercise08.vertices`, `Rudin.Chapter10.Exercise08.image_square`, `Rudin.Chapter10.Exercise08.affine_formula`, `Rudin.Chapter10.Exercise08.hasFDerivAt_transform`, `Rudin.Chapter10.Exercise08.jacobian`, `Rudin.Chapter10.Exercise08.injective`, `Rudin.Chapter10.Exercise08.integrand_transform`, `Rudin.Chapter10.Exercise08.transformed_integral`, `Rudin.Chapter10.Exercise08.integrable_integrand`, `Rudin.Chapter10.Exercise08.square_integral_value`, `Rudin.Chapter10.Exercise08.integral_value`, `Rudin.Chapter10.Exercise08.transformed_source`.

<a id="r10e09"></a>
### 10.9 — Polar integration and the correct slit

**Lean source:** [Exercise09.lean](../../../Math/Rudin/Chapter10/Exercise09.lean).

**Inventory status:** Pending verification.

**Statement.** For $a\ge0$, let $D_a=\{(x,y):x^2+y^2\le a^2\}$ and $T(r,\theta)=(r\cos\theta,r\sin\theta)$. The image of $[0,a]\times[0,2\pi]$ is $D_a$. The map is injective on $(0,a)\times(0,2\pi)$, and its Jacobian is $r$. If $f$ is continuous on $D_a$, with real or complex values, then

$$
\int_{D_a}f(x,y)\,dx\,dy
=\int_0^a\left(\int_0^{2\pi}r f(r\cos\theta,r\sin\theta)\,d\theta\right)dr.
$$

The finite-disk measure identity also holds for real Banach-valued coefficients. For real $f$, the right side has explicit repeated Darboux witnesses; for complex $f$, such witnesses are supplied for both components. Continuous cutoffs with compact support in the open slit disk remove a compact-interior-support restriction. All assertions about integration include $a=0$.

The printed differential/bound assignment is not this formula. With its literal usual nested binding, $f=1$ and $a=1$ give $2\pi^2$ instead of $\pi$. The angular interval $(0,2\pi)$ requires a positive-$x$-axis slit, not the positive-$y$-axis slit in the hint.

**Proof.** The identity $\|T(r,\theta)\|_2^2=r^2$ proves containment. Conversely, represent $x+iy$ by its modulus and argument, adding $2\pi$ to negative arguments. Its modulus lies in $[0,a]$, and the adjusted angle lies in $[0,2\pi]$. This includes the origin. Shifting the angle by $-\pi$ and negating the target reduces injectivity on the open parameter rectangle to the standard polar chart. Differentiation gives columns $(\cos\theta,\sin\theta)$ and $(-r\sin\theta,r\cos\theta)$, with determinant $r$.

The map is also injective on $(0,a]\times(0,2\pi)$, whose image is the closed disk with the positive-$x$-axis radius removed. The omitted set is null; the proof bounds it by the horizontal coordinate line. Change of variables gives the disk integral as the integral of $r f(T(r,\theta))$ over this parameter set. Continuity on the compact closed disk proves integrability. The transformed integrand is continuous on the closed parameter rectangle and hence integrable there. Fubini and the irrelevance of interval endpoints give the displayed angular-inner, radial-outer formula.

For the approximation assertion, the open slit disk is the disk interior with that same radius removed. Its difference from the closed disk is null, since both the convex frontier and the slit are null. Exhaust the open slit by compact subsets and choose continuous cutoffs $0\le\chi_n\le1$, equal to one on each selected compact set and supported compactly inside the open slit. Every point of the open slit eventually has cutoff one. Although $f$ is assumed continuous only on the disk, each $\chi_nf$ is globally continuous: its support lies in the disk interior. Domination by $|f|$ proves convergence of the cutoff integrals to the full disk integral. Thus no boundary-vanishing hypothesis on $f$ is needed. At radius zero the disk is a null singleton and the radial integral is zero.

For the source witnesses, use coordinates $(\theta,r)$ on $[0,2\pi]\times[0,a]$ so that coordinate zero is integrated first. Continuity gives all real Darboux stages. Applying this to the real and imaginary parts and commuting those projections with integration gives the complex component statements.

Finally, the literal printed reading integrates $r$ from $0$ to $2\pi$ and the angle from $0$ to $1$, giving $2\pi^2$. The corrected unit-disk formula gives $\pi$. These values are unequal.

All five `R10E09` obligations remain todo and unmapped in the inventory. The file proves the geometry, correction, approximation, and measure identity above. Its explicit source witnesses concern the polar side, with component witnesses rather than a direct recursive complex tagged-sum predicate; no separate source witness for the disk zero extension is stated here.

**Lean declarations:** `Rudin.Chapter10.Exercise09.range`, `Rudin.Chapter10.Exercise09.interior_injective`, `Rudin.Chapter10.Exercise09.hasFDerivAt_transform`, `Rudin.Chapter10.Exercise09.jacobian`, `Rudin.Chapter10.Exercise09.image_slit`, `Rudin.Chapter10.Exercise09.slit_ae_disk`, `Rudin.Chapter10.Exercise09.disk_integral`, `Rudin.Chapter10.Exercise09.polar_integrable`, `Rudin.Chapter10.Exercise09.polar_integral`, `Rudin.Chapter10.Exercise09.slit_approximation`, `Rudin.Chapter10.Exercise09.polar_source_real`, `Rudin.Chapter10.Exercise09.polar_source_complex`, `Rudin.Chapter10.Exercise09.corrected_constant_value`, `Rudin.Chapter10.Exercise09.disk_area_one`, `Rudin.Chapter10.Exercise09.literal_value`, `Rudin.Chapter10.Exercise09.literal_order_obstruction`, `Rudin.Chapter10.Exercise09.literal_disk_obstruction`.

<a id="r10e10"></a>
### 10.10 — Decay, improper polar integration, and the Gaussian

**Lean source:** [Exercise10.lean](../../../Math/Rudin/Chapter10/Exercise10.lean).

**Inventory status:** Pending verification.

**Statement.** A sufficient decay condition for a continuous real or complex function on the Euclidean plane is

$$
|f(x)|\le C(1+\|x\|)^{-q}\quad(x\in\mathbb R^2),\qquad C\ge0,\quad q>2.
$$

Under this condition, $f$ and $|f|$ are integrable. Integrals over expanding closed disks and coordinate squares $[-R,R]^2$ converge to the same plane integral, for both functions. Defining the improper polar integral by keeping the full angular interval at each radial cutoff gives

$$
\int_{\mathbb R^2}f
=\lim_{a\to\infty}\int_0^a\left(\int_0^{2\pi}r f(r\cos\theta,r\sin\theta)\,d\theta\right)dr,
$$

with absolute convergence in the same cutoff sense. In particular,

$$
\int_{\mathbb R}e^{-s^2}\,ds=\sqrt\pi,
\qquad
\lim_{R\to\infty}\int_{-R}^{R}e^{-s^2}\,ds=\sqrt\pi.
$$

Each finite one-dimensional Gaussian cut has a Darboux source integral. The printed reversed radial/angular binding instead gives a divergent Gaussian cutoff.

**Proof.** The standard integrability criterion for $(1+\|x\|)^{-q}$ in dimension two applies because $q>2$. The bound and continuity then prove integrability of $f$ and its norm. This includes $C=0$. Disks and coordinate squares are increasing measurable exhaustions of the plane. Convergence of set integrals of an integrable function proves agreement of their limits, also for the norm. The finite-disk formula from Exercise 10.9 identifies each nonnegative-radius disk integral with the correctly bound polar cutoff. Passing to the limit proves the polar formula and its absolute version.

For $G(x)=e^{-\|x\|^2}$, the source verifies the explicit decay bound $G(x)\le24(1+\|x\|)^{-4}$. It follows from the exponential power estimate and $(1+t)^4\le24e^{t^2}$ for $t\ge0$. In polar coordinates $G=e^{-r^2}$. The antiderivative $-e^{-r^2}/2$ gives

$$
\int_0^a r e^{-r^2}\,dr=\frac{1-e^{-a^2}}2,
\qquad
\int_0^a\int_0^{2\pi}r e^{-r^2}\,d\theta\,dr=\pi(1-e^{-a^2}).
$$

The limit is $\pi$, so the plane Gaussian integral is $\pi$. The one-dimensional Gaussian is integrable by the library integrability theorem. In Cartesian coordinates $G(x,y)=e^{-x^2}e^{-y^2}$; product integration gives $I^2=\pi$, where $I=\int_{\mathbb R}e^{-s^2}\,ds\ge0$. Thus $I=\sqrt\pi$. Continuity supplies the Darboux witness on every ordered finite interval, including singleton intervals. Integrability then identifies the symmetric finite-cut limit with $I$.

With the literal printed binding, the Gaussian cutoff is instead

$$
L(A)=\int_0^A\left(\int_0^{2\pi}r e^{-r^2}\,dr\right)d\theta
=A\frac{1-e^{-(2\pi)^2}}2.
$$

Its coefficient is positive. Hence $L(A)\to+\infty$ and it has no finite limit, unlike the corrected plane integral.

All four `R10E10` obligations remain todo and unmapped. The general improper integrals here are explicitly defined as limits of finite measure integrals, with their convergence proved. The file does not supply a separate literal repeated-Riemann comparison for every general decay function and every Cartesian cutoff; its direct finite source witnesses are for the one-dimensional Gaussian. This distinguishes the established improper-measure formulation from a broader source-integral certification.

**Lean declarations:** `Rudin.Chapter10.Exercise10.integrable_of_decay`, `Rudin.Chapter10.Exercise10.disk_exhaustion`, `Rudin.Chapter10.Exercise10.rectangle_exhaustion`, `Rudin.Chapter10.Exercise10.decay_convergence`, `Rudin.Chapter10.Exercise10.disk_polar`, `Rudin.Chapter10.Exercise10.whole_plane_polar`, `Rudin.Chapter10.Exercise10.absolute_polar_convergence`, `Rudin.Chapter10.Exercise10.gaussian_decay`, `Rudin.Chapter10.Exercise10.gaussian_polar`, `Rudin.Chapter10.Exercise10.radial_gaussian_integral`, `Rudin.Chapter10.Exercise10.gaussian_cutoff`, `Rudin.Chapter10.Exercise10.gaussian_plane_integral`, `Rudin.Chapter10.Exercise10.gaussian_integral`, `Rudin.Chapter10.Exercise10.gaussian_finite_source`, `Rudin.Chapter10.Exercise10.gaussian_improper`, `Rudin.Chapter10.Exercise10.literal_cutoff_value`, `Rudin.Chapter10.Exercise10.literal_order_obstruction`, `Rudin.Chapter10.Exercise10.literal_no_finite_value`.

<a id="r10e11"></a>
### 10.11 — The beta–gamma substitution

**Lean source:** [Exercise11.lean](../../../Math/Rudin/Chapter10/Exercise11.lean).

**Inventory status:** Pending verification.

**Statement.** The map $T(s,t)=(s-st,st)$ is a bijection from $S=(0,\infty)\times(0,1)$ onto $Q=(0,\infty)^2$, with inverse $(u,v)\mapsto(u+v,v/(u+v))$ and Jacobian $s$. For an integrable coefficient on $Q$, substitution is valid on the full strip and along every increasing compact exhaustion of it. For $x,y>0$,

$$
\int_0^1 t^{x-1}(1-t)^{y-1}\,dt
=\frac{\Gamma(x)\Gamma(y)}{\Gamma(x+y)}.
$$

The beta integrand is absolutely integrable on $(0,1)$, including when it is unbounded near an endpoint. Each compact interior interval has a Darboux source integral. Those finite source values converge to the displayed value along any increasing compact-interval exhaustion of $(0,1)$.

**Proof.** For $s>0$ and $0<t<1$, both $s(1-t)$ and $st$ are positive. Conversely, $u,v>0$ give $s=u+v>0$ and $0<v/(u+v)<1$. Direct substitution verifies both inverse identities. Differentiation gives

$$
DT=\begin{pmatrix}1-t&-s\\t&s\end{pmatrix},\qquad \det DT=s.
$$

The injective differentiable change-of-variables theorem gives the measure-integral identity, and its integrability version gives

$$
f\in L^1(Q)\quad\Longleftrightarrow\quad s f(T(s,t))\in L^1(S).
$$

The convergence assertion assumes $f\in L^1(Q)$ and compact sets $K_n$ with $K_n\subset K_{n+1}$ and $\bigcup_nK_n=S$. Finite substitution holds on each $K_n$, and integrability makes both the transformed cut integrals and their image integrals tend to $\int_Q f$. Such compact exhaustions exist because the strip is open in the plane. Equality of totalized integrals alone is not used to infer convergence.

Put $g_z(u)=e^{-u}u^{z-1}$. To obtain the displayed beta integrand with this choice of $T$, the source uses the quadrant kernel $g_y(u)g_x(v)$. Its integral is $\Gamma(y)\Gamma(x)$ and it is integrable by the gamma-integral convergence theorem. The transformed kernel factors as

$$
s\,g_y(s-st)g_x(st)
=e^{-s}s^{x+y-1}t^{x-1}(1-t)^{y-1}.
$$

All bases are positive on the strip, so the real-power product rules apply. Product integration therefore gives

$$
\Gamma(x)\Gamma(y)=\Gamma(x+y)\int_0^1t^{x-1}(1-t)^{y-1}\,dt.
$$

Divide by $\Gamma(x+y)>0$. This derives the beta value from the substitution rather than invoking a beta–gamma evaluation theorem. Transported integrability of the two-dimensional kernel, followed by integration in $s$, shows that $\Gamma(x+y)$ times the beta integrand is integrable; division by this positive constant proves beta integrability. Endpoints have measure zero, so the open-interval and interval-integral values agree.

On $[a,b]\subset(0,1)$, the integrand is continuous for arbitrary real exponents, and hence has the literal Darboux integral. For $x,y>0$, integrability and increasing exhaustion by such intervals prove convergence of these source values, including all singular endpoint cases allowed by the strict positivity assumptions.

All four `R10E11` obligations remain todo and unmapped. The full-strip change of variables and compact-exhaustion extension are measure-integral statements with explicit integrability hypotheses. The file additionally proves the one-dimensional improper beta source bridge; it does not state a general multidimensional source-Riemann theorem for arbitrary integrable coefficients on arbitrary compact exhaustion sets.

**Lean declarations:** `Rudin.Chapter10.Exercise11.bijection`, `Rudin.Chapter10.Exercise11.left_inverse`, `Rudin.Chapter10.Exercise11.right_inverse`, `Rudin.Chapter10.Exercise11.hasFDerivAt_transform`, `Rudin.Chapter10.Exercise11.jacobian`, `Rudin.Chapter10.Exercise11.integral_transform`, `Rudin.Chapter10.Exercise11.integrable_transform_iff`, `Rudin.Chapter10.Exercise11.improper_extension`, `Rudin.Chapter10.Exercise11.exists_strip_exhaustion`, `Rudin.Chapter10.Exercise11.kernel_transform`, `Rudin.Chapter10.Exercise11.quadrant_integrable`, `Rudin.Chapter10.Exercise11.quadrant_integral`, `Rudin.Chapter10.Exercise11.beta_gamma_Ioo`, `Rudin.Chapter10.Exercise11.beta_gamma`, `Rudin.Chapter10.Exercise11.strip_kernel_integrable`, `Rudin.Chapter10.Exercise11.beta_integrable`, `Rudin.Chapter10.Exercise11.beta_source_cut`, `Rudin.Chapter10.Exercise11.beta_source_improper`.

<a id="r10e12"></a>
### 10.12 — A triangular map from the cube to the simplex

**Lean source:** [Exercise12.lean](../../../Math/Rudin/Chapter10/Exercise12.lean).

**Inventory status:** Pending verification.

**Statement.** Define, in source coordinate order,

$$
x_i=T(u)_i=u_i\prod_{j<i}(1-u_j),\qquad
S(x)_i=\frac{x_i}{1-\sum_{j<i}x_j}.
$$

Then

$$
\sum_{i=1}^n x_i=1-\prod_{i=1}^n(1-u_i),\qquad
T([0,1]^n)=Q^n.
$$

The map is injective on the cube interior and maps that interior bijectively onto the simplex interior, with inverse $S$. On the entire closed simplex, $S$ is a chosen right inverse of $T$, using value zero for a quotient whose denominator is zero. The actual Jacobians are

$$
J_T(u)=\prod_{i=1}^{n-1}(1-u_i)^{n-i},\qquad
J_S(x)=\left[\prod_{i=1}^{n-1}\left(1-\sum_{j=1}^{i}x_j\right)\right]^{-1},
$$

where the second formula is asserted on the simplex interior. The forward formula holds for all $u$. Empty sums and products cover $n=0$ and $n=1$; both determinants are $1$ in these cases.

**Proof.** Expanding the ordered product $\prod_i(1-u_i)$ by successive subtraction gives the sum identity. The same identity on each initial segment gives

$$
1-\sum_{j<i}T(u)_j=\prod_{j<i}(1-u_j).
$$

For $u\in[0,1]^n$, all coordinates of $T(u)$ are nonnegative, and the full sum is at most one. Conversely, for $x\in Q^n$, let $R_i=1-\sum_{j<i}x_j$. Nonnegativity of the remaining coordinates gives $0\le x_i\le R_i$. Thus $x_i/R_i\in[0,1]$ when $R_i>0$; when $R_i=0$, one also has $x_i=0$ and the chosen quotient is zero. Induction on $i$, using the prefix identity and previously recovered coordinates, proves $T(S(x))=x$ on the whole closed simplex. This proves closed-domain surjectivity without dividing by a zero denominator.

On the open cube, every prefix product is positive, so the same identity permits cancellation and gives $S(T(u))=u$. The forward coordinates are positive and their sum is strictly less than one. Conversely, the strict simplex inequalities give $0<x_i<R_i$, so $S(x)$ lies in the open cube. These sets are the actual topological interiors: the strict inequalities define open subsets, while a point in the closed simplex interior must have positive coordinates; a small positive change in one coordinate also forces its sum to be strictly less than one. Dimension zero is handled separately in this last argument.

The product and reciprocal differentiation rules give genuine Fréchet derivatives. Their matrices are lower triangular. The forward diagonal entry in row $i$ is $\prod_{j<i}(1-u_j)$, so multiplication of diagonal entries counts each factor $1-u_j$ exactly $n-j$ times. The inverse diagonal entry is $R_i^{-1}$. Its first denominator is one, leaving precisely the displayed product through $n-1$. Positivity of the denominators justifies differentiation of $S$ on the interior.

All six `R10E12` obligations remain marked in progress, although the current source includes the closed boundary and interior results above.

**Lean declarations:** `Rudin.Chapter10.Exercise12.coordinate_sum`, `Rudin.Chapter10.Exercise12.surjectivity`, `Rudin.Chapter10.Exercise12.S_mem_cube`, `Rudin.Chapter10.Exercise12.T_S`, `Rudin.Chapter10.Exercise12.S_T`, `Rudin.Chapter10.Exercise12.interior_injectivity`, `Rudin.Chapter10.Exercise12.injective_on_interior`, `Rudin.Chapter10.Exercise12.openCube_eq_interior`, `Rudin.Chapter10.Exercise12.interior_inverse`, `Rudin.Chapter10.Exercise12.openSimplex_eq_interior`, `Rudin.Chapter10.Exercise12.T_mem_openSimplex`, `Rudin.Chapter10.Exercise12.S_mem_openCube`, `Rudin.Chapter10.Exercise12.forward_jacobian`, `Rudin.Chapter10.Exercise12.hasFDerivAt_T`, `Rudin.Chapter10.Exercise12.inverse_jacobian`, `Rudin.Chapter10.Exercise12.hasFDerivAt_S`.

<a id="r10e13"></a>
### 10.13 — Monomial moments and simplex volume

**Lean source:** [Exercise13.lean](../../../Math/Rudin/Chapter10/Exercise13.lean).

**Inventory status:** Pending verification.

**Statement.** For nonnegative integers $r_1,\ldots,r_n$ and $q$, the current source proves the stronger barycentric moment formula

$$
\int_{Q^n}\left(\prod_{i=1}^n x_i^{r_i}\right)\left(1-\sum_{i=1}^n x_i\right)^q dx
=\frac{\left(\prod_{i=1}^n r_i!\right)q!}{\left(n+\sum_{i=1}^n r_i+q\right)!}.
$$

In particular,

$$
\int_{Q^n}\prod_i x_i^{r_i}\,dx
=\frac{\prod_i r_i!}{(n+\sum_i r_i)!},\qquad
\operatorname{vol}(Q^n)=\frac1{n!}.
$$

The monomial is integrable. Its literal zero extension to the unit cube has repeated Darboux integrals in every coordinate order and a multidimensional tagged Riemann integral, all with the stated monomial value. Dimension zero and zero exponents are included.

**Proof.** The beta–gamma theorem at positive integer parameters gives

$$
\int_0^1 t^p(1-t)^q\,dt=\frac{p!q!}{(p+q+1)!}.
$$

Scaling the polynomial integral yields, for every real $a$,

$$
\int_0^a t^p(a-t)^q\,dt
=a^{p+q+1}\frac{p!q!}{(p+q+1)!}.
$$

This includes $a=0$ and uses oriented interval integration when $a<0$.

Induct on the dimension for the stronger moment formula. Separate the first coordinate $t$ from the remaining coordinates $z\in Q^{n-1}$, and write $a=1-\sum z_i\ge0$. The simplex slicing theorem gives the inner integral

$$
\left(\prod_{i=2}^n z_i^{r_i}\right)\int_0^a t^{r_1}(a-t)^q\,dt
=\left(\prod_{i=2}^n z_i^{r_i}\right)a^{r_1+q+1}
\frac{r_1!q!}{(r_1+q+1)!}.
$$

Apply the induction hypothesis with final barycentric exponent $r_1+q+1$. The factorial $(r_1+q+1)!$ cancels, giving the displayed formula. A slice with $a=0$ causes no exception. In dimension zero the domain has its normalized singleton measure, the empty monomial is one, and both sides equal one.

Taking $q=0$ gives the monomial formula; taking every $r_i=0$ gives volume. Continuity on the compact simplex proves integrability independently of the evaluated total integral. The local support results for the simplex zero extension supply every source Darboux stage, preserve the actual boundary values, and identify every permuted order with the set integral. The tagged-box comparison gives the multidimensional Riemann witness with the same value.

Both `R10E13` obligations remain marked in progress in the inventory.

**Lean declarations:** `Rudin.Chapter10.Exercise13.beta_natural`, `Rudin.Chapter10.Exercise13.beta_scaled`, `Rudin.Chapter10.Exercise13.mixed_moment`, `Rudin.Chapter10.Exercise13.monomial_integral`, `Rudin.Chapter10.Exercise13.monomial_integrable`, `Rudin.Chapter10.Exercise13.monomial_source`, `Rudin.Chapter10.Exercise13.monomial_riemann`, `Rudin.Chapter10.Exercise13.simplex_volume`.

<a id="r10e14"></a>
### 10.14 — The wedge sorting sign equals the determinant sign

**Lean source:** [Exercise14.lean](../../../Math/Rudin/Chapter10/Exercise14.lean).

**Inventory status:** Pending verification.

**Statement.** Let $j=(j_1,\ldots,j_k)$ be coordinate indices and $\sigma$ a permutation of their positions. Define $s(\sigma)$ as the determinant of the corresponding permutation matrix. Then

$$
dx_{j_{\sigma(1)}}\wedge\cdots\wedge dx_{j_{\sigma(k)}}
=s(\sigma)\,dx_{j_1}\wedge\cdots\wedge dx_{j_k},
\qquad s(\sigma)=\operatorname{sgn}(\sigma).
$$

Thus the sign obtained by sorting distinct coordinate differentials is the determinant sign in the source equation. A transposition of distinct positions negates the wedge. The permutation identity also applies to repeated coordinate indices, when the alternating wedge vanishes, and to the empty wedge.

**Proof.** Regard each $dx_i$ as the coordinate covector and their wedge as the canonical alternating multilinear product in the exterior algebra of the dual space. The alternating-map permutation law multiplies this product by the permutation sign. The determinant permutation law gives exactly the same sign for the row-permuted identity matrix, since the identity determinant is one. This identifies the two definitions of sign. The alternating-map interchange law gives the transposition assertion directly. Alternation also makes a tuple with equal covectors in distinct positions vanish, so repeated indices introduce no exception.

`R10E14.permutation_sign` remains marked in progress in the inventory.

**Lean declarations:** `Rudin.Chapter10.Exercise14.permutation_sign`, `Rudin.Chapter10.Exercise14.determinantSign_eq`, `Rudin.Chapter10.Exercise14.interchange`.

<a id="r10e15"></a>
### 10.15 — Graded commutation of differential forms

**Lean source:** [Exercise15.lean](../../../Math/Rudin/Chapter10/Exercise15.lean).

**Inventory status:** Pending verification.

**Statement.** If $\omega$ is a real $k$-form and $\lambda$ a real $m$-form on a common domain, then

$$
\omega\wedge\lambda=(-1)^{km}\lambda\wedge\omega.
$$

The wedge has degree $k+m$. Products of coordinate wedges with a repeated index vanish. Forms are represented as sections of homogeneous exterior powers of the dual space, and the wedge is actual exterior-algebra multiplication. The result is pointwise: it requires neither coefficient regularity nor an open domain, and it includes degree zero. More generally, the homogeneous-element identity holds in the exterior algebra of any real module.

**Proof.** First consider decomposable homogeneous elements $a=u_1\wedge\cdots\wedge u_k$ and $b=v_1\wedge\cdots\wedge v_m$. Moving the first block past the second makes $km$ interchanges, so the exterior-algebra anticommutation law gives $ab=(-1)^{km}ba$. The source uses this standard law for the canonical alternating products. Such products span each homogeneous exterior power. Bilinearity, addition, and compatibility with scalar multiplication extend the identity by induction on these spans to arbitrary homogeneous elements.

Apply that identity to $\omega(x)$ and $\lambda(x)$ at every point $x$. The source first states the sign using integer units, then converts it to the literal real scalar $(-1)^{km}$. Multiplication of the degree-$k$ and degree-$m$ submodules lies in the degree-$(k+m)$ submodule. If one factor in the first block equals one factor in the second, their concatenated tuple has two equal entries in distinct positions. Its alternating product is zero, proving the repeated-index assertion without a distinctness restriction on the original tuples.

`R10E15.graded_commutation` remains marked in progress in the inventory.

**Lean declarations:** `Rudin.Chapter10.Exercise15.homogeneous_commutation`, `Rudin.Chapter10.Exercise15.graded_commutation`, `Rudin.Chapter10.Exercise15.graded_commutation_real`, `Rudin.Chapter10.Exercise15.wedge_mem`, `Rudin.Chapter10.Exercise15.wedge_repeated_index`.

<a id="r10e16"></a>
### 10.16 — The boundary of a boundary

**Lean source:** [Exercise16.lean](../../../Math/Rudin/Chapter10/Exercise16.lean).

**Inventory status:** Pending verification.

**Statement.** For an oriented affine simplex $\sigma=[p_0,\ldots,p_k]$ of dimension $k\geq2$, the alternating face boundary satisfies $\partial^2\sigma=0$. The same identity holds for every finite integer chain. In the ordinary, unaugmented convention, a zero-chain has zero boundary, so the identity also includes dimensions zero and one. These statements also hold for chains of full parameter maps, not only affine vertex lists. The algebraic result requires no differentiability assumption.

**Proof.** The boundary is

$$
\partial[p_0,\ldots,p_k]=\sum_{i=0}^k(-1)^i[p_0,\ldots,\widehat p_i,\ldots,p_k].
$$

For $i<j$, deleting $p_i$ and then $p_j$ has sign $(-1)^{i+j-1}$, whereas deleting $p_j$ and then $p_i$ has sign $(-1)^{i+j}$. Both operations give the same ordered face. Thus every term cancels with its other occurrence. In the ordered-list proof this cancellation is encoded by $\partial(a*c)=c-a*\partial c$ and induction. It holds before the orientation quotient and therefore after it. Additivity extends it to all signed chains, including all integer multiplicities.

For full maps, a face is restriction along the affine inclusion that omits a parameter vertex. The two deletion orders give equal full composite maps, and the same fixed-point-free pairing cancels the signed terms. Restriction commutes with arbitrary postcomposition, and the boundary commutes with both postcomposition and integer multiplication. This includes differentiable maps without imposing an extra $C^2$ condition.

The comparison with the source simplex is exact on the closed domain. If $u_i\geq0$ and $\sum u_i\leq1$, its barycentric coordinates are $(1-\sum u_i,u_1,\ldots,u_k)$. Every nonnegative barycentric tuple of sum one arises this way, and its realization is $p_0+\sum u_i(p_i-p_0)$. Inserting a zero weight realizes the deleted-vertex face. Consequently the Cartesian and barycentric ranges agree, including their boundaries, and every parameter face remains in the closed simplex. The empty-list generator belongs only to the augmented auxiliary model; the ordinary boundary in degree zero is the zero map.

**Lean declarations:** `Rudin.Chapter10.Exercise16.source_boundary`, `Rudin.Chapter10.Exercise16.deleted_pairs_cancel`, `Rudin.Chapter10.Exercise16.simplex_boundary_squared`, `Rudin.Chapter10.Exercise16.chain_boundary_squared`, `Rudin.Chapter10.Exercise16.ordinary_second_boundary`, `Rudin.Chapter10.Exercise16.zero_chain_boundary`, `Rudin.Chapter10.Exercise16.source_face`, `Rudin.Chapter10.Exercise16.barycentric_surjective`, `Rudin.Chapter10.Exercise16.source_range`, `Rudin.Chapter10.Exercise16.Parameterized.face_face`, `Rudin.Chapter10.Exercise16.Parameterized.boundary_squared`, `Rudin.Chapter10.Exercise16.Parameterized.ordinaryBoundary_squared`, `Rudin.Chapter10.Exercise16.Parameterized.boundary_multiplicity`, `Rudin.Chapter10.Exercise16.Parameterized.boundary_map`, `Rudin.Chapter10.Exercise16.Parameterized.source_face`, `Rudin.Chapter10.Exercise16.Parameterized.source_map`, `Rudin.Chapter10.Exercise16.Parameterized.face_domain`.

<a id="r10e17"></a>
### 10.17 — Two oriented triangles form a square

**Lean source:** [Exercise17.lean](../../../Math/Rudin/Chapter10/Exercise17.lean).

**Inventory status:** Pending verification.

**Statement.** Set $q_0=(0,0)$, $q_1=(1,0)$, $q_2=(1,1)$, $q_3=(0,1)$, and let $\tau_1=[q_0,q_1,q_2]$, $\tau_2=-[q_0,q_3,q_2]$. Their sum $J^2$ is the positively oriented unit square: their closed ranges cover the square and have disjoint interiors. Its boundary is

$$
\partial J^2=[q_0,q_1]+[q_1,q_2]+[q_2,q_3]+[q_3,q_0].
$$

In contrast,

$$
\partial(\tau_1-\tau_2)=[q_0,q_1]+[q_1,q_2]+[q_0,q_3]+[q_3,q_2]-2[q_0,q_2].
$$

**Proof.** The first affine triangle has range $0\leq y\leq x\leq1$: the inverse barycentric weights are $(1-x,x-y,y)$. The second has range $0\leq x\leq y\leq1$, with weights $(1-y,y-x,x)$. These formulas retain the diagonal, edges, and vertices. The two possible orders of $x,y$ prove coverage. An interior point of a region constrained by $x\leq y$ must satisfy $x<y$: the nonzero linear map $(x,y)\mapsto x-y$ is open, so the interior maps into the interior of $(-\infty,0]$. Applying this to both triangles proves disjointness of their interiors.

The two vertex-difference matrices have determinants $1$ and $-1$. The coefficient $-1$ in $\tau_2$ therefore makes both signed triangles positive; it does not change their geometric ranges. Expand each triangle boundary. In the sum the diagonal cancels and reversed outer edges acquire their cyclic signs. In the difference the diagonal occurs with coefficient $-2$, which gives the second displayed formula.

**Lean declarations:** `Rudin.Chapter10.Exercise17.lower_range`, `Rudin.Chapter10.Exercise17.upper_range`, `Rudin.Chapter10.Exercise17.range₁`, `Rudin.Chapter10.Exercise17.range₂`, `Rudin.Chapter10.Exercise17.square_coverage`, `Rudin.Chapter10.Exercise17.interior_coordinate_lt`, `Rudin.Chapter10.Exercise17.disjoint_interiors`, `Rudin.Chapter10.Exercise17.positive_orientations`, `Rudin.Chapter10.Exercise17.J2_value`, `Rudin.Chapter10.Exercise17.square_boundary`, `Rudin.Chapter10.Exercise17.difference_boundary`.

<a id="r10e18"></a>
### 10.18 — Six tetrahedra form a cube

**Lean source:** [Exercise18.lean](../../../Math/Rudin/Chapter10/Exercise18.lean).

**Inventory status:** Pending verification.

**Statement.** For each permutation $p=(i,j,k)$ of $(1,2,3)$, take

$$
\sigma_p=\operatorname{sgn}(p)[0,e_i,e_i+e_j,e_1+e_2+e_3].
$$

All six signed tetrahedra have positive orientation. Their ranges cover $[0,1]^3$ with pairwise disjoint interiors, and the range in order $(1,2,3)$ is $0\leq x_3\leq x_2\leq x_1\leq1$. The boundary of their sum $J^3$ consists of twelve oriented triangles on the six square faces.

**Proof.** The six orders $123,132,213,231,312,321$ have signs $+,-,-,+,+,-$ and exhaust all permutations exactly once. The cumulative-sum vertex matrix has the determinant of the corresponding permutation matrix. The first determinant is $1$; multiplying any determinant by its prescribed sign gives $1$.

For order $(i,j,k)$, the affine coordinates of barycentric weights are $(w_1+w_2+w_3,w_2+w_3,w_3)$ in that order. Thus its exact range is $0\leq x_k\leq x_j\leq x_i\leq1$. Conversely, such a point has weights

$$
(1-x_i,\ x_i-x_j,\ x_j-x_k,\ x_k).
$$

Sorting three real coordinates proves cube coverage, including ties and coordinates zero or one. Interior points have strict coordinate order, by the open-linear-map argument of Exercise 17. Different orders cannot both hold strictly, so the interiors are disjoint.

Write $S(a,b,c,d)=[a,b,c]-[a,d,c]$ and $s=e_1+e_2+e_3$. Expanding the twenty-four signed faces gives

$$
\begin{aligned}
\partial J^3={}&S(e_1,e_1+e_2,s,e_1+e_3)-S(0,e_2,e_2+e_3,e_3)\\
&-S(e_2,e_1+e_2,s,e_2+e_3)+S(0,e_1,e_1+e_3,e_3)\\
&+S(e_3,e_1+e_3,s,e_2+e_3)-S(0,e_1,e_1+e_2,e_2).
\end{aligned}
$$

The twelve internal face occurrences cancel in pairs, leaving two triangles on each coordinate face. More precisely, insert $r$ into coordinate $i$ of each of the two triangle maps from Exercise 17. Affine realization commutes with this insertion. Their combined range is exactly $x_i=r$ with the remaining coordinates in $[0,1]$. Taking $r=0,1$ gives exactly the cube surface, including all edges and corners. This establishes geometric coverage as well as the chain identity.

**Lean declarations:** `Rudin.Chapter10.Exercise18.order_bijective`, `Rudin.Chapter10.Exercise18.all_permutations`, `Rudin.Chapter10.Exercise18.vertices_permutation`, `Rudin.Chapter10.Exercise18.sign_determinant`, `Rudin.Chapter10.Exercise18.first_orientation`, `Rudin.Chapter10.Exercise18.positive_orientations`, `Rudin.Chapter10.Exercise18.coordinates`, `Rudin.Chapter10.Exercise18.range_iff`, `Rudin.Chapter10.Exercise18.first_range`, `Rudin.Chapter10.Exercise18.cube_coverage`, `Rudin.Chapter10.Exercise18.interior_order`, `Rudin.Chapter10.Exercise18.disjoint_interiors`, `Rudin.Chapter10.Exercise18.J3_value`, `Rudin.Chapter10.Exercise18.cube_boundary`, `Rudin.Chapter10.Exercise18.faceTriangle_realize`, `Rudin.Chapter10.Exercise18.face_coverage`, `Rudin.Chapter10.Exercise18.surface_coverage`.

<a id="r10e19"></a>
### 10.19 — The alternating cube-face formula

**Lean source:** [Exercise19.lean](../../../Math/Rudin/Chapter10/Exercise19.lean).

**Inventory status:** Pending verification.

**Statement.** Define the affine coordinate insertions $B_{r1}(u,v)=(r,u,v)$, $B_{r2}(u,v)=(u,r,v)$, $B_{r3}(u,v)=(u,v,r)$, and let $\beta_{ri}=B_{ri}(J^2)$ as an oriented affine two-chain. Then

$$
\partial J^3=\sum_{i=1}^3(-1)^i(\beta_{0i}-\beta_{1i}).
$$

This is equality of chains, with their signs and multiplicities, not only equality of ranges or integral values.

**Proof.** Affine maps preserve barycentric combinations of weights summing to one. Thus mapping the vertices by $B_{ri}$ is exactly postcomposition of each full affine triangle map. In particular, $\beta_{ri}$ is the square chain on the four inserted vertices, or equivalently the first inserted triangle minus the second inserted triangle. Substitute these six square chains in the boundary expansion from Exercise 18. The faces with fixed first and third coordinates occur as upper minus lower, and the faces with fixed second coordinate as lower minus upper. These are precisely the signs in the displayed formula. The formal indexing starts at zero, so its exponent is the coordinate index plus one.

**Lean declarations:** `Rudin.Chapter10.Exercise19.insertion_formulas`, `Rudin.Chapter10.Exercise19.insertion_realize`, `Rudin.Chapter10.Exercise19.β_value`, `Rudin.Chapter10.Exercise19.β_triangles`, `Rudin.Chapter10.Exercise19.face_chain_value`, `Rudin.Chapter10.Exercise19.face_triangles`, `Rudin.Chapter10.Exercise19.cube_face_formula`.

<a id="r10e20"></a>
### 10.20 — Integration by parts for differential forms

**Lean source:** [Exercise20.lean](../../../Math/Rudin/Chapter10/Exercise20.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $U$ be open in a real normed space, $f:U\to\mathbb R$ be $C^1$, and $\omega$ be a $C^1$ differential $n$-form on $U$. Let $\Phi$ be a finite integer chain of $(n+1)$-simplex maps, each $C^2$ on an open neighborhood of its closed parameter simplex, whose entire closed images lie in $U$. With the signed restriction boundary,

$$
\int_\Phi f\,d\omega=\int_{\partial\Phi}f\omega-\int_\Phi df\wedge\omega.
$$

Every coefficient integral and each boundary-face integral exists; the simplex integrals also have the source repeated Riemann interpretation in every coordinate order. The formula descends to the oriented quotient for any chain with such an admissible representative. It includes zero chains and integer multiplicities.

**Proof.** The differential wedge is the usual unnormalized alternation:

$$
(df\wedge\omega)_x(v_0,\ldots,v_n)=\sum_{i=0}^n(-1)^i df_x(v_i)\,\omega_x(v_0,\ldots,\widehat v_i,\ldots,v_n).
$$

The derivative product rule and linearity of alternation give $d(f\omega)=f\,d\omega+df\wedge\omega$. Both summands and $f\omega$ are continuous on $U$. Their pullback coefficients are continuous on the compact closed parameter simplexes, including every face, which supplies integrability and the repeated Riemann witnesses. Apply Stokes to $f\omega$, split its integral using that integrability, and rearrange. Linearity extends the calculation from a simplex to the full integer chain. Integration and boundary respect the orientation relations, so the quotient statement follows from any admissible representative.

For $n=0$, take the zero-form $g$ on $\mathbb R$ and the affine segment from $a$ to $b$. Its one-form integral is the oriented interval integral; its zero-dimensional signed boundary evaluates to $f(b)g(b)-f(a)g(a)$, and $df\wedge g=g\,df$. Consequently, for globally $C^1$ real functions $f,g$ and any $a,b$,

$$
\int_a^b f(x)g'(x)\,dx=f(b)g(b)-f(a)g(a)-\int_a^b f'(x)g(x)\,dx.
$$

This holds for either endpoint order. For $a\leq b$, including $a=b$, both terms have actual Darboux Riemann integral witnesses, obtained from their continuous coefficients.

**Lean declarations:** `Rudin.Chapter10.Exercise20.validity_conditions`, `Rudin.Chapter10.Exercise20.continuous_terms`, `Rudin.Chapter10.Exercise20.differentialWedge_apply`, `Rudin.Chapter10.Exercise20.exterior_product`, `Rudin.Chapter10.Exercise20.form_identity`, `Rudin.Chapter10.Exercise20.oriented_form_identity`, `Rudin.Chapter10.Exercise20.differentialWedge_zero`, `Rudin.Chapter10.Exercise20.segment_integral`, `Rudin.Chapter10.Exercise20.segment_boundary`, `Rudin.Chapter10.Exercise20.one_variable_identity`, `Rudin.Chapter10.Exercise20.one_variable_case`.

<a id="r10e21"></a>
### 10.21 — The angular form and winding number

**Lean source:** [Exercise21.lean](../../../Math/Rudin/Chapter10/Exercise21.lean).

**Inventory status:** Pending verification.

**Statement.** On $\mathbb R^2\setminus\{0\}$, identify $z=x+iy$ and define

$$
\eta=\frac{x\,dy-y\,dx}{x^2+y^2}.
$$

The form is $C^1$ and closed, and its integral on the positive circle $\gamma_r(t)=(r\cos t,r\sin t)$, $r>0$, $0\leq t\leq2\pi$, is $2\pi$. If a closed curve $\Gamma$ is $C^2$ on an open neighborhood of $[0,2\pi]$ and every segment $[\gamma_r(t),\Gamma(t)]$ avoids zero, then $\int_\Gamma\eta=2\pi$. In particular, for $a,b>0$,

$$
\int_0^{2\pi}\frac{ab}{a^2\cos^2t+b^2\sin^2t}\,dt=2\pi.
$$

Locally, $\eta=d(\arctan(y/x))$ wherever $x\ne0$, and $\eta=d(-\arctan(x/y))$ wherever $y\ne0$. There is no single differentiable real potential on the punctured plane. Finally, for every closed $C^1$ curve $\Gamma:[a,b]\to\mathbb C\setminus\{0\}$, $a\leq b$, with continuous derivative jet $v$ satisfying the genuine within-derivative condition at all points, including endpoints,

$$
\frac1{2\pi}\int_a^b\eta_{\Gamma(t)}(v(t))\,dt=\operatorname{Ind}(\Gamma).
$$

The index is exactly the Chapter 8 index. Source Darboux Riemann witnesses are supplied for this angular integral, for the circle, for the homotopy conclusion, and for the ellipse.

**Proof.** The angular covector satisfies $\eta_z(v)=\operatorname{Im}(v/z)$. On the circle, $\gamma_r'=(-r\sin t,r\cos t)$ and the quotient coefficient is identically one, proving the circle value. Direct differentiation of the two arctangent charts gives the displayed covector. Each chart is $C^2$ where its denominator is nonzero, so $d\eta=d^2\theta=0$ locally. At least one chart applies at every nonzero point. If a global differentiable potential existed, its composition with the unit circle would have derivative one. The fundamental theorem of calculus would then give a change of $2\pi$ between equal endpoint values, a contradiction.

For the Stokes proof, rescale the parameter rectangle positively to the unit square and use

$$
H(s,u)=(1-u)\Gamma(2\pi s)+u\gamma_r(2\pi s).
$$

The segment hypothesis puts its closed image in the punctured plane. It is $C^2$ near the parameter square. Triangulate that square into two actual smooth triangles, apply simplex Stokes and $d\eta=0$, and cancel the internal diagonal. The two side restrictions coincide because both curves are closed, so their integrals cancel. The remaining two restrictions give equality with the circle integral. Positive linear rescaling preserves these path integrals. For the ellipse, the straight segment to the unit circle has coordinates $((u+va)\cos t,(u+vb)\sin t)$ with $u,v\geq0$, $u+v=1$; both factors are positive. It cannot vanish because sine and cosine cannot both vanish. Its angular coefficient is the displayed rational function, so the homotopy result applies.

There is also a proof without Stokes. Segment avoidance implies $\Gamma(t)/\gamma_r(t)$ lies off the nonpositive real axis. On this slit domain, the half-angle primitive

$$
A(z)=2\arctan\frac{y}{\sqrt{x^2+y^2}+x}
$$

has derivative $\eta$. Its denominator is positive. Along the quotient curve its derivative is $\eta_{\Gamma(t)}(\Gamma'(t))-1$, by the quotient rule and the circle calculation. The quotient has equal endpoints, so the fundamental theorem of calculus makes the integral of this difference zero.

For the general $C^1$ loop, the logarithmic derivative $v/\Gamma$ is continuous on the closed interval and integrable. Chapter 8 proves that its integral is $2\pi i n$ for an integer $n$, and defines the index as that integral divided by $2\pi i$. Taking imaginary parts gives the asserted angular identity, including the singleton interval case. The full-map path integral on $[0,1]$ agrees with this expression whenever $v$ is the actual ambient derivative. Continuity of the real angular coefficients supplies all stated source Riemann integrals.

**Lean declarations:** `Rudin.Chapter10.Exercise21.eta_eq_im_div`, `Rudin.Chapter10.Exercise21.circle_integral`, `Rudin.Chapter10.Exercise21.circle_derivative`, `Rudin.Chapter10.Exercise21.circle_coefficient`, `Rudin.Chapter10.Exercise21.circle_source_integral`, `Rudin.Chapter10.Exercise21.eta_closed`, `Rudin.Chapter10.Exercise21.eta_smooth`, `Rudin.Chapter10.Exercise21.closed_triangle_boundary`, `Rudin.Chapter10.Exercise21.closed_square_boundary`, `Rudin.Chapter10.Exercise21.straight_homotopy_stokes`, `Rudin.Chapter10.Exercise21.straight_homotopy_source`, `Rudin.Chapter10.Exercise21.ellipse_integral`, `Rudin.Chapter10.Exercise21.ellipse_source_integral`, `Rudin.Chapter10.Exercise21.xAngle_exterior`, `Rudin.Chapter10.Exercise21.xAngle_derivative`, `Rudin.Chapter10.Exercise21.yAngle_exterior`, `Rudin.Chapter10.Exercise21.yAngle_derivative`, `Rudin.Chapter10.Exercise21.local_angles_not_global`, `Rudin.Chapter10.Exercise21.not_globally_exact`, `Rudin.Chapter10.Exercise21.straight_homotopy_local_primitives`, `Rudin.Chapter10.Exercise21.cutAngle_curve_derivative`, `Rudin.Chapter10.Exercise21.winding_index`, `Rudin.Chapter10.Exercise21.angularIntegral_source`, `Rudin.Chapter10.Exercise21.pathIntegral_bridge`, `Rudin.Chapter10.Exercise21.angularIntegral_eq_im`, `Rudin.Chapter10.Exercise21.integral_rescale`.

<a id="r10e23"></a>
### 10.23 — Radial forms: closedness and partial exactness coverage

**Lean source:** [Exercise23.lean](../../../Math/Rudin/Chapter10/Exercise23.lean).

**Inventory status:** Pending verification.

**Statement.** For $1\leq k\leq N$, set $r_k=(\sum_{i=1}^k x_i^2)^{1/2}$ and $E_k=\{r_k>0\}$. The source radial form is

$$
\omega_k=r_k^{-k}\sum_{i=1}^k(-1)^{i-1}x_i\,dx_1\wedge\cdots\wedge\widehat{dx_i}\wedge\cdots\wedge dx_k.
$$

The completed source proves $d\omega_k=0$ on $E_k$ for every such $k$. For $k=1$ it also proves that $\omega_1=x_1/|x_1|$ is locally constant there. For $k\geq2$ and $-1<t<1$, it proves convergence, the derivative, and the improper-endpoint interpretation of

$$
g_k(t)=\int_{-1}^t(1-s^2)^{(k-3)/2}\,ds.
$$

In degree zero the added exactness convention is image $\{0\}$: a zero-form is exact on a domain if and only if it vanishes there. Positive-degree exactness means the exterior derivative of an actual $C^1$ form one degree lower. Under this explicit convention, the one-dimensional form on the punctured line is closed but not exact.

Further completed results concern sphere patches and radial rescaling. Let $K\subset\mathbb R^m$ be compact, $U$ an open neighborhood of $K$, and let $\sigma:U\to\mathbb R^{m+1}$ and $\rho:U\to\mathbb R$ be $C^2$, with $\|\sigma(u)\|=1$ and $\rho(u)>0$ on $K$. The two maps avoid zero on $K$, their pullbacks of $\omega_{m+1}$ agree on $K$, both flux coefficients are integrable over $K$, and their flux integrals over $K$ agree. No rank condition on $\sigma$ is required.

If additionally $K$ has unique differentiation at each point and the normal-first determinant $\det[\sigma,D_1\sigma,\ldots,D_m\sigma]$ is nonnegative on $K$, then its flux is its geometric parametric area

$$
\int_K\sqrt{\det\bigl(\langle D_i\sigma,D_j\sigma\rangle\bigr)}\,du.
$$

For a $C^2$ map from a neighborhood of a compact set of positive Lebesgue measure, this area is strictly positive if its parameter derivative columns are linearly independent at every point of that set.

This file has **partial source coverage**, not a complete solution. For `R10E23.b`, only the scalar integral facts above are proved; with the prescribed $f_k(x)=(-1)^k g_k(x_k/r_k)$, the identity $\omega_k=d(f_k\omega_{k-1})=df_k\wedge\omega_{k-1}$ on $E_{k-1}$ is not proved. For `R10E23.c`, nonexactness in dimensions at least two is not proved. For `R10E23.d.formulation` and `R10E23.d.generalization`, the results prove radial invariance and the sphere-patch flux/area comparison, but do not construct a whole-sphere chain, prove its face cancellation, or establish the global positive sphere integral required by the selected contract. The zero-degree convention is an explicit addition, not a source-defined negative-degree primitive.

**Proof.** In its own $k$ coordinates, write $\omega_k(x)=\|x\|^{-k}\iota_x\mathrm{vol}$; the ambient form is its pullback by projection to the first $k$ coordinates. Expanding the determinant in its first row proves the coordinate formula and the Euclidean norm formula proves the radius identity.

Alternation removes any multiple of the radial vector added to a tangent argument. Hence, for a positive scale $\rho$,

$$
\mathrm{vol}(\rho\sigma,\rho D_1\sigma+(D_1\rho)\sigma,\ldots)
=\rho^{m+1}\mathrm{vol}(\sigma,D_1\sigma,\ldots).
$$

The denominator scales by the same positive power. This proves radial pullback invariance, including nonconstant scales and rank-deficient maps. Apply it to normalization $x\mapsto x/\|x\|$, which preserves the form away from zero. Its derivative is tangent to the unit sphere: differentiation of the squared norm gives orthogonality to the unit radial vector. Any $k$ such tangent vectors in $\mathbb R^k$ are linearly dependent, since they lie in the proper kernel of a nonzero inner-product functional. Thus every top-degree alternating form vanishes on them. Naturality of exterior differentiation under the smooth normalization map now proves closedness, and pullback by the coordinate projection proves ambient closedness. For $k=1$, the sign function is constant on a neighborhood of each point of $E_1$, which also supplies derivative existence directly.

For $g_k$, the exponent $\alpha=(k-3)/2$ is greater than $-1$, including $\alpha=-1/2$ when $k=2$. Factor $(1-s^2)^\alpha=(1+s)^\alpha(1-s)^\alpha$. The first factor is integrable at $-1$; the second is continuous and bounded on $[-1,t]$. This proves endpoint integrability. The integrand is continuous at every interior $t$, so the fundamental theorem gives $g_k'(t)=(1-t^2)^\alpha$. Continuity of the interval primitive gives the limit of $\int_a^t$ as $a\downarrow-1$. No form-primitive identity follows in the current file.

For the degree-zero convention, evaluate the form at the first positive coordinate unit vector: its value is one. It therefore cannot be the zero form on $E_1$. At top index the radial domain is exactly punctured Euclidean space, so this also proves the stated punctured-line result. No negative-degree form is introduced.

For the area comparison, the square of the normal-first determinant is the Gram determinant of the normal and tangents. A unit normal orthogonal to the tangents makes this determinant equal to the tangent Gram determinant. Outward nonnegative orientation selects its nonnegative square root. Tangency on the compact domain, including boundary points, follows from the unit-norm identity and unique differentiation. This proves the pointwise flux-density identity. The $C^2$ neighborhood extensions give continuous area and flux densities; compactness gives their integrability and hence the integral identities. Linear independence makes the tangent Gram determinant positive, and positive measure then gives strictly positive area.

The file also checks normalization on the standard frame: the coordinate volume and the radial form on an outward orthonormal frame are one. A concrete radial-invariance example uses a constant unit direction and radius $1+\|u\|^2$ on any compact parameter set. These are normalization and rescaling checks, not a replacement for a whole-sphere integral.

**Lean declarations:** `Rudin.Chapter10.Exercise23.omega_source_formula`, `Rudin.Chapter10.Exercise23.radius_source_formula`, `Rudin.Chapter10.Exercise23.omega_closed`, `Rudin.Chapter10.Exercise23.topRadial_closed`, `Rudin.Chapter10.Exercise23.omega_one_apply`, `Rudin.Chapter10.Exercise23.omega_one_locally_constant`, `Rudin.Chapter10.Exercise23.omega_one_closed`, `Rudin.Chapter10.Exercise23.omega_one_not_exact`, `Rudin.Chapter10.Exercise23.g_integrable`, `Rudin.Chapter10.Exercise23.g_hasDerivAt`, `Rudin.Chapter10.Exercise23.g_improper_limit`, `Rudin.Chapter10.Exercise23.exactOn_zero_iff`, `Rudin.Chapter10.Exercise23.exactOn_zero_image`, `Rudin.Chapter10.Exercise23.exactOn_succ_iff`, `Rudin.Chapter10.Exercise23.dimension_one_closed_not_exact`, `Rudin.Chapter10.Exercise23.radialDomain_top`, `Rudin.Chapter10.Exercise23.radial_pullback_at`, `Rudin.Chapter10.Exercise23.normalize_pullback`, `Rudin.Chapter10.Exercise23.top_alternating_tangent_zero`, `Rudin.Chapter10.Exercise23.compact_radial_invariance`, `Rudin.Chapter10.Exercise23.normal_flux_eq_gram_area`, `Rudin.Chapter10.Exercise23.sphere_flux_density`, `Rudin.Chapter10.Exercise23.compact_sphere_flux_area`, `Rudin.Chapter10.Exercise23.parametricArea_pos`, `Rudin.Chapter10.Exercise23.coordinateVolume_standard`, `Rudin.Chapter10.Exercise23.topRadial_standard`, `Rudin.Chapter10.Exercise23.compact_radial_model`.

<a id="r10e28"></a>
### 10.28 — Stokes on a parametrized annulus

**Lean source:** [Exercise28.lean](../../../Math/Rudin/Chapter10/Exercise28.lean).

**Inventory status:** Pending verification.

**Statement.** Let $0<a<b$, let $\Phi(r,\theta)=(r\cos\theta,r\sin\theta)$ on the closed rectangle $[a,b]\times[0,2\pi]$, with parameter order $(r,\theta)$, and put $\omega=x^3\,dy$. Then

$$
\int_\Phi d\omega=\int_{\partial\Phi}\omega=\frac{3\pi}{4}(b^4-a^4).
$$

The four induced parameter edges have integrals $0$, $3\pi b^4/4$, $0$, $-3\pi a^4/4$, respectively. The repeated surface integral with $r$ outermost, every angular slice, and all signed boundary integrals have source Riemann witnesses. The current source completes these results although the inventory declaration lists are still empty.

**Proof.** Differentiation gives $d\omega=3x^2\,dx\wedge dy$. The polar derivative has determinant $r$, so the pulled-back surface coefficient is $3r^3\cos^2\theta$. Also

$$
\Phi^*\omega=r^3\cos^3\theta\sin\theta\,dr+r^4\cos^4\theta\,d\theta.
$$

The standard trigonometric integral formulas give $\int_0^{2\pi}\cos^2\theta\,d\theta=\pi$ and $\int_0^{2\pi}\cos^4\theta\,d\theta=3\pi/4$. Integrating $3\pi r^3$ from $a$ to $b$ gives the surface value. On both radial edges the sine factor is zero, so their individual integrals vanish. Their image paths also coincide with opposite induced signs. On the outer circle the integral is $3\pi b^4/4$; the reversed inner circle gives $-3\pi a^4/4$. Their sum is the same surface value.

Independently of this numerical comparison, the proof applies rectangle Stokes to the actual pullback form. Naturality gives $d(\Phi^*\omega)=\Phi^*(d\omega)$, and Fubini identifies the continuous coefficient's area integral with the repeated integral. Its four induced boundary terms are exactly those just computed. The coefficient is continuous on the compact rectangle, so it is integrable; the same continuous-coefficient bridge gives each source Riemann witness. The algebraic numerical formulas hold for arbitrary real endpoints as oriented interval integrals. The area/Stokes comparison and source witnesses are proved for $a\leq b$, including $a=b$; the exercise theorem specializes to $0<a<b$. Finally $\|\Phi(r,\theta)\|^2=r^2$, which verifies the annular radius bounds on the closed domain.

**Lean declarations:** `Rudin.Chapter10.Exercise28.exterior`, `Rudin.Chapter10.Exercise28.polar_derivative`, `Rudin.Chapter10.Exercise28.pullback_value`, `Rudin.Chapter10.Exercise28.surface_coefficient`, `Rudin.Chapter10.Exercise28.angular_two`, `Rudin.Chapter10.Exercise28.angular_four`, `Rudin.Chapter10.Exercise28.surface_value`, `Rudin.Chapter10.Exercise28.radial_edges`, `Rudin.Chapter10.Exercise28.circular_edges`, `Rudin.Chapter10.Exercise28.boundary_value`, `Rudin.Chapter10.Exercise28.seam_paths`, `Rudin.Chapter10.Exercise28.annular_radius`, `Rudin.Chapter10.Exercise28.coefficient_integrable`, `Rudin.Chapter10.Exercise28.surface_area`, `Rudin.Chapter10.Exercise28.actual_stokes`, `Rudin.Chapter10.Exercise28.surface_source`, `Rudin.Chapter10.Exercise28.boundary_source`, `Rudin.Chapter10.Exercise28.exercise28`.

<a id="r10e29"></a>
### 10.29 — A smooth section and a varying-endpoint primitive

**Lean source:** [Exercise29.lean](../../../Math/Rudin/Chapter10/Exercise29.lean).

**Inventory status:** Pending verification.

**Statement.** Let $X$ be a finite-dimensional real normed space and $V\subset X\times\mathbb R$ be open and convex. Its projection $U$ onto $X$ is open, and there is a $C^1$ function $\alpha:U\to\mathbb R$ with $(x,\alpha(x))\in V$. For $\varphi\in C^1(V)$,

$$
F(x,z)=\int_{\alpha(x)}^z\varphi(x,t)\,dt
$$

is $C^1$ on $V$, and each oriented fiber integral exists. The section is constructed, not assumed.

For the setting of Theorem 10.38, let $E\subset (X\times\mathbb R)\times Y$ be open and convex, where $Y$ is a real normed space, and let $f\in C^1(E)$ factor as $f((x,z),y)=\varphi(x,z)$. The constructed section on the projection of $E$ gives a $C^1$ primitive $F((x,z),y)$ on $E$ with all unused coordinates retained. For $p=1$, nonempty $E\subset\mathbb R\times Y$ supplies a fixed endpoint $c$ in its projection and the primitive $\int_c^x\varphi(t)\,dt$. On an empty domain regularity is vacuous; no endpoint in an empty projection is asserted. These completed results are not yet mapped in the inventory.

**Proof.** Each fiber of $V$ is a nonempty convex interval over its projection. For every $x\in U$, choose one fiber value $c_x$. Openness makes the same constant $c_x$ valid for all base points in a neighborhood of $x$. The smooth partition-of-unity selection theorem combines these locally constant choices into a locally finite smooth weighted sum. The weights sum to one, so convexity of each fiber keeps that sum in the fiber. This produces the $C^1$ section, also when $U$ is empty; an extension outside $U$ is used only to give a total function, without asserting smoothness outside $U$.

Convexity keeps the entire interval between $\alpha(x)$ and $z$ in the fiber, regardless of endpoint order. Use the affine substitution

$$
F(x,z)=\int_0^1(z-\alpha(x))\,\varphi\bigl(x,\alpha(x)+(z-\alpha(x))s\bigr)\,ds.
$$

It remains valid for equal or reversed endpoints. The integrand is $C^1$ near every point over the compact interval $0\leq s\leq1$. To justify differentiation under the integral, take a compact closed ball inside the open base domain. Continuity of the parameter derivative on its product with $[0,1]$ supplies a uniform bound. Dominated differentiation gives the derivative as the integral of that parameter derivative, and dominated continuity makes the derivative continuous. Thus the fixed-interval integral, and hence $F$, is $C^1$. The bound is derived locally, not an added global hypothesis. Continuity on each compact fiber interval gives integrability and Darboux Riemann witnesses. If the displayed bounds are $a>b$, the source witness on $[b,a]$ has value $-\int_a^b\varphi(x,t)\,dt$.

In the factorized setting, $\varphi$ is itself $C^1$ on the projection: near a projected point fix one admissible unused coordinate $y_0$ and use the local lift $z\mapsto(z,y_0)$ into $E$. The factorization identifies $\varphi$ locally with the $C^1$ function $f(z,y_0)$. Apply the preceding section and varying-integral results on the open convex projection, and compose with projection from $E$.

For $p=1$ and nonempty $E$, choose any point of $E$ and its first coordinate $c$. Convexity contains every integration interval in the projection. The fundamental theorem gives derivative $\varphi$ for $x\mapsto\int_c^x\varphi$, and continuity gives $C^1$ regularity. Compose with the first projection to retain unused coordinates. On the empty domain both the zero function and every fixed-endpoint displayed primitive are $C^1$ there, without a nonexistent choice from its projection.

**Lean declarations:** `Rudin.Chapter10.Exercise29.projection_open`, `Rudin.Chapter10.Exercise29.fiber_convex`, `Rudin.Chapter10.Exercise29.section_exists`, `Rudin.Chapter10.Exercise29.integral_c1_data`, `Rudin.Chapter10.Exercise29.integral_c1`, `Rudin.Chapter10.Exercise29.integral_hasFDerivAt`, `Rudin.Chapter10.Exercise29.fiber_interval`, `Rudin.Chapter10.Exercise29.integral_affine`, `Rudin.Chapter10.Exercise29.varying_integral_c1`, `Rudin.Chapter10.Exercise29.fiber_integrable`, `Rudin.Chapter10.Exercise29.fiber_source`, `Rudin.Chapter10.Exercise29.factor_c1`, `Rudin.Chapter10.Exercise29.exercise29`, `Rudin.Chapter10.Exercise29.fixed_lower_c1`, `Rudin.Chapter10.Exercise29.exercise29_p_one`, `Rudin.Chapter10.Exercise29.exercise29_empty`.

<a id="r10e30"></a>
### 10.30 — The Euclidean surface normal

**Lean source:** [Exercise30.lean](../../../Math/Rudin/Chapter10/Exercise30.lean).

**Inventory status:** Verified as stated.

**Statement.** For arbitrary $\alpha,\beta\in\mathbb R^3$, let

$$
N=(\alpha_2\beta_3-\alpha_3\beta_2,\ \alpha_3\beta_1-\alpha_1\beta_3,\ \alpha_1\beta_2-\alpha_2\beta_1),\qquad T(u,v)=u\alpha+v\beta.
$$

Then $\det[\alpha\ \beta\ N]=\|N\|^2$, and $N\cdot T(e_1)=N\cdot T(e_2)=0$. The statements use the Euclidean inner product and norm and require no independence or nondegeneracy assumption.

**Proof.** The coordinate vector $N$ is $\alpha\times\beta$. The scalar triple-product identity gives

$$
\det[\alpha\ \beta\ N]=(\alpha\times\beta)\cdot N=N\cdot N=\|N\|^2.
$$

The cross product is perpendicular to each factor, so $N\cdot\alpha=N\cdot\beta=0$. The linear map $T$ sends the two parameter basis vectors to $\alpha$ and $\beta$, proving the stated orthogonality. These identities remain valid when the two factors are dependent, including zero vectors: the cross product then vanishes.

**Lean declarations:** `Rudin.Chapter10.exercise30_normal_coordinates`, `Rudin.Chapter10.exercise30_determinant`, `Rudin.Chapter10.exercise30_basis`, `Rudin.Chapter10.exercise30_normal_perpendicular`, `Rudin.Chapter10.exercise30_orthogonality`.

<a id="r10e32"></a>
### 10.32 — The Möbius band and its two boundary notions

**Lean source:** [Exercise32.lean](../../../Math/Rudin/Chapter10/Exercise32.lean).

**Inventory status:** Pending verification.

**Statement.** Let $0<\delta<1$, $D=[0,\pi]\times[-\delta,\delta]$, and

$$
\Phi(\theta,t)=\bigl((1-t\sin\theta)\cos2\theta,\ (1-t\sin\theta)\sin2\theta,\ t\cos\theta\bigr).
$$

Its image is a regular Möbius band avoiding the $z$-axis. The only identifications are equal parameters and the reversed seam $\Phi(\pi,t)=\Phi(0,-t)$. It admits no continuous nowhere-zero normal field orthogonal to its actual parameter tangents.

Let $p_1=(0,-\delta)$, $p_2=(\pi,-\delta)$, $p_3=(\pi,\delta)$, $p_4=(0,\delta)$, $p_5=p_1$, and let $\Gamma_i$ be the full map $\Phi\circ[p_i,p_{i+1}]$, with its oriented affine unit-interval parametrization. Put $a=(1,0,-\delta)$ and $b=(1,0,\delta)$. Then $\Phi(p_1)=\Phi(p_3)=a$, $\Phi(p_2)=\Phi(p_4)=b$, and both $\Gamma_1,\Gamma_3$ run from $a$ to $b$. Their planar projections are loops with indices $+1,-1$, respectively. Both seam maps equal $[b,a]$, and the actual parameter boundary is

$$
\partial\Phi=\Gamma_1+\Gamma_2+\Gamma_3+\Gamma_4=\Gamma_1+\Gamma_3+2\Gamma_2.
$$

The single free rim instead has oriented chain $\Gamma=\Gamma_1-\Gamma_3$ and closed parametrization

$$
G(\theta)=\bigl((1+\delta\sin\theta)\cos2\theta,\ (1+\delta\sin\theta)\sin2\theta,\ -\delta\cos\theta\bigr),\qquad0\leq\theta\leq2\pi.
$$

For $\eta=(x\,dy-y\,dx)/(x^2+y^2)$, defined off the $z$-axis,

$$
\int_{\partial\Phi}\eta=0,\qquad\int_\Gamma\eta=\int_G\eta=4\pi.
$$

All four edge integrals and the displayed closed rim integral have source Riemann witnesses. Thus the free rim chain is not the parameter boundary chain.

**Proof.** Since $|t\sin\theta|\leq\delta<1$, the planar radius $1-t\sin\theta$ is positive on all of $D$, including its seam and rim. In particular the image avoids the $z$-axis. If two image points agree, their positive planar radii agree, and their planar angles $2\theta,2\psi$ have the same sine and cosine. For $\theta,\psi\in[0,\pi]$, this means either $\theta=\psi$ or the two opposite interval endpoints. In the first case equality of radius and height, together with $\sin^2\theta+\cos^2\theta=1$, gives equal transverse parameters. At the two endpoints it gives the reversed transverse parameter. Direct substitution proves the seam formula.

Differentiating $\Phi$ gives independent tangents everywhere on $D$. Indeed, in a relation $A\Phi_\theta+B\Phi_t=0$, the planar angular component is $2A(1-t\sin\theta)$, so $A=0$ by radius positivity. The transverse tangent has nonzero length, so $B=0$. This includes all boundary points.

To prove nonorientability, restrict a proposed continuous normal field to the core $c(\theta)=(\cos2\theta,\sin2\theta,0)$. Its two tangents are $(-2\sin2\theta,2\cos2\theta,0)$ and $(-\sin\theta\cos2\theta,-\sin\theta\sin2\theta,\cos\theta)$. Every vector perpendicular to both is a scalar multiple of the unit vector

$$
n(\theta)=(\cos\theta\cos2\theta,\cos\theta\sin2\theta,\sin\theta).
$$

The scalar is the dot product with $n(\theta)$ and is continuous and nonzero. But $c(0)=c(\pi)$ while $n(\pi)=-n(0)$, so its endpoint values are opposites. The intermediate value theorem forces a zero, a contradiction. This proves the stated normal-field formulation of nonorientability, not just a sign mismatch in a drawing.

Substitute the four corners to obtain their images. Rescale $D$ positively to the unit square by $(s,u)\mapsto(\pi s,\delta(2u-1))$. Its four signed full-map restrictions give the asserted boundary decomposition; the same boundary is obtained by triangulating the square into smooth simplexes. Substitution on the vertical edges shows that both are literally the same segment from $b$ to $a$. They therefore add with multiplicity two, rather than cancel. Endpoint substitution gives both rim arcs from $a$ to $b$.

The first half of $G$ is $\Gamma_1$ after positive linear rescaling, and the second half is the reverse of $\Gamma_3$. Splitting $[0,2\pi]$ at $\pi$ proves that its image is exactly the union of the two free-edge images, with no seam added. That union lies in the band, and $G(0)=G(2\pi)$.

The form $\eta$ is the pullback of the closed angular form of Exercise 21 by planar projection. It is $C^1$ off the axis and closed there. Apply analytic Stokes to the rescaled square, using its two smooth triangle maps and the axis-avoidance result, to obtain zero on its actual parameter boundary.

For direct values, a positive-radius planar curve of angular speed $k$ has angular coefficient $k$: the derivative of its radius contributes a radial vector, whose alternating numerator is zero. The first arc on the unit interval has coefficient $2\pi$, the third has coefficient $-2\pi$, and both seam coefficients are zero. Their source Riemann integrals are therefore $2\pi,0,-2\pi,0$. Exercise 21 identifies the two projected-loop indices as $+1$ and $-1$. The closed parametrization $G$ has coefficient $2$ throughout $[0,2\pi]$, giving $4\pi$ and its Riemann witness. Equivalently, the chain $\Gamma_1-\Gamma_3$ has integral $2\pi-(-2\pi)=4\pi$. Since integration is an additive function on these signed full-map chains, this nonzero value distinguishes it from the parameter boundary. There is no conflict with Stokes: the band is nonorientable, and its geometric free rim is not the signed boundary of this rectangular parametrization.

**Lean declarations:** `Rudin.Chapter10.Exercise32.seam`, `Rudin.Chapter10.Exercise32.injective_modulo_seam`, `Rudin.Chapter10.Exercise32.theta_derivative`, `Rudin.Chapter10.Exercise32.transverse_derivative`, `Rudin.Chapter10.Exercise32.tangent_independence`, `Rudin.Chapter10.Exercise32.avoids_axis`, `Rudin.Chapter10.Exercise32.nonorientable`, `Rudin.Chapter10.Exercise32.core_normal_multiple`, `Rudin.Chapter10.Exercise32.boundary_decomposition`, `Rudin.Chapter10.Exercise32.triangulated_boundary`, `Rudin.Chapter10.Exercise32.corner_images`, `Rudin.Chapter10.Exercise32.edge_endpoints`, `Rudin.Chapter10.Exercise32.first_edge_winding`, `Rudin.Chapter10.Exercise32.edge1_projection`, `Rudin.Chapter10.Exercise32.third_edge_winding`, `Rudin.Chapter10.Exercise32.edge3_full`, `Rudin.Chapter10.Exercise32.repeated_seam_maps`, `Rudin.Chapter10.Exercise32.boundary_repeated_seam`, `Rudin.Chapter10.Exercise32.geometricEdge_closed`, `Rudin.Chapter10.Exercise32.geometricEdge_first_half`, `Rudin.Chapter10.Exercise32.geometricEdge_second_half`, `Rudin.Chapter10.Exercise32.geometric_edge_range`, `Rudin.Chapter10.Exercise32.rim_subset_band`, `Rudin.Chapter10.Exercise32.parametrized_boundary_integral`, `Rudin.Chapter10.Exercise32.boundary_source_integrals`, `Rudin.Chapter10.Exercise32.edge1_integral`, `Rudin.Chapter10.Exercise32.edge3_integral`, `Rudin.Chapter10.Exercise32.geometric_edge_integral`, `Rudin.Chapter10.Exercise32.geometric_edge_chain_integral`, `Rudin.Chapter10.Exercise32.geometric_edge_source_integral`, `Rudin.Chapter10.Exercise32.geometric_edge_ne_parameter_boundary`.
